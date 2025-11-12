/* eslint-disable no-console */
/**
 * IBKR Advanced Options Flow Server (Equities + Futures)
 * - Auto-picks ~15DTE expiry and ~25 ATM contracts (C+P interleaved)
 * - Captures UL & OPT price at "trade time"
 * - Streams live quotes (incl. delta) for options and underlying
 * - Classifies BTO/STO/BTC/STC (UW-style; OPEN if size > (OI+Vol))
 * - Tracks 12 days of OI/Vol history
 * - Emits TRADE + PRINT events; PRINT includes volume/OI ratio
 *
 * Run:
 *   IBKR_HOST=https://127.0.0.1:5000 PORT=3000 NODE_TLS_REJECT_UNAUTHORIZED=0 node index.js
 */

const http = require('http');
const express = require('express');
const cors = require('cors');
const compression = require('compression');
const morgan = require('morgan');
const axios = require('axios');
const { wrapper } = require('axios-cookiejar-support');
const tough = require('tough-cookie');
const WebSocket = require('ws');

const PORT = parseInt(process.env.PORT || '3000', 10);
const IBKR_HOST = process.env.IBKR_HOST || 'https://127.0.0.1:5000';

const jar = new tough.CookieJar();
const ax = wrapper(axios.create({
  baseURL: `${IBKR_HOST}/v1/api`,
  jar,
  withCredentials: true,
  timeout: 15000
}));

/* --------------------------- App / WS ---------------------------------- */
const app = express();
app.use(compression());
app.use(cors());
app.use(morgan('tiny'));
const server = http.createServer(app);

const wss = new WebSocket.Server({ noServer: true });
server.on('upgrade', (req, socket, head) => {
  if (req.url === '/ws') {
    wss.handleUpgrade(req, socket, head, (ws) => wss.emit('connection', ws, req));
  } else {
    socket.destroy();
  }
});
const clients = new Set();

/* --------------------------- Config ------------------------------------ */
const THRESHOLDS = {
  sweep:         { minPremium:  50000, minContracts: 100 },
  block:         { minPremium: 100000, minContracts:  50 },
  notable:       { minPremium:  25000, minContracts:  25 },
  futuresSweep:  { minPremium: 100000, minContracts:  50 },
  futuresBlock:  { minPremium: 200000, minContracts:  25 },
  futuresNotable:{ minPremium:  50000, minContracts:  10 }
};

const FUTURES_SYMBOLS = {
  '/ES': { name:'E-mini S&P 500', exchange:'GLOBEX', multiplier:50 },
  '/NQ': { name:'E-mini NASDAQ-100', exchange:'GLOBEX', multiplier:20 },
  '/YM': { name:'E-mini Dow', exchange:'ECBOT', multiplier:5 },
  '/RTY':{ name:'E-mini Russell 2000', exchange:'GLOBEX', multiplier:50 },
  '/CL': { name:'Crude Oil', exchange:'NYMEX', multiplier:1000 },
  '/GC': { name:'Gold', exchange:'COMEX', multiplier:100 }
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA','NVDA','AMZN','MSFT','META','GOOGL'];

/* --------------------------- State ------------------------------------- */
const historicalData = new Map();   // conid -> [{date, oi, volume, ts}]
const liveQuotes     = new Map();   // conid -> last quote cache
const optionToUL     = new Map();   // optionConid -> underlyingConid
const ulForOption    = new Map();   // option conid -> { isFuture, mult, symbol, right, strike, expiry, oi? }

/* --------------------------- Utils ------------------------------------- */
const sleep  = (ms)=>new Promise(r=>setTimeout(r,ms));
const nowISO = ()=>new Date().toISOString();
const todayKey = ()=>new Date().toISOString().split('T')[0];

function px(v){
  if (v == null) return 0;
  const n = parseFloat(String(v).replace(/[^\d\.\-\+]/g, ''));
  return isFinite(n) ? n : 0;
}
function num(x){ const n = +x; return Number.isFinite(n) ? n : 0; }

function isFuturesMarketOpen() {
  const now = new Date();
  const d = now.getUTCDay(), h = now.getUTCHours();
  if (d === 6) return false;
  if (d === 0 && h < 23) return false;
  if (d === 5 && h >= 22) return false;
  return true;
}
function isEquityMarketOpen() {
  const d = new Date().getUTCDay();
  return d >= 1 && d <= 5;
}
function parseYYYYMMDD(s){
  if (!s) return null;
  if (/^\d{8}$/.test(s)) {
    const y=+s.slice(0,4), m=+s.slice(4,6)-1, d=+s.slice(6,8);
    return new Date(Date.UTC(y,m,d));
  }
  if (/^\d{4}-\d{2}-\d{2}$/.test(s)) return new Date(s+'T00:00:00Z');
  return null;
}
function dte(dateUtc){
  if (!dateUtc) return Infinity;
  return Math.ceil((dateUtc - new Date()) / 86400000);
}

/* ------------------------ History (12 days) ---------------------------- */
function storeHistoricalData(conid, oi, volume){
  const ts = Date.now();
  const arr = historicalData.get(conid) || [];
  arr.push({ date: todayKey(), oi:+oi||0, volume:+volume||0, ts });
  const cutoff = ts - 12*24*60*60*1000;
  historicalData.set(conid, arr.filter(x=>x.ts >= cutoff));
}
function getHistoricalAverages(conid){
  const arr = historicalData.get(conid) || [];
  if (!arr.length) return { avgOI:0, avgVolume:0, dataPoints:0 };
  const totOI = arr.reduce((s,x)=>s+(x.oi||0),0);
  const totV  = arr.reduce((s,x)=>s+(x.volume||0),0);
  return { avgOI: totOI/arr.length, avgVolume: totV/arr.length, dataPoints: arr.length };
}

/* --------------------------- IB helpers -------------------------------- */
async function primeIB() {
  try { await ax.get('/sso/validate'); } catch {}
  for (let i = 0; i < 20; i++) {
    try {
      const { data } = await ax.get('/iserver/auth/status');
      if (data?.authenticated && data?.connected) {
        console.log('\n\n[IB] authenticated & connected\n');
        return;
      }
      console.log('[IB] status:', data);
    } catch (e) {
      console.log('[IB] status error:', e.message);
    }
    await sleep(1000);
  }
  throw new Error('IB not authenticated/connected');
}

// Not all CP builds have this route; failure is OK.
async function setMarketDataLive() {
  try {
    await ax.post('/iserver/marketdata/type', { marketDataType: 1 });
    console.log('[IB] market data type set to LIVE');
  } catch (e) {
    console.error('[IB] could not set market data type:', e.response?.status, e.response?.data || e.message);
  }
}

async function ibGet(path, params){ const { data } = await ax.get(path, { params }); return data; }
async function secdefSearch(symbol, secType){ return ibGet('/iserver/secdef/search', { symbol, secType }); }
async function findStockConid(symbol){ const data = await secdefSearch(symbol,'STK'); return data?.[0]?.conid; }
async function mdSnapshot(conids){
  // 31=last, 84=bid, 85=bidSize, 86=ask, 88=lastSize, 7762=day volume,
  // 7308..7311 greeks, 7283=IV
  const FIELDS = '31,84,85,86,88,7762,7308,7309,7310,7311,7283';
  return ibGet('/iserver/marketdata/snapshot', { conids: conids.join(','), fields: FIELDS, since: 0 });
}

/* ------------------------ Greeks / Classifiers ------------------------- */
function calcGreeks(row){
  return {
    delta: +row['7308']||0,
    gamma: +row['7309']||0,
    theta: +row['7310']||0,
    vega:  +row['7311']||0,
    iv:    +row['7283']||0
  };
}
function classifySizeTags(trade, isFuture){
  const t = isFuture
    ? { sweep: THRESHOLDS.futuresSweep, block: THRESHOLDS.futuresBlock, notable: THRESHOLDS.futuresNotable }
    : { sweep: THRESHOLDS.sweep,        block: THRESHOLDS.block,        notable: THRESHOLDS.notable };
  const out = [];
  if (trade.premium >= t.sweep.minPremium && trade.size >= t.sweep.minContracts && trade.aggressor) out.push('SWEEP');
  if (trade.premium >= t.block.minPremium && trade.size >= t.block.minContracts) out.push('BLOCK');
  if (trade.premium >= t.notable.minPremium && trade.size >= t.notable.minContracts) out.push('NOTABLE');
  return out.length ? out : ['REGULAR'];
}
function classifyTradeUWStyle(trade, oi, vol, hist){
  const isAggBuy = !!trade.aggressor;
  if (trade.size > (oi + vol)) return isAggBuy ? 'BTO' : 'STO';

  const volRatio = hist.avgVolume > 0 ? (vol / hist.avgVolume) : 1;
  const oiChange = oi - (hist.avgOI || 0);
  const spike = volRatio >= 2;

  if (spike && oiChange > 0) return isAggBuy ? 'BTO' : 'STO';
  if (spike && oiChange <= 0) return isAggBuy ? 'BTC' : 'STC';

  if (oi > 0 && trade.size/oi > 0.4) return isAggBuy ? 'BTO' : 'STO';
  return isAggBuy ? 'BTC' : 'STC';
}
function confidenceScore(trade, oi, vol, hist){
  let c = 50;
  const vr = hist.avgVolume>0 ? (vol/hist.avgVolume) : 1;
  if (vr>3) c+=20; else if (vr>2) c+=10;
  if (oi>0){
    const r = trade.size/oi;
    if (r>0.5) c+=20; else if (r>0.25) c+=10;
  }
  if (trade.premium>100000) c+=10;
  if (hist.dataPoints>=5) c+=10;
  return Math.min(100,c);
}

/* --------------------------- Broadcast --------------------------------- */
function broadcastAll(o){ const s = JSON.stringify(o); for (const ws of clients) if (ws.readyState===WebSocket.OPEN) ws.send(s); }

function broadcastLiveOption(conid, row){
  const msg = {
    type:'LIVE_QUOTE', conid,
    last:px(row['31']),
    bid:px(row['84']),
    ask:px(row['86']),
    volume:num(row['7762']),   // day volume if present
    delta:num(row['7308']),
    timestamp: Date.now()
  };
  liveQuotes.set(conid, msg);
  broadcastAll(msg);
}
function broadcastLiveUL(conid, row){
  const msg = {
    type:'UL_LIVE_QUOTE', conid,
    last:px(row['31']),
    bid:px(row['84']),
    ask:px(row['86']),
    volume:num(row['7762']),   // use day volume when available
    timestamp: Date.now()
  };
  broadcastAll(msg);
}

/* --------------------- ATM / ~15DTE picking --------------------------- */
function chooseExpiryNear15DTE(list, { target=15, window=10 }){
  const byExp = new Map();
  for (const x of list) {
    const exp = x.maturityDate || x.lastTradingDay || x.expiry;
    if (!exp) continue;
    if (!byExp.has(exp)) byExp.set(exp, []);
    byExp.get(exp).push(x);
  }
  let bestExp = null, bestDelta = Infinity;
  for (const [exp] of byExp) {
    const d = dte(parseYYYYMMDD(exp));
    const delta = Math.abs(d - target);
    if (delta <= window && delta < bestDelta) { bestDelta = delta; bestExp = exp; }
  }
  if (!bestExp) {
    for (const [exp] of byExp) {
      const d = dte(parseYYYYMMDD(exp));
      const delta = Math.abs(d - target);
      if (delta < bestDelta) { bestDelta = delta; bestExp = exp; }
    }
  }
  return bestExp ? byExp.get(bestExp) : [];
}

function pickContractsAroundATM({ contracts, underlyingPx, targetCount=25 }){
  const calls=[], puts=[];
  for (const c of contracts) {
    const isCall = c.right === 'C' || /C\b/.test(c.right||'') || /C\b/.test(c.localSymbol||'') || /C\b/.test(c.description||'');
    const strike = +c.strike || 0;
    const rec = { ...c, isCall, strike, dist: Math.abs(strike - underlyingPx) };
    (isCall ? calls : puts).push(rec);
  }
  calls.sort((a,b)=>a.dist-b.dist);
  puts.sort((a,b)=>a.dist-b.dist);
  const out=[]; let i=0;
  while (out.length < targetCount && (i < calls.length || i < puts.length)) {
    if (i < calls.length) out.push(calls[i]);
    if (out.length >= targetCount) break;
    if (i < puts.length) out.push(puts[i]);
    i++;
  }
  return out;
}

/* ------------------------ PRINTS emitter ------------------------------- */
function maybeEmitPrint(optionMeta, row, isFuture, multiplier){
  const conid = optionMeta.conid;
  const last  = px(row['31']);
  const lastSize = num(row['88']);     // trade size
  const dayVol   = num(row['7762']);   // cumulative day volume
  const oi       = optionMeta.oi ?? null;

  if (!last || !lastSize) return;

  const bid = px(row['84']), ask = px(row['86']);
  const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
  const volOiRatio = (oi && dayVol) ? (dayVol / oi) : null;
  const premium = lastSize * last * multiplier;

  broadcastAll({
    type:'PRINT',
    conid,
    symbol: optionMeta.symbol,
    right: optionMeta.right === 'C' ? 'CALL' : 'PUT',
    strike: optionMeta.strike,
    expiry: optionMeta.expiry,
    tradePrice: last,
    tradeSize: lastSize,
    bid, ask,
    aggressor,
    premium,
    volOiRatio,
    timestamp: Date.now()
  });
}

/* --------------------- Futures helpers (months) ------------------------ */
function pickMonthFromTrsrv(root, data){
  const arr = data?.[root] || [];
  if (!Array.isArray(arr) || !arr.length) return null;
  let best=null, bestScore=1e9;
  const now = new Date();
  for (const c of arr) {
    const y=Math.floor(c.expirationDate/10000);
    const m=Math.floor((c.expirationDate%10000)/100)-1;
    const d=c.expirationDate%100;
    const exp = new Date(Date.UTC(y,m,d));
    const score = Math.abs(Math.ceil((exp - now)/86400000) - 15);
    if (score < bestScore) { bestScore=score; best=c; }
  }
  return best ? String(best.expirationDate).slice(0,6) : null; // YYYYMM
}

/* ------------------------- Builders ----------------------------------- */
async function getFrontFuture(symbol){
  const clean = symbol.replace('/','');
  const list = await secdefSearch(clean,'FUT');
  return list?.[0];
}

async function buildFuturesOptionSelection(symbol, underlyingPx){
  const meta = FUTURES_SYMBOLS[symbol];
  const fut  = await getFrontFuture(symbol);
  if (!fut) return { ulConid:null, options:[] };

  // get a concrete month from /trsrv/futures
  let month;
  try {
    const root = symbol.replace('/','').toUpperCase();
    const monthsData = await ibGet('/trsrv/futures', { symbols: root });
    month = pickMonthFromTrsrv(root, monthsData);
  } catch { month = null; }
  if (!month) {
    const dt = new Date(); const y=dt.getUTCFullYear(); const m=String(dt.getUTCMonth()+2).padStart(2,'0');
    month = `${y}${m}`;
  }

  let info = [];
  try {
    // try with exchange first; retry without; then advance a month once if still empty
    info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype:'FOP', month, exchange: meta.exchange });
    if (!Array.isArray(info) || info.length === 0) {
      info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype:'FOP', month });
    }
    if (!Array.isArray(info) || info.length === 0) {
      const y = +month.slice(0,4), m = +month.slice(4,6);
      const dt = new Date(Date.UTC(y, m-1, 1)); dt.setUTCMonth(dt.getUTCMonth()+1);
      const ny = dt.getUTCFullYear(), nm = String(dt.getUTCMonth()+1).padStart(2,'0');
      const month2 = `${ny}${nm}`;
      info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype:'FOP', month: month2 });
    }
  } catch (e) {
    console.error('[FOP INFO]', symbol, e.response?.status, e.response?.data || e.message);
  }

  const raw = Array.isArray(info) ? info : [];
  const norm = raw.map(x => ({
    conid: x.conid,
    right: x.right === 'C' ? 'C' : 'P',
    strike: +x.strike || 0,
    expiry: x.lastTradingDay || x.maturityDate || '',
    exchange: meta.exchange,
    symbol
  }));

  const coarse = norm.filter(c => c.strike > 0);
  const near   = coarse.filter(c => Math.abs((c.strike - underlyingPx)/Math.max(1,underlyingPx)) < 0.20);
  const base   = near.length >= 12 ? near : coarse;
  const picked = pickContractsAroundATM({ contracts: base, underlyingPx, targetCount:25 });  

  return { ulConid: fut.conid, options: picked };
}

async function buildEquityOptionSelection(symbol, underlyingPx){
  const stkConid = await findStockConid(symbol);
  if (!stkConid) return { ulConid:null, options:[] };

  const raw = await secdefSearch(symbol, 'OPT');
  const norm = (Array.isArray(raw) ? raw : []).map(x => ({
    conid: x.conid,
    right: /C\b/.test(x.description||x.localSymbol||'') ? 'C' : 'P',
    strike: +x.strike || 0,
    expiry: x.maturityDate || '',
    exchange: x.exchange || 'SMART',
    symbol
  }));
  const forExpiry = chooseExpiryNear15DTE(norm, { target:15, window:10 });
  const picked = pickContractsAroundATM({ contracts: (forExpiry.length?forExpiry:norm), underlyingPx, targetCount:25 });
  return { ulConid: stkConid, options: picked };
}

/* -------------------------- Core process ------------------------------- */
async function captureUnderlying(ulConid){
  const snap = await mdSnapshot([ulConid]);
  const row  = snap?.[0] || {};
  const ulPx = px(row['31']);
  broadcastLiveUL(ulConid, row);
  return { price: ulPx, row };
}

function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){  
  const last      = px(optRow['31']);
  const lastSize  = num(optRow['88']);    // per-trade size
  const dayVol    = num(optRow['7762']);  // cumulative day volume
  const oi        = optionMeta.oi ?? null;

  const bid  = px(optRow['84']);
  const ask  = px(optRow['86']);
  const greeks = calcGreeks(optRow);

  if (oi != null) storeHistoricalData(optionMeta.conid, oi, dayVol);
  const hist = getHistoricalAverages(optionMeta.conid);

  const size = lastSize;
  const premium = last * size * multiplier;
  const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
  const volOiRatio = (oi && dayVol) ? (dayVol/oi) : null;

  const trade = {
    symbol: optionMeta.symbol,
    assetClass: isFuture ? 'FUTURES_OPTION' : 'EQUITY_OPTION',
    conid: optionMeta.conid,
    type: optionMeta.right === 'C' ? 'CALL' : 'PUT',
    strike: optionMeta.strike,
    expiry: optionMeta.expiry,
    optionPrice: last,
    bid, ask,
    size,
    openInterest: oi,
    premium,
    aggressor,
    underlyingConid: ulConid,
    underlyingPrice: ul.price,
    multiplier,
    exchange: optionMeta.exchange || (isFuture ? 'GLOBEX' : 'SMART'),
    timestamp: nowISO(),
    greeks,
    volOiRatio
  };

  const direction  = classifyTradeUWStyle(trade, oi ?? 0, dayVol ?? 0, hist);
  const confidence = confidenceScore(trade, oi ?? 0, dayVol ?? 0, hist);
  const tags       = classifySizeTags(trade, isFuture);

  return {
    payload: {
      type:'TRADE',
      ...trade,
      direction, confidence,
      classifications: tags,
      historicalComparison: {
        avgOI: Math.round(hist.avgOI),
        avgVolume: Math.round(hist.avgVolume),
        oiChange: oi != null ? Math.round(oi - (hist.avgOI||0)) : 0,
        volumeMultiple: hist.avgVolume>0 && dayVol ? +(dayVol/hist.avgVolume).toFixed(2) : null,
        dataPoints: hist.dataPoints
      },
      marketSession: isFuture ? (isFuturesMarketOpen() ? 'OPEN' : 'CLOSED')
                              : (isEquityMarketOpen() ? 'REGULAR/EXTENDED' : 'CLOSED')
    },
    optRow
  };
}

async function processOptionConid(optionMeta, isFuture, ulConid, multiplier){
  const [optSnap, ul] = await Promise.all([ mdSnapshot([optionMeta.conid]), captureUnderlying(ulConid) ]);
  const optRow = optSnap?.[0];
  if (!optRow) return;

  optionToUL.set(optionMeta.conid, ulConid);
  ulForOption.set(optionMeta.conid, {
    isFuture, mult: multiplier, symbol: optionMeta.symbol,
    right: optionMeta.right, strike: optionMeta.strike, expiry: optionMeta.expiry,
    oi: optionMeta.oi ?? null
  });

  const { payload, optRow: rowForPrint } = buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier });
  if (payload.premium >= 1000) broadcastAll(payload); // micro-print guard
  maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);
  broadcastLiveOption(optionMeta.conid, optRow);
}

/* -------------------------- Loops ------------------------------------- */
async function loopFuturesSymbol(symbol){
  try{
    const fut = await getFrontFuture(symbol);
    if (!fut) return;

    const ulSnap = await mdSnapshot([fut.conid]);
    const ulRow  = ulSnap?.[0] || {};
    const ulPx   = px(ulRow['31']);
    broadcastLiveUL(fut.conid, ulRow);

    if (!ulPx || ulPx < 0) return; // permissions/delayed → skip pass

    const { ulConid, options } = await buildFuturesOptionSelection(symbol, ulPx);
    for (const meta of options) {
      await processOptionConid(meta, true, ulConid, FUTURES_SYMBOLS[symbol].multiplier);
      await sleep(120);
    }
  } catch(e) {
    console.error('[FUT LOOP]', symbol, e.response?.data || e.message);
  }
}

async function loopEquitySymbol(symbol){
  try{
    const stkConid = await findStockConid(symbol);
    if (!stkConid) return;

    const ulSnap = await mdSnapshot([stkConid]);
    const ulRow  = ulSnap?.[0] || {};
    const ulPx   = px(ulRow['31']);
    broadcastLiveUL(stkConid, ulRow);

    if (!ulPx || ulPx < 0) return;

    const { ulConid, options } = await buildEquityOptionSelection(symbol, ulPx);
    for (const meta of options) {
      await processOptionConid(meta, false, ulConid, 100);
      await sleep(90);
    }
  } catch(e) {
    console.error('[EQ LOOP]', symbol, e.response?.data || e.message);
  }
}

async function pollLiveQuotes(){
  try{
    const optionConids = Array.from(optionToUL.keys());
    if (!optionConids.length) return;

    const snaps = await mdSnapshot(optionConids);
    for (let i=0;i<snaps.length;i++){
      const row = snaps[i] || {};
      const conid = row.conid || optionConids[i];
      broadcastLiveOption(conid, row);

      const meta = ulForOption.get(conid);
      if (meta) {
        const optionMeta = { conid, symbol: meta.symbol, right: meta.right, strike: meta.strike, expiry: meta.expiry, oi: meta.oi ?? null };
        maybeEmitPrint(optionMeta, row, meta.isFuture, meta.mult);
      }
      const ulConid = optionToUL.get(conid);
      if (ulConid) {
        const ulSnap = await mdSnapshot([ulConid]);
        broadcastLiveUL(ulConid, ulSnap?.[0] || {});
      }
      await sleep(25);
    }
  } catch(e) {}
}

/* ------------------------- WS + UI ------------------------------------ */
const DEFAULT_SUBS = { futures:['/ES','/NQ'], equities:['SPY','QQQ'] };

wss.on('connection', (ws)=>{
  clients.add(ws);
  ws._subs = { ...DEFAULT_SUBS };
  ws.send(JSON.stringify({
    type:'connected',
    message:'Connected to IBKR Flow (auto 25 ATM, ~15 DTE) with live quotes, prints & BTO/STO/BTC/STC',
    availableFutures: Object.keys(FUTURES_SYMBOLS),
    availableEquities: EQUITY_SYMBOLS
  }));
  ws.on('message', (m)=>{
    try{
      const d = JSON.parse(m.toString());
      if (d.action === 'subscribe') {
        ws._subs = {
          futures: Array.isArray(d.futuresSymbols) ? d.futuresSymbols : DEFAULT_SUBS.futures,
          equities: Array.isArray(d.equitySymbols) ? d.equitySymbols : DEFAULT_SUBS.equities
        };
        ws.send(JSON.stringify({ type:'subscribed', futures: ws._subs.futures, equities: ws._subs.equities }));
      }
    }catch(e){}
  });
  ws.on('close', ()=>clients.delete(ws));
});

app.get('/', (req,res)=>{
  res.setHeader('content-type','text/html; charset=utf-8');
  res.end(`<!doctype html>
<html><head><title>IBKR Flow</title>
<style>
body{font-family:monospace;background:#0a0a0a;color:#0f0;margin:0;padding:16px}
.row{border:1px solid #0f0;margin:10px 0;padding:10px}
.equity{border-left:4px solid #ff00ff}
.futures{border-left:4px solid #00ffff}
.sweep{border-color:#ff0033;background:#1a0000}
.block{border-color:#ffaa00;background:#1a0f00}
.notable{border-color:#00ff00;background:#001a00}
.bto,.btc{color:#00ff99;font-weight:bold}
.sto,.stc{color:#ffaa55;font-weight:bold}
.q{font-size:12px;color:#9a9a9a}
.print{font-size:12px;color:#0ff}
</style></head>
<body>
<h2>🚀 IBKR Flow (25x ATM, ~15DTE)</h2>
<div>WS: ws://localhost:${PORT}/ws</div>
<hr/>
<div id="out"></div>
<script>
const out = document.getElementById('out');
const ws = new WebSocket('ws://'+location.host+'/ws');
ws.onopen=()=>ws.send(JSON.stringify({action:'subscribe',futuresSymbols:['/ES','/NQ'],equitySymbols:['SPY','QQQ']}));
function rowTrade(d){
  const classes = (d.classifications||[]).map(x=>x.toLowerCase()).join(' ');
  const ac = d.assetClass==='FUTURES_OPTION'?'futures':'equity';
  const dir=(d.direction||'').toLowerCase();
  const hist=d.historicalComparison||{};
  const g=d.greeks||{delta:0};
  return \`<div class="row \${classes} \${ac}" id="t-\${d.conid}">
    <div><span class="\${dir}">\${d.direction}</span> \${d.confidence}% |
      <b>\${d.symbol} \${d.type} $\${d.strike}</b> exp \${d.expiry||''} |
      size \${d.size} OI \${d.openInterest ?? '-'} prem $\${(d.premium||0).toFixed(0)} |
      \${d.volOiRatio!=null ? \`vol/OI \${d.volOiRatio.toFixed(2)}\` : ''}</div>
    <div class="q" id="q-\${d.conid}">
      UL $\${(d.underlyingPrice||0).toFixed(2)} | OPT $\${(d.optionPrice||0).toFixed(2)}
      | bid $\${(d.bid||0).toFixed(2)} ask $\${(d.ask||0).toFixed(2)} | Δ \${(g.delta||0).toFixed(3)}
    </div>
    <div class="q">hist: avgOI \${hist.avgOI??'-'} | avgVol \${hist.avgVolume??'-'} | OIΔ \${hist.oiChange??'-'} | Vol× \${hist.volumeMultiple??'-'} | days \${hist.dataPoints??0}</div>
  </div>\`;
}
function rowPrint(p){
  return \`<div class="row print">
    PRINT \${p.symbol} \${p.right} $\${p.strike} exp \${p.expiry||''} |
    size \${p.tradeSize} @ $\${p.tradePrice.toFixed(2)} prem $\${p.premium.toFixed(0)} |
    \${p.volOiRatio!=null ? \`vol/OI \${p.volOiRatio.toFixed(2)}\` : ''} | \${p.aggressor?'BUY-agg':'SELL-agg'}
  </div>\`;
}
function updateQuote(d){
  const el=document.getElementById('q-'+d.conid);
  if(!el) return;
  if(d.type==='LIVE_QUOTE'){
    el.innerHTML=\`OPT $\${d.last.toFixed(2)} (bid $\${d.bid.toFixed(2)} ask $\${d.ask.toFixed(2)}) | Δ \${d.delta.toFixed(3)} | vol \${d.volume} | \${new Date(d.timestamp).toLocaleTimeString()}\`;
  }
}
ws.onmessage=(e)=>{
  const d=JSON.parse(e.data);
  if(d.type==='TRADE'){
    const div=document.createElement('div'); div.innerHTML=rowTrade(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  }else if(d.type==='PRINT'){
    const div=document.createElement('div'); div.innerHTML=rowPrint(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  }else if(d.type==='LIVE_QUOTE' || d.type==='UL_LIVE_QUOTE'){
    updateQuote(d);
  }
};
</script>
</body></html>`);
});

app.get('/health', (req,res)=>res.json({ ok:true, ts:Date.now() }));

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  try {
    await primeIB();
    await setMarketDataLive(); // ok if 404
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }

  server.listen(PORT, () => console.log('[server] listening on :'+PORT));

  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs  = ['SPY','QQQ'];

      for (const f of futs) await loopFuturesSymbol(f);
      for (const s of eqs)  await loopEquitySymbol(s);
      await pollLiveQuotes();
      await sleep(1500);
    }
  }

  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();

