/* eslint-disable no-console */
/**
 * IBKR Advanced Options Flow Server (Equities + Futures)
 * - Auto-picks ~15DTE expiry and 25 ATM contracts (C+P)
 * - Captures UL & OPT price at "trade time"
 * - Streams live quotes; tracks delta
 * - Classifies BTO/STO/BTC/STC (UW-style; OPEN if size > (OI+Vol))
 * - Tracks 12 days OI/Vol history
 * - Emits TRADE + PRINT events; PRINT includes volume/OI ratio
 *
 * Run:
 *   IBKR_HOST=https://127.0.0.1:5000 PORT=3000 NODE_TLS_REJECT_UNAUTHORIZED=0 node index.js
 *   (You must be logged in to IBKR Client Portal and have market data perms.)
 */

/* ================== Imports & Setup ================== */
const http = require('http');
const express = require('express');
const cors = require('cors');
const compression = require('compression');
const morgan = require('morgan');
const axios = require('axios');
const { wrapper } = require('axios-cookiejar-support');
const tough = require('tough-cookie');
const WebSocket = require('ws');

/* ---------- ENV ---------- */
const PORT = parseInt(process.env.PORT || '3000', 10);
const IBKR_HOST = (process.env.IBKR_HOST || 'https://127.0.0.1:5000').replace(/\/+$/,''); // no trailing slash

/* ---------- Axios (cookie jar) ---------- */
const jar = new tough.CookieJar();
const ax = wrapper(axios.create({
  baseURL: `${IBKR_HOST}/v1/api`,
  jar,
  withCredentials: true,
  timeout: 20000,
  // NOTE: SSL trust is handled via NODE_TLS_REJECT_UNAUTHORIZED=0 at runtime if needed
}));

/* ---------- Express ---------- */
const app = express();
app.use(compression());
app.use(cors());
app.use(morgan('tiny'));

/* ---------- HTTP + WS ---------- */
const server = http.createServer(app);
const wss = new WebSocket.Server({ noServer:true });
const clients = new Set();

server.on('upgrade', (req, socket, head) => {
  if (req.url === '/ws') {
    wss.handleUpgrade(req, socket, head, (ws)=> wss.emit('connection', ws, req));
  } else {
    socket.destroy();
  }
});

/* ================== Config & State ================== */

const FUTURES_SYMBOLS = {
  '/ES': { name:'E-mini S&P 500',   exchFOP:'CME',   exchFUT:'GLOBEX', multiplier:50,  ulHintConid:'11004968' },
  '/NQ': { name:'E-mini NASDAQ-100',exchFOP:'CME',   exchFUT:'GLOBEX', multiplier:20,  ulHintConid:'11004958' },
  '/YM': { name:'E-mini Dow',       exchFOP:'CBOT',  exchFUT:'ECBOT',  multiplier:5 },
  '/RTY':{ name:'E-mini Russell 2K',exchFOP:'CME',   exchFUT:'GLOBEX', multiplier:50 },
  '/CL': { name:'Crude Oil',        exchFOP:'NYMEX', exchFUT:'NYMEX',  multiplier:1000 },
  '/GC': { name:'Gold',             exchFOP:'COMEX', exchFUT:'COMEX',  multiplier:100 },
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA','NVDA','AMZN','MSFT','META','GOOGL'];

const THRESHOLDS = {
  sweep:          { minPremium:  50_000, minContracts: 100 },
  block:          { minPremium: 100_000, minContracts:  50 },
  notable:        { minPremium:  25_000, minContracts:  25 },
  futuresSweep:   { minPremium: 100_000, minContracts:  50 },
  futuresBlock:   { minPremium: 200_000, minContracts:  25 },
  futuresNotable: { minPremium:  50_000, minContracts:  10 },
};

const FIELDS = '31,84,85,86,87,88,7295,7308,7309,7310,7311,7283,6509'; // last,bid,bidSz,ask,vol,askSz,OI,greeks,IV,mdType

const historicalData = new Map();      // conid -> [{ date, oi, volume, ts }]
const optionToUL = new Map();          // optionConid -> underlyingConid
const ulForOptionMeta = new Map();     // optionConid -> { isFuture, mult, symbol, right, strike, expiry }
const prevVol = new Map();             // conid -> previous cumulative volume (for PRINT size calc)
const liveQuotes = new Map();          // conid -> last live quote object

const DEFAULT_SUBS = { futures:['/ES','/NQ'], equities:['SPY','QQQ'] };

/* ================== Helpers ================== */

const sleep = (ms)=>new Promise(r=>setTimeout(r,ms));
const nowISO = ()=>new Date().toISOString();
const todayKey = ()=>new Date().toISOString().split('T')[0];

function parseYYYYMMDD(s){
  if (!s) return null;
  if (/^\d{8}$/.test(s)) {
    const y = +s.slice(0,4), m=+s.slice(4,6)-1, d=+s.slice(6,8);
    return new Date(Date.UTC(y,m,d));
  }
  if (/^\d{4}-\d{2}-\d{2}$/.test(s)) return new Date(s+'T00:00:00Z');
  return null;
}
function dte(dateUtc){
  if (!dateUtc) return Infinity;
  const ms = dateUtc - new Date();
  return Math.ceil(ms/86400000);
}
function isFuturesMarketOpen() {
  const now = new Date();
  const d = now.getUTCDay(), h = now.getUTCHours();
  if (d===6) return false;
  if (d===0 && h<23) return false;
  if (d===5 && h>=22) return false;
  return true;
}
function isEquityMarketOpen() {
  const d = new Date().getUTCDay();
  return d>=1 && d<=5;
}

/* ---------- History (12 days) ---------- */
function storeHistoricalData(conid, oi, volume){
  const ts = Date.now();
  const arr = historicalData.get(conid) || [];
  arr.push({ date: todayKey(), oi: +oi||0, volume: +volume||0, ts });
  const cutoff = ts - 12*24*60*60*1000;
  historicalData.set(conid, arr.filter(x=>x.ts>=cutoff));
}
function getHistoricalAverages(conid){
  const arr = historicalData.get(conid) || [];
  if (!arr.length) return { avgOI:0, avgVolume:0, dataPoints:0 };
  const totOI = arr.reduce((s,x)=>s+(x.oi||0),0);
  const totV  = arr.reduce((s,x)=>s+(x.volume||0),0);
  return { avgOI: totOI/arr.length, avgVolume: totV/arr.length, dataPoints: arr.length };
}

/* ================== IBKR API wrappers ================== */

async function primeIB(){
  try { await ax.get('/sso/validate'); } catch {}
  for (let i=0;i<20;i++){
    try{
      const { data } = await ax.get('/iserver/auth/status');
      if (data?.authenticated && data?.connected){
        console.log('\n[IB] authenticated & connected\n');
        return;
      }
      console.log('[IB] status:', data);
    }catch(e){ console.log('[IB] status error:', e.message); }
    await sleep(1000);
  }
  throw new Error('IB not authenticated/connected');
}

async function setMarketDataLive(){
  try{
    await ax.post('/iserver/marketdata/type', { marketDataType: 1 });
    console.log('[IB] market data type set to LIVE');
  }catch(e){
    // Probe, then continue
    try{
      const { data } = await ax.get('/iserver/marketdata/snapshot', {
        params: { conids: '11004968', fields: '6509' }
      });
      const code = data?.[0]?.['6509'];
      console.log(`[IB] market data type probe: ${code || 'unknown'}`);
    }catch{}
    console.warn('[IB] market data type endpoint not available; continuing.');
  }
}

async function ibGet(path, params){ const { data } = await ax.get(path, { params }); return data; }
async function secdefSearch(symbol, secType){ return ibGet('/iserver/secdef/search', { symbol, secType }); }
async function mdSnapshot(conidsArr){
  const conids = Array.isArray(conidsArr) ? conidsArr.join(',') : String(conidsArr);
  return ibGet('/iserver/marketdata/snapshot', { conids, fields: FIELDS, since: 0 });
}
async function trsrvFutures(symbolsCsv){ return ibGet('/trsrv/futures', { symbols: symbolsCsv }); }

/* ================== Selection logic ================== */

async function getFrontFuture(symbol){
  const clean = symbol.replace('/','');
  const list = await secdefSearch(clean, 'FUT'); // typically returns the active root
  // prefer the first; if portal returns multiple, you can refine later
  return list?.[0];
}

async function pickFuturesMonth(symbol, targetDTE=15){
  const clean = symbol.replace('/','');
  const data = await trsrvFutures(clean);
  const rows = data?.[clean] || [];
  if (!rows.length) throw new Error(`No futures months for ${symbol}`);
  const scored = rows.map(r=>{
    const ymd = String(r.expirationDate); // e.g. 20251219
    const y = +ymd.slice(0,4), m = +ymd.slice(4,6)-1, d = +ymd.slice(6,8);
    const exp = new Date(Date.UTC(y,m,d));
    const diff = Math.abs(Math.ceil((exp - new Date())/86400000) - targetDTE);
    return { month: ymd.slice(0,6), score: diff };
  });
  scored.sort((a,b)=>a.score-b.score);
  return scored[0]?.month; // "YYYYMM"
}

function pickContractsAroundATM({ contracts, underlyingPx, targetCount=25 }){
  const calls=[], puts=[];
  for (const c of contracts){
    const isCall = c.right === 'C' || /C\b/.test(c.localSymbol||'') || /C\b/.test(c.description||'');
    const strike = +c.strike || 0;
    const rec = { ...c, isCall, strike, dist: Math.abs(strike - underlyingPx) };
    (isCall ? calls : puts).push(rec);
  }
  calls.sort((a,b)=>a.dist-b.dist);
  puts.sort((a,b)=>a.dist-b.dist);
  const out=[]; let i=0;
  while (out.length<targetCount && (i<calls.length || i<puts.length)){
    if (i<calls.length) out.push(calls[i]);
    if (out.length>=targetCount) break;
    if (i<puts.length) out.push(puts[i]);
    i++;
  }
  return out;
}

function chooseExpiryNear15DTE(list, { target=15, window=10 }){
  const map = new Map(); // expiry -> array
  for (const x of list){
    const exp = x.maturityDate || x.lastTradingDay || x.expiry;
    if (!exp) continue;
    if (!map.has(exp)) map.set(exp, []);
    map.get(exp).push(x);
  }
  let bestExp=null, bestDelta=Infinity;
  for (const [exp, arr] of map){
    const d = dte(parseYYYYMMDD(exp));
    const delta = Math.abs(d - target);
    if (delta < bestDelta && Math.abs(d - target) <= window){
      bestDelta = delta; bestExp = exp;
    }
  }
  if (!bestExp){
    for (const [exp] of map){
      const d = dte(parseYYYYMMDD(exp));
      const delta = Math.abs(d - target);
      if (delta < bestDelta){ bestDelta = delta; bestExp = exp; }
    }
  }
  return bestExp ? map.get(bestExp) : [];
}

/* ---------- Build selections ---------- */

async function buildFuturesOptionSelection(symbol, underlyingPx){
  const meta = FUTURES_SYMBOLS[symbol];
  const fut = await getFrontFuture(symbol);
  if (!fut) return { ulConid:null, options:[] };

  let month;
  try{ month = await pickFuturesMonth(symbol, 15); }
  catch(e){
    console.error('[FUT MONTHS]', symbol, e.message);
    const dt = new Date();
    month = `${dt.getUTCFullYear()}${String(dt.getUTCMonth()+1).padStart(2,'0')}`;
  }

  let info;
  try{
    const ulConid = fut.underlyingConid || fut.conid;
    info = await ibGet('/iserver/secdef/info', { conid: ulConid, sectype:'FOP', month, exchange: meta.exchFOP });
  }catch(e){
    console.error('[FOP INFO]', symbol, e?.status || e?.response?.status, e?.response?.data || e.message);
    return { ulConid: fut.conid, options:[] };
  }

  const raw = Array.isArray(info) ? info : [];
  const norm = raw.map(x=>({
    conid: x.conid,
    right: x.right === 'C' ? 'C' : 'P',
    strike: +x.strike || 0,
    expiry: x.lastTradingDay || x.maturityDate || '',
    exchange: meta.exchFOP,
    symbol
  }));

  const coarse = norm.filter(c => c.strike>0 && Math.abs((c.strike - underlyingPx)/Math.max(1,underlyingPx)) < 0.15);
  const picked = pickContractsAroundATM({ contracts: coarse.length?coarse:norm, underlyingPx, targetCount:25 });
  return { ulConid: fut.conid, options: picked, multiplier: meta.multiplier, isFuture:true };
}

async function findStockConid(symbol){
  const data = await secdefSearch(symbol, 'STK');
  return data?.[0]?.conid || null;
}

async function buildEquityOptionSelection(symbol, underlyingPx){
  const stkConid = await findStockConid(symbol);
  if (!stkConid) return { ulConid:null, options:[] };

  const raw = await secdefSearch(symbol, 'OPT');
  const norm = (Array.isArray(raw)?raw:[]).map(x=>({
    conid: x.conid,
    right: /C\b/.test(x.description||x.localSymbol||'') ? 'C' : 'P',
    strike: +x.strike || 0,
    expiry: x.maturityDate || '',
    exchange: x.exchange || 'SMART',
    symbol
  }));

  const byExp = chooseExpiryNear15DTE(norm, { target:15, window:10 });
  if (!byExp.length) return { ulConid: stkConid, options:[] };

  const picked = pickContractsAroundATM({ contracts: byExp, underlyingPx, targetCount:25 });
  return { ulConid: stkConid, options: picked, multiplier: 100, isFuture:false };
}

/* ================== Streaming & Classification ================== */

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
    ? { sweep:THRESHOLDS.futuresSweep, block:THRESHOLDS.futuresBlock, notable:THRESHOLDS.futuresNotable }
    : { sweep:THRESHOLDS.sweep,        block:THRESHOLDS.block,        notable:THRESHOLDS.notable };
  const out=[];
  if (trade.premium >= t.sweep.minPremium && trade.size >= t.sweep.minContracts && trade.aggressor) out.push('SWEEP');
  if (trade.premium >= t.block.minPremium && trade.size >= t.block.minContracts) out.push('BLOCK');
  if (trade.premium >= t.notable.minPremium && trade.size >= t.notable.minContracts) out.push('NOTABLE');
  return out.length?out:['REGULAR'];
}

function classifyTradeUWStyle(trade, oi, vol, hist){
  // OPEN if size > (OI + Volume) — Unusual Whales style simplifying assumption
  const isAggBuy = !!trade.aggressor;
  if (trade.size > (oi + vol)) return isAggBuy ? 'BTO' : 'STO';

  const volRatio = hist.avgVolume>0 ? (vol/hist.avgVolume) : 1;
  const oiChange = oi - (hist.avgOI||0);
  const spike = volRatio >= 2;

  if (spike && oiChange > 0) return isAggBuy ? 'BTO' : 'STO';
  if (spike && oiChange <= 0) return isAggBuy ? 'BTC' : 'STC';

  if (oi>0 && trade.size/oi > 0.4) return isAggBuy ? 'BTO' : 'STO';
  return isAggBuy ? 'BTC' : 'STC';
}

function confidenceScore(trade, oi, vol, hist){
  let c=50;
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

/* ---------- Broadcast helpers ---------- */
function broadcastAll(obj){
  const s = JSON.stringify(obj);
  for (const ws of clients) if (ws.readyState===WebSocket.OPEN) ws.send(s);
}
function broadcastLiveOption(conid, row){
  const msg = {
    type:'LIVE_QUOTE', conid,
    last:+(row['31']||0), bid:+(row['84']||0), ask:+(row['86']||0),
    volume:+(row['87']||0), delta:+(row['7308']||0), timestamp: Date.now()
  };
  liveQuotes.set(conid, msg);
  broadcastAll(msg);
}
function broadcastLiveUL(conid, row){
  const msg = {
    type:'UL_LIVE_QUOTE', conid,
    last:+(row['31']||0), bid:+(row['84']||0), ask:+(row['86']||0),
    volume:+(row['87']||0), timestamp: Date.now()
  };
  broadcastAll(msg);
}

/* ---------- PRINT emitter (volume delta) ---------- */
function maybeEmitPrint(optionMeta, row, isFuture, multiplier){
  const conid = optionMeta.conid;
  const last  = +row['31'] || 0;
  const vol   = +row['87'] || 0;
  const oi    = +row['7295'] || 0;  // OI = 7295
  if (!vol) return;

  const prevV = prevVol.get(conid) || 0;
  const tradeSize = Math.max(0, vol - prevV);
  prevVol.set(conid, vol);

  if (tradeSize > 0 && last > 0){
    const bid = +row['84'] || 0;
    const ask = +row['86'] || 0;
    const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
    const volOiRatio = oi > 0 ? vol/oi : vol;
    const premium = tradeSize * last * (multiplier||100);

    broadcastAll({
      type:'PRINT',
      conid,
      symbol: optionMeta.symbol,
      right: optionMeta.right === 'C' ? 'CALL' : 'PUT',
      strike: optionMeta.strike,
      expiry: optionMeta.expiry,
      tradePrice: last,
      tradeSize,
      bid, ask, aggressor, premium, volOiRatio,
      timestamp: Date.now()
    });
  }
}

/* ---------- Build TRADE payload ---------- */
function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){
  const last  = +optRow['31'] || 0;
  const vol   = +optRow['87'] || 0;
  const oi    = +optRow['7295'] || 0; // FIXED OI field
  const bid   = +optRow['84'] || 0;
  const ask   = +optRow['86'] || 0;
  const greeks = calcGreeks(optRow);

  storeHistoricalData(optionMeta.conid, oi, vol);
  const hist = getHistoricalAverages(optionMeta.conid);

  const size = vol;
  const premium = last * size * (multiplier||100);
  const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
  const volOiRatio = oi>0 ? (vol/oi) : vol;

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
    multiplier: (multiplier||100),
    exchange: optionMeta.exchange || (isFuture ? FUTURES_SYMBOLS[optionMeta.symbol]?.exchFOP : 'SMART'),
    timestamp: nowISO(),
    greeks,
    volOiRatio
  };

  const direction  = classifyTradeUWStyle(trade, oi, vol, hist);
  const confidence = confidenceScore(trade, oi, vol, hist);
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
        oiChange: Math.round(oi - (hist.avgOI||0)),
        volumeMultiple: hist.avgVolume>0 ? +(vol/hist.avgVolume).toFixed(2) : null,
        dataPoints: hist.dataPoints
      },
      marketSession: isFuture ? (isFuturesMarketOpen() ? 'OPEN' : 'CLOSED')
                              : (isEquityMarketOpen() ? 'REGULAR/EXTENDED' : 'CLOSED')
    },
    optRow
  };
}

/* ---------- Capture + process one option conid ---------- */
async function captureUnderlying(ulConid){
  const snap = await mdSnapshot([ulConid]);
  const row = snap?.[0] || {};
  const px = +row['31'] || 0;
  broadcastLiveUL(ulConid, row);
  return { price: px, row };
}

async function processOptionConid(optionMeta, isFuture, ulConid, multiplier){
  const [optSnap, ul] = await Promise.all([ mdSnapshot([optionMeta.conid]), captureUnderlying(ulConid) ]);
  const optRow = optSnap?.[0];
  if (!optRow) return;

  // link for live quote polling
  optionToUL.set(optionMeta.conid, ulConid);
  ulForOptionMeta.set(optionMeta.conid, {
    isFuture, mult: multiplier, symbol: optionMeta.symbol,
    right: optionMeta.right, strike: optionMeta.strike, expiry: optionMeta.expiry
  });

  // TRADE
  const { payload, optRow: rowForPrint } = buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier });
  if (payload.premium >= 1000) broadcastAll(payload);

  // PRINT
  maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);

  // LIVE_QUOTE snapshot for UI
  broadcastLiveOption(optionMeta.conid, optRow);
}

/* ---------- Loops ---------- */
async function loopFuturesSymbol(symbol){
  try{
    const meta = FUTURES_SYMBOLS[symbol];
    const fut = await getFrontFuture(symbol);
    if (!fut) return;

    const ulSnap = await mdSnapshot([fut.conid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = +ulRow['31'] || 0;
    broadcastLiveUL(fut.conid, ulRow);

    const sel = await buildFuturesOptionSelection(symbol, ulPx);
    for (const m of sel.options) {
      await processOptionConid(m, true, sel.ulConid, meta.multiplier);
      await sleep(100);
    }
  }catch(e){
    console.error('[FUT LOOP]', symbol, e?.response?.data || e.message);
  }
}

async function loopEquitySymbol(symbol){
  try{
    const stkConid = await findStockConid(symbol);
    if (!stkConid) return;

    const ulSnap = await mdSnapshot([stkConid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = +ulRow['31'] || 0;
    broadcastLiveUL(stkConid, ulRow);

    const sel = await buildEquityOptionSelection(symbol, ulPx);
    for (const m of sel.options) {
      await processOptionConid(m, false, sel.ulConid, sel.multiplier);
      await sleep(80);
    }
  }catch(e){
    console.error('[EQ LOOP]', symbol, e?.response?.data || e.message);
  }
}

async function pollLiveQuotes(){
  try{
    const optionConids = Array.from(optionToUL.keys());
    if (!optionConids.length) return;

    const snaps = await mdSnapshot(optionConids);
    for (let i=0;i<snaps.length;i++){
      const row = snaps[i];
      const conid = row.conid || optionConids[i];

      // live option quote
      broadcastLiveOption(conid, row);

      // maybe PRINT
      const meta = ulForOptionMeta.get(conid);
      if (meta){
        const optionMeta = { conid, symbol: meta.symbol, right: meta.right, strike: meta.strike, expiry: meta.expiry };
        maybeEmitPrint(optionMeta, row, meta.isFuture, meta.mult);
      }

      // refresh UL
      const ulConid = optionToUL.get(conid);
      if (ulConid){
        const ulSnap = await mdSnapshot([ulConid]);
        broadcastLiveUL(ulConid, ulSnap?.[0] || {});
      }

      await sleep(20);
    }
  }catch(e){}
}

/* ================== WS & UI ================== */

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
      if (d.action === 'subscribe'){
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

async function coordinatorLoop(){
  while(true){
    const futSet = new Set(), eqSet = new Set();
    for (const ws of clients){
      const s = ws._subs || DEFAULT_SUBS;
      (s.futures||[]).forEach(x=>futSet.add(x));
      (s.equities||[]).forEach(x=>eqSet.add(x));
    }
    const futs = Array.from(futSet), eqs = Array.from(eqSet);
    for (const f of futs) await loopFuturesSymbol(f);
    for (const s of eqs)  await loopEquitySymbol(s);
    await pollLiveQuotes();
    await sleep(1500);
  }
}
/* ---------- Minimal in-browser viewer (robust) ---------- */
app.get('/', (req,res)=>{
  res.setHeader('content-type','text/html; charset=utf-8');
  res.end(`<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <title>IBKR Flow</title>
  <!-- Tiny inline favicon to avoid 404s -->
  <link rel="icon" href='data:image/svg+xml,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><text y="50" font-size="48">⚡️</text></svg>'>
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
    small{color:#9a9a9a}
    .chip{display:inline-block;padding:1px 6px;border:1px solid #444;border-radius:8px;margin-left:8px;font-size:11px;color:#ccc}
    .live{border-color:#0f0;color:#0f0}
    .idle{border-color:#666;color:#888}
  </style>
</head>
<body>
  <h2>🚀 IBKR Flow (25x ATM, ~15DTE)</h2>
  <div>WS: ws://localhost:${PORT}/ws</div>
  <hr/>
  <div id="out"></div>

  <script>
    // ------- helpers: safe formatting -------
    function fnum(x, d=2) {
      if (x === null || x === undefined) return '-';
      const n = Number(x);
      if (!isFinite(n)) return '-';
      return n.toFixed(d);
    }
    function fint(x) {
      if (x === null || x === undefined) return '-';
      const n = Number(x);
      if (!isFinite(n)) return '-';
      return String(Math.round(n));
    }

    const out = document.getElementById('out');
    const ws  = new WebSocket('ws://'+location.host+'/ws');
    ws.onopen = () => ws.send(JSON.stringify({
      action:'subscribe',
      futuresSymbols:['/ES','/NQ'],
      equitySymbols:['SPY','QQQ']
    }));

    function statusChipHTML(hasLast){
      return '<span class="chip '+(hasLast?'live':'idle')+'">'+(hasLast?'LIVE':'NO_TRADE_YET')+'</span>';
    }

    function rowTrade(d){
      const classes = (d.classifications||[]).map(x=>x.toLowerCase()).join(' ');
      const ac  = d.assetClass==='FUTURES_OPTION'?'futures':'equity';
      const dir = (d.direction||'').toLowerCase();
      const hist= d.historicalComparison||{};
      const g   = d.greeks||{delta:0};

      const hasLast = Number.isFinite(+d.optionPrice) && +d.optionPrice>0;

      return \`<div class="row \${classes} \${ac}" id="t-\${d.conid}">
        <div>
          <span class="\${dir}">\${d.direction||'-'}</span>
          \${fint(d.confidence)}% \${statusChipHTML(hasLast)} |
          <b>\${d.symbol} \${d.type} $\${fnum(d.strike,2)}</b>
          exp \${d.expiry || '-'} |
          size \${fint(d.size)} OI \${fint(d.openInterest)}
          prem $\${fnum(d.premium,0)} |
          vol/OI \${d.volOiRatio==null?'-':fnum(d.volOiRatio,2)}
        </div>

        <div class="q" id="q-\${d.conid}">
          UL $\${fnum(d.underlyingPrice,2)} |
          OPT $\${fnum(d.optionPrice,2)} |
          bid $\${fnum(d.bid,2)} ask $\${fnum(d.ask,2)} |
          Δ \${fnum(g.delta,3)}
        </div>

        <small>
          hist: avgOI \${fint(hist.avgOI)} |
          avgVol \${fint(hist.avgVolume)} |
          OIΔ \${fint(hist.oiChange)} |
          Vol× \${hist.volumeMultiple==null?'-':fnum(hist.volumeMultiple,2)} |
          days \${fint(hist.dataPoints)}
        </small>
      </div>\`;
    }

    function rowPrint(p){
      return \`<div class="row print">
        PRINT \${p.symbol} \${p.right} $\${fnum(p.strike)} exp \${p.expiry||'-'} |
        size \${fint(p.tradeSize)} @ $\${fnum(p.tradePrice,2)}
        prem $\${fnum(p.premium,0)} |
        vol/OI \${p.volOiRatio==null?'-':fnum(p.volOiRatio,2)} |
        \${p.aggressor?'BUY-agg':'SELL-agg'}
      </div>\`;
    }

    // Only update option rows here. UL ticks are ignored (they don't map 1:1 to trade rows in the viewer).
    function updateQuote(d){
      if (d.type !== 'LIVE_QUOTE') return; // ignore UL_LIVE_QUOTE in this updater
      const el = document.getElementById('q-'+d.conid);
      if(!el) return;
      el.innerHTML = \`OPT $\${fnum(d.last)} (bid $\${fnum(d.bid)} ask $\${fnum(d.ask)}) |
                      Δ \${fnum(d.delta,3)} | vol \${fint(d.volume)} |
                      \${new Date(d.timestamp).toLocaleTimeString()}\`;
      const row = document.getElementById('t-'+d.conid);
      if (row) {
        const chip = row.querySelector('.chip');
        if (chip) { chip.className='chip live'; chip.textContent='LIVE'; }
      }
    }

    ws.onmessage = (e) => {
      const d = JSON.parse(e.data);
      if (d.type === 'TRADE') {
        const div = document.createElement('div');
        div.innerHTML = rowTrade(d);
        out.insertBefore(div.firstElementChild, out.firstChild);
        while(out.children.length > 100) out.removeChild(out.lastChild);
      } else if (d.type === 'PRINT') {
        const div = document.createElement('div');
        div.innerHTML = rowPrint(d);
        out.insertBefore(div.firstElementChild, out.firstChild);
        while(out.children.length > 100) out.removeChild(out.lastChild);
      } else if (d.type === 'LIVE_QUOTE' || d.type === 'UL_LIVE_QUOTE') {
        updateQuote(d); // will ignore UL
      }
    };
  </script>
</body>
</html>`);
});

app.get('/health', (req,res)=>res.json({ ok:true, ts:Date.now() }));

/* ================== Boot ================== */
(async ()=>{
  try{
    console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
    await primeIB();
    await setMarketDataLive();

    server.listen(PORT, ()=>console.log('[server] listening on :'+PORT));

    // start coordinator & pollers
    coordinatorLoop().catch(e=>console.error('[coordinator]', e?.response?.data || e.message));
    setInterval(()=>{ pollLiveQuotes().catch(()=>{}); }, 1500);
  }catch(e){
    console.error('[boot]', e?.response?.data || e.message || e);
    process.exit(1);
  }
})();

