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
 *   IBKR_HOST=http://127.0.0.1:5000 PORT=3000 node flow-server.js
 */

/* ====== header you can paste ====== */
/* ====== header you can paste (fixed) ====== */
const http = require('http');
const https = require('https');
const express = require('express');
const cors = require('cors');
const compression = require('compression');
const morgan = require('morgan');
const axios = require('axios');
const { wrapper } = require('axios-cookiejar-support');
const tough = require('tough-cookie');
const WebSocket = require('ws');             // ✅ add this

const jar = new tough.CookieJar();

// AFTER (✅ works with axios-cookiejar-support)
const ax = wrapper(axios.create({
  baseURL: `https://127.0.0.1:5000/v1/api`,
  jar,
  withCredentials: true,
  timeout: 15000
}));

const app = express();
app.use(compression());
app.use(cors());
app.use(morgan('tiny'));

const PORT = parseInt(process.env.PORT || '3000', 10);
const IBKR_HOST = process.env.IBKR_HOST || 'http://localhost:5000';

// ------------ Flow thresholds -------------
const THRESHOLDS = {
  sweep: { minPremium: 50000,  minContracts: 100 },
  block: { minPremium: 100000, minContracts: 50  },
  notable:{ minPremium: 25000,  minContracts: 25  },
  futuresSweep: { minPremium: 100000, minContracts: 50 },
  futuresBlock: { minPremium: 200000, minContracts: 25 },
  futuresNotable:{ minPremium: 50000,  minContracts: 10 }
};

const FUTURES_SYMBOLS = {
  '/ES': { name:'E-mini S&P 500', exchange:'GLOBEX', multiplier:50 },
  '/NQ': { name:'E-mini NASDAQ-100', exchange:'GLOBEX', multiplier:20 },
  '/YM': { name:'E-mini Dow', exchange:'ECBOT', multiplier:5 },
  '/RTY':{ name:'E-mini Russell 2000', exchange:'GLOBEX', multiplier:50 },
  '/CL': { name:'Crude Oil', exchange:'NYMEX', multiplier:1000 },
  '/GC': { name:'Gold', exchange:'COMEX', multiplier:100 },
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA','NVDA','AMZN','MSFT','META','GOOGL'];

// ------------ State -----------------------
const server = http.createServer(app);
const wss = new WebSocket.Server({ noServer:true });
server.on('upgrade', (req, socket, head) => {
  if (req.url === '/ws') wss.handleUpgrade(req, socket, head, ws => wss.emit('connection', ws, req));
  else socket.destroy();
});
const clients = new Set();

const historicalData = new Map();   // conid -> [{date, oi, volume, ts}]
const liveQuotes = new Map();       // conid -> last quote cache
const optionToUL = new Map();       // optionConid -> underlyingConid
const prevVol = new Map();          // conid -> previous cumulative volume (for PRINT)
const prevLast = new Map();         // conid -> previous last price (optional)
const ulForOptionMeta = new Map();  // conid -> { isFuture, mult, symbol }

// ------------ Utils -----------------------
const sleep = (ms)=>new Promise(r=>setTimeout(r,ms));
const nowISO = ()=>new Date().toISOString();
const todayKey = ()=>new Date().toISOString().split('T')[0];

function isFuturesMarketOpen() {
  const now = new Date();
  const d = now.getUTCDay();
  const h = now.getUTCHours();
  if (d===6) return false;
  if (d===0 && h<23) return false;
  if (d===5 && h>=22) return false;
  return true;
}
function isEquityMarketOpen() {
  const d = new Date().getUTCDay();
  return d>=1 && d<=5;
}
function parseYYYYMMDD(s){
  // Accept "YYYYMMDD" or "YYYY-MM-DD"
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
  return Math.ceil(ms/(24*60*60*1000));
}
async function setMarketDataLive() {
  try {
    await ax.post('/iserver/marketdata/type', { marketDataType: 1 }); // 1=LIVE, 2=DELAYED
    console.log('[IB] market data type set to LIVE');
  } catch (e) {
    console.error('[IB] could not set market data type:', e.response?.status, e.response?.data || e.message);
  }
}


// ------------ History (12 days) -----------
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
async function pickFuturesMonth(symbol) {
  const clean = symbol.replace('/', '');
  const monthsResp = await ax.get('/trsrv/futures', { params: { symbols: clean } });
  const months = monthsResp.data?.[clean]?.months || [];
  if (!months.length) throw new Error(`No futures months for ${symbol}`);

  // months like "202512" → pick ~15 DTE by converting each month to last biz day
  const scored = months.map(m => {
    const y = +m.slice(0,4), mo = +m.slice(4,6) - 1;
    // crude approx: 3rd Friday of the month (common equity opt style; works ok for ES)
    const d = new Date(Date.UTC(y, mo, 1));
    let fridays = 0, best = null;
    for (let i=0;i<31;i++) {
      const dt = new Date(Date.UTC(y, mo, 1+i));
      if (dt.getUTCMonth() !== mo) break;
      if (dt.getUTCDay() === 5) { fridays++; best = dt; }
      if (fridays === 3) { best = dt; break; }
    }
    const dte = Math.ceil((best - new Date()) / 86400000);
    return { month: m, dte: isFinite(dte) ? Math.abs(dte - 15) : 9999 };
  });
  scored.sort((a,b) => a.dte - b.dte);
  return scored[0].month;
}
async function buildFuturesOptionSelection(symbol, underlyingPx) {
  const futMeta = FUTURES_SYMBOLS[symbol];
  const fut = await getFrontFuture(symbol);
  if (!fut) return { ulConid: null, options: [] };

  // NEW: ask /trsrv/futures for months, then request a SPECIFIC month
  let month;
  try {
    month = await pickFuturesMonth(symbol);
  } catch (e) {
    console.error('[FUT MONTHS]', symbol, e.message);
    // fallback: try next two months commonly used on CME (very naive)
    const y = new Date().getUTCFullYear();
    const m = String(new Date().getUTCMonth()+2).padStart(2, '0');
    month = `${y}${m}`;
  }

  // IMPORTANT: pass explicit month, not "ALL" → avoids many 500s
  let info;
  try {
    info = await ax.get('/iserver/secdef/info', {
      params: { conid: fut.conid, sectype: 'FOP', month, exchange: futMeta.exchange }
    });
  } catch (e) {
    console.error('[FOP INFO]', symbol, e.response?.status, e.response?.data || e.message);
    return { ulConid: fut.conid, options: [] };
  }

  const raw = Array.isArray(info.data) ? info.data : [];

  const norm = raw.map(x => ({
    conid: x.conid,
    right: x.right === 'C' ? 'C' : 'P',
    strike: +x.strike || 0,
    expiry: x.lastTradingDay || x.maturityDate || '',
    exchange: futMeta.exchange,
    symbol
  }));

  // If your info result is huge, optionally prefilter by strikes within ±15% of ATM
  const coarse = norm.filter(c => c.strike > 0 && Math.abs((c.strike - underlyingPx)/Math.max(1,underlyingPx)) < 0.15);

  const picked = pickContractsAroundATM({
    contracts: coarse.length ? coarse : norm,
    underlyingPx,
    targetCount: 25
  });

  return { ulConid: fut.conid, options: picked };
}
async function primeIB() {
  // Hit /sso/validate to set cookies
  try {
    await ax.get('/sso/validate');
  } catch {}

  // Wait until authenticated & connected
  for (let i = 0; i < 20; i++) {
    try {
      const { data } = await ax.get('/iserver/auth/status');
      if (data?.authenticated && data?.connected) {
        console.log('[IB] authenticated & connected');
        return;
      }
      console.log('[IB] status:', data);
    } catch (e) {
      console.log('[IB] status error:', e.message);
    }
    await new Promise(r => setTimeout(r, 1000));
  }
  throw new Error('IB not authenticated/connected');
}

// ------------ IB helpers ------------------
async function ibGet(path, params){
  const url = `${IBKR_HOST}/v1/api${path}`;
  const { data } = await ax.get(url, { params });
  return data;
}
async function findStockConid(symbol){
  const data = await ibGet('/iserver/secdef/search', { symbol, secType:'STK' });
  return data?.[0]?.conid;
}
async function secdefSearch(symbol, secType){
  return ibGet('/iserver/secdef/search', { symbol, secType });
}
async function secdefInfo(conid, sectype, exchange, month='ALL'){
  return ibGet('/iserver/secdef/info', { conid, sectype, exchange, month });
}
const FIELDS = '31,84,85,86,87,7308,7309,7310,7311,7283';
async function mdSnapshot(conids){
  const data = await ibGet('/iserver/marketdata/snapshot', { conids: conids.join(','), fields: FIELDS, since:0 });
  return data;
}

// ------------ Greeks, tags, direction -----
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
  // OPEN if size > (OI + Volume)
  const isAggBuy = !!trade.aggressor;
  if (trade.size > (oi + vol)) return isAggBuy ? 'BTO' : 'STO';

  const volRatio = hist.avgVolume > 0 ? (vol / hist.avgVolume) : 1;
  const oiChange = oi - (hist.avgOI||0);
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

// ------------ Broadcast helpers -----------
function broadcastAll(obj){
  const s = JSON.stringify(obj);
  for (const ws of clients) if (ws.readyState===WebSocket.OPEN) ws.send(s);
}
function broadcastLiveOption(conid, row){
  const msg = {
    type:'LIVE_QUOTE', conid,
    last:+(row['31']||0), bid:+(row['84']||0), ask:+(row['86']||0),
    volume:+(row['87']||0), delta:+(row['7308']||0),
    timestamp: Date.now()
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

// ------------ NEW: ATM & ~15DTE selection -
function pickContractsAroundATM({ contracts, underlyingPx, targetCount=25 }) {
  // Split calls/puts, sort by |strike-ATM|, then interleave to keep both sides
  const calls = [];
  const puts  = [];
  for (const c of contracts) {
    const isCall = c.right === 'C' || /C\b/.test(c.right||'') || /C\b/.test(c.localSymbol||'') || /C\b/.test(c.description||'');
    const strike = +c.strike || 0;
    const rec = { ...c, isCall, strike, dist: Math.abs(strike - underlyingPx) };
    (isCall ? calls : puts).push(rec);
  }
  calls.sort((a,b)=>a.dist-b.dist);
  puts.sort((a,b)=>a.dist-b.dist);
  const out = [];
  let i=0;
  while (out.length < targetCount && (i < calls.length || i < puts.length)) {
    if (i < calls.length) out.push(calls[i]);
    if (out.length >= targetCount) break;
    if (i < puts.length) out.push(puts[i]);
    i++;
  }
  return out;
}

function chooseExpiryNear15DTE(list, { target=15, window=10 }) {
  // group by expiry; pick one expiry whose DTE closest to target and within +/-window
  const map = new Map(); // expiry -> array
  for (const x of list) {
    const exp = x.maturityDate || x.lastTradingDay || x.expiry;
    if (!exp) continue;
    const k = exp;
    if (!map.has(k)) map.set(k, []);
    map.get(k).push(x);
  }
  let bestExp = null;
  let bestDelta = Infinity;
  for (const [exp, arr] of map) {
    const d = dte(parseYYYYMMDD(exp));
    const delta = Math.abs(d - target);
    if (delta < bestDelta && Math.abs(d - target) <= window) {
      bestDelta = delta; bestExp = exp;
    }
  }
  if (!bestExp) {
    // fallback: pick the absolute closest even if outside window
    for (const [exp, arr] of map) {
      const d = dte(parseYYYYMMDD(exp));
      const delta = Math.abs(d - target);
      if (delta < bestDelta) { bestDelta = delta; bestExp = exp; }
    }
  }
  if (!bestExp) return [];
  return map.get(bestExp);
}

// ------------ NEW: Prints emitter ----------
function maybeEmitPrint(optionMeta, row, isFuture, multiplier) {
  const conid = optionMeta.conid;
  const last  = +row['31'] || 0;
  const vol   = +row['87'] || 0;
  const oi    = +row['84'] || 0; // if your OI field differs, map it here.
  if (!vol) return;

  const prevV = prevVol.get(conid) || 0;
  const tradeSize = vol - prevV;
  prevVol.set(conid, vol);
  prevLast.set(conid, last);

  if (tradeSize > 0 && last > 0) {
    const bid = +row['84'] || 0;
    const ask = +row['86'] || 0;
    const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
    const volOiRatio = oi > 0 ? vol / oi : vol; // publish cumulative ratio
    const premium = tradeSize * last * multiplier;

    broadcastAll({
      type: 'PRINT',
      conid,
      symbol: optionMeta.symbol,
      right: optionMeta.right === 'C' ? 'CALL' : 'PUT',
      strike: optionMeta.strike,
      expiry: optionMeta.expiry,
      tradePrice: last,
      tradeSize,
      bid, ask,
      aggressor,
      premium,
      volOiRatio,
      timestamp: Date.now()
    });
  }
}

// ------------ Core processing -------------
async function captureUnderlying(ulConid){
  const snap = await mdSnapshot([ulConid]);
  const row = snap?.[0] || {};
  const px = +row['31'] || 0;
  broadcastLiveUL(ulConid, row);
  return { price: px, row };
}

function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }) {
  const last = +optRow['31'] || 0;
  const vol  = +optRow['87'] || 0;
  const oi   = +optRow['84'] || 0;
  const bid  = +optRow['84'] || 0;
  const ask  = +optRow['86'] || 0;
  const greeks = calcGreeks(optRow);

  storeHistoricalData(optionMeta.conid, oi, vol);
  const hist = getHistoricalAverages(optionMeta.conid);

  const size = vol;
  const premium = last * size * multiplier;
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
    multiplier,
    exchange: optionMeta.exchange || (isFuture ? 'GLOBEX' : 'SMART'),
    timestamp: nowISO(),
    greeks,
    volOiRatio // NEW: included in TRADE
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

async function processOptionConid(optionMeta, isFuture, ulConid, multiplier){
  const [optSnap, ul] = await Promise.all([ mdSnapshot([optionMeta.conid]), captureUnderlying(ulConid) ]);
  const optRow = optSnap?.[0];
  if (!optRow) return;

  // Link for live-quote pumping
  optionToUL.set(optionMeta.conid, ulConid);
  ulForOptionMeta.set(optionMeta.conid, { isFuture, mult: multiplier, symbol: optionMeta.symbol });

  // Build TRADE and broadcast
  const { payload, optRow: rowForPrint } = buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier });

  // guard: avoid spammy micro prints; still broadcast live delta below
  if (payload.premium >= 1000) broadcastAll(payload);

  // Emit PRINT if volume incremented
  maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);

  // Also push an immediate LIVE_QUOTE snapshot for option (shows delta)
  broadcastLiveOption(optionMeta.conid, optRow);
}

// ------------ Underlying resolution -------
async function getFrontFuture(symbol){
  const clean = symbol.replace('/','');
  const list = await secdefSearch(clean, 'FUT');
  return list?.[0];
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
  if (!forExpiry.length) return { ulConid: stkConid, options: [] };

  const picked = pickContractsAroundATM({ contracts: forExpiry, underlyingPx, targetCount:25 });
  return { ulConid: stkConid, options: picked };
}

// ------------ Loops -----------------------
async function loopFuturesSymbol(symbol){
  try{
    const fut = await getFrontFuture(symbol);
    if (!fut) return;

    // Underlying price
    const ulSnap = await mdSnapshot([fut.conid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = +ulRow['31'] || 0;
    broadcastLiveUL(fut.conid, ulRow);

    const { ulConid, options } = await buildFuturesOptionSelection(symbol, ulPx);
    for (const meta of options) {
      await processOptionConid(meta, true, ulConid, FUTURES_SYMBOLS[symbol].multiplier);
      await sleep(120);
    }
  }catch(e){ console.error('[FUT LOOP]', symbol, e.message); }
}

async function loopEquitySymbol(symbol){
  try{
    const stkConid = await findStockConid(symbol);
    if (!stkConid) return;

    const ulSnap = await mdSnapshot([stkConid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = +ulRow['31'] || 0;
    broadcastLiveUL(stkConid, ulRow);

    const { ulConid, options } = await buildEquityOptionSelection(symbol, ulPx);
    for (const meta of options) {
      await processOptionConid(meta, false, ulConid, 100);
      await sleep(90);
    }
  }catch(e){ console.error('[EQ LOOP]', symbol, e.message); }
}

// Pump live quotes for already-linked options/ULs, detect PRINT deltas too
async function pollLiveQuotes(){
  try{
    const optionConids = Array.from(optionToUL.keys());
    if (!optionConids.length) return;

    const snaps = await mdSnapshot(optionConids);
    for (let i=0;i<snaps.length;i++){
      const row = snaps[i];
      const conid = row.conid || optionConids[i];
      broadcastLiveOption(conid, row);

      // NEW: print detection on polling too
      const meta = ulForOptionMeta.get(conid);
      if (meta) {
        const optionMeta = { conid, symbol: meta.symbol, right: (row.right==='C'?'C':'P'), strike: +(row.strike||0), expiry: row.maturityDate||'' };
        maybeEmitPrint(optionMeta, row, meta.isFuture, meta.mult);
      }

      const ulConid = optionToUL.get(conid);
      if (ulConid) {
        const ulSnap = await mdSnapshot([ulConid]);
        broadcastLiveUL(ulConid, ulSnap?.[0] || {});
      }
      await sleep(25);
    }
  }catch(e){}
}

// ------------ WS & coordinator ------------
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
        ws.send(JSON.stringify({ type:'subscribed', ...ws._subs }));
      }
    }catch(e){}
  });
  ws.on('close', ()=>clients.delete(ws));
});

async function coordinatorLoop(){
  while(true){
    const futSet = new Set(), eqSet = new Set();
    for (const ws of clients) {
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

// ------------ Minimal UI ------------------
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
      size \${d.size} OI \${d.openInterest} prem $\${(d.premium||0).toFixed(0)} |
      vol/OI \${(d.volOiRatio??0).toFixed(2)}</div>
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
    vol/OI \${(p.volOiRatio??0).toFixed(2)} | \${p.aggressor?'BUY-agg':'SELL-agg'}
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

// Health
app.get('/health', (req,res)=>res.json({ ok:true, ts:Date.now() }));


// --- startup (CommonJS safe) ---
(async () => {
  try {
    console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);

    await primeIB();            // ✅ ok inside async IIFE
    await setMarketDataLive();  // ✅ set LIVE market data

    server.listen(PORT, () => {
      console.log(`[server] listening on :${PORT}`);
    });

    // kick off loops
    coordinatorLoop().catch((e) => console.error('[coordinator]', e.message));
    setInterval(() => { pollLiveQuotes().catch(()=>{}); }, 1500);
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
    process.exit(1);
  }
})();