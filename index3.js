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

// const FUTURES_SYMBOLS = {
//   '/ES': { name:'E-mini S&P 500', exchange:'GLOBEX', multiplier:50 },
//   '/NQ': { name:'E-mini NASDAQ-100', exchange:'GLOBEX', multiplier:20 },
//   '/YM': { name:'E-mini Dow', exchange:'ECBOT', multiplier:5 },
//   '/RTY':{ name:'E-mini Russell 2000', exchange:'GLOBEX', multiplier:50 },
//   '/CL': { name:'Crude Oil', exchange:'NYMEX', multiplier:1000 },
//   '/GC': { name:'Gold', exchange:'COMEX', multiplier:100 }
// };
const FUTURES_SYMBOLS = {
  '/ES': { name: 'E-mini S&P 500', exchange: 'CME', multiplier: 50 },
  '/NQ': { name: 'E-mini NASDAQ-100', exchange: 'CME', multiplier: 20 },
  '/YM': { name: 'E-mini Dow', exchange: 'CBOT', multiplier: 5 },
  '/RTY': { name: 'E-mini Russell 2000', exchange: 'CME', multiplier: 50 },
  '/CL': { name: 'Crude Oil', exchange: 'NYMEX', multiplier: 1000 },
  '/GC': { name: 'Gold', exchange: 'COMEX', multiplier: 100 }
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA','NVDA','AMZN','MSFT','META','GOOGL'];

/* --------------------------- State ------------------------------------- */
const historicalData = new Map();   // conid -> [{date, oi, volume, ts}]
const liveQuotes     = new Map();   // conid -> last quote cache
const optionToUL     = new Map();   // optionConid -> underlyingConid
const prevVol        = new Map();   // conid -> previous cumulative volume (for PRINT)
const ulForOption    = new Map();   // option conid -> { isFuture, mult, symbol }

/* --------------------------- Utils ------------------------------------- */
const sleep  = (ms)=>new Promise(r=>setTimeout(r,ms));
const nowISO = ()=>new Date().toISOString();
const todayKey = ()=>new Date().toISOString().split('T')[0];

function px(v){
  if (v == null) return 0;
  const n = parseFloat(String(v).replace(/[^\d\.\-\+]/g, ''));
  return isFinite(n) ? n : 0;
}

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
  // const FIELDS = '31,84,85,86,87,7308,7309,7310,7311,7283';
  // 31=last, 84=bid, 85=bidSize, 86=ask, 88=lastSize, 7762=day volume (hi-prec),
  // 7308..7311 greeks, 7283=IV. Add others later (see IBKR ref).
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
  // OPEN if size > (OI + Volume)
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
// Send mapping updates when new conids are discovered
function broadcastConidMapping(conid, mapping) {
  broadcastAll({
    type: 'CONID_MAPPING',
    conid,
    mapping
  });
}
/* --------------------------- Broadcast --------------------------------- */
// function broadcastAll(o){ const s = JSON.stringify(o); for (const ws of clients) if (ws.readyState===WebSocket.OPEN) ws.send(s); }
function broadcastAll(o){ 
  const s = JSON.stringify(o); 
  for (const ws of clients) {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(s);
    }
  }
}

function broadcastLiveOption(conid, row){
  const msg = {
    type:'LIVE_QUOTE', conid,
    last:px(row['31']), bid:px(row['84']), ask:px(row['86']),
    volume:+row['7762']||0, delta:+row['7308']||0, timestamp: Date.now()
  };
  liveQuotes.set(conid, msg);
  broadcastAll(msg);
}
function broadcastLiveUL(conid, row){
  const msg = {
    type:'UL_LIVE_QUOTE', conid,
    last:px(row['31']), bid:px(row['84']), ask:px(row['86']),
    volume:+row['87']||0, timestamp: Date.now()
  };
  broadcastAll(msg);
}

/* --------------------- ATM / ~15DTE picking --------------------------- */
function chooseExpiryNear15DTE(list, { target=15, window=10 }){
  const byExp = new Map();
  for (const x of list) {
    const exp = x.maturityDate || x.lastTradingDay || x.expiry;
    if (!exp) continue;
    const k = exp;
    if (!byExp.has(k)) byExp.set(k, []);
    byExp.get(k).push(x);
  }
  let bestExp = null, bestDelta = Infinity;
  for (const [exp, arr] of byExp) {
    const d = dte(parseYYYYMMDD(exp));
    const delta = Math.abs(d - target);
    if (delta <= window && delta < bestDelta) { bestDelta = delta; bestExp = exp; }
  }
  if (!bestExp) {
    for (const [exp, arr] of byExp) {
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

function maybeEmitPrint(optionMeta, row, isFuture, multiplier) {
  const conid = optionMeta.conid;
  const last = px(row['31']);
  const volume = +row['87'] || 0; // Changed from 'vol' to 'volume'
  const oi = +row['84'] || 0;
  
  if (!volume) return;

  const prevVolume = prevVol.get(conid) || 0; // Changed from prevV to prevVolume
  const tradeSize = volume - prevVolume;
  prevVol.set(conid, volume);

  if (tradeSize > 0 && last > 0) {
    const bid = px(row['84']), ask = px(row['86']);
    const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last - ask) < Math.abs(last - bid)) : true));
    const volOiRatio = oi > 0 ? volume / oi : volume;
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
      bid,
      ask,
      aggressor,
      premium,
      volOiRatio,
      timestamp: Date.now()
    });
  }
}

/* --------------------- Futures helpers (months) ------------------------ */
// Your CP returns: { ES:[{expirationDate:YYYYMMDD,...},...], NQ:[...] }
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

async function getFrontFutureMonth(symbol) {
  const cleanSymbol = symbol.replace('/', '');
  try {
    // Get current month and year for futures codes
    const now = new Date();
    const currentYear = now.getUTCFullYear();
    const currentMonth = now.getUTCMonth() + 1;
    
    // Futures month codes: F=Jan, G=Feb, H=Mar, J=Apr, K=May, M=Jun, 
    // N=Jul, Q=Aug, U=Sep, V=Oct, X=Nov, Z=Dec
    const monthCodes = ['F','G','H','J','K','M','N','Q','U','V','X','Z'];
    
    // Find the front month (usually current or next month)
    let frontMonthIndex = currentMonth - 1;
    let frontYear = currentYear;
    
    // If we're past the 15th, look at next month
    if (now.getUTCDate() > 15) {
      frontMonthIndex = (frontMonthIndex + 1) % 12;
      if (frontMonthIndex === 0) frontYear++;
    }
    
    const monthCode = monthCodes[frontMonthIndex];
    const yearCode = frontYear.toString().slice(-1); // Last digit of year
    
    return `${monthCode}${yearCode}`;
  } catch (e) {
    console.error(`[FUT MONTH] ${symbol} error:`, e.message);
    // Fallback to current month
    const monthCodes = ['F','G','H','J','K','M','N','Q','U','V','X','Z'];
    const now = new Date();
    return `${monthCodes[now.getUTCMonth()]}${now.getUTCFullYear().toString().slice(-1)}`;
  }
}

async function getFuturesOptionsChain(futuresConid, exchange) {
  try {
    // Try to get options chain using the futures conid
    const params = {
      conid: futuresConid,
      sectype: 'FOP',
      exchange: exchange || 'GLOBEX'
    };
    
    const data = await ibGet('/iserver/secdef/info', params);
    return Array.isArray(data) ? data : [];
  } catch (e) {
    console.error(`[FOP CHAIN] conid ${futuresConid}:`, e.message);
    return [];
  }
}

/* === helper: choose a YYYYMM for equities from the 'months' string === */
function pickEquityYYYYMMFromMonthsString(monthsStr, { targetDte = 15 } = {}) {
  if (!monthsStr) return null; // fallback handled by caller
  const TOK = monthsStr.split(';').map(s => s.trim()).filter(Boolean); // e.g. ["NOV25","DEC25",...]
  if (!TOK.length) return null;

  // Map month code to number
  const M = { JAN:1,FEB:2,MAR:3,APR:4,MAY:5,JUN:6,JUL:7,AUG:8,SEP:9,OCT:10,NOV:11,DEC:12 };

  // Build candidates as { yyyymm, dteDelta }
  const now = new Date();
  const candidates = [];
  for (const t of TOK) {
    const mm3 = t.slice(0,3).toUpperCase();
    const yy2 = t.slice(3);
    const m = M[mm3]; if (!m) continue;
    const y = 2000 + (+yy2 || 0); // "25" -> 2025
    const firstOfMonth = new Date(Date.UTC(y, m - 1, 1));
    // crude DTE proxy (middle of month), good enough to pick a month bucket
    const midMonth = new Date(Date.UTC(y, m - 1, 15));
    const dte = Math.ceil((midMonth - now) / 86400000);
    candidates.push({ yyyymm: `${y}${String(m).padStart(2,'0')}`, delta: Math.abs(dte - targetDte) });
  }
  if (!candidates.length) return null;
  candidates.sort((a,b)=>a.delta-b.delta);
  return candidates[0].yyyymm;
}
/* --------------------------- Dynamic Conid Mapping ------------------------- */
const dynamicConidMap = new Map(); // conid -> {symbol, strike, right, expiry, discoveredAt}

// Track underlying mappings separately
const ulConidMap = new Map(); // ulConid -> symbol

// Update the mapping functions to broadcast
function updateConidMapping(conid, symbol, strike, right, expiry) {
  const mapping = {
    symbol,
    strike,
    right,
    expiry,
    discoveredAt: Date.now(),
    lastSeen: Date.now()
  };
  dynamicConidMap.set(conid, mapping);
  broadcastConidMapping(conid, mapping);
}

function updateULMapping(ulConid, symbol) {
  const mapping = {
    symbol,
    type: 'UNDERLYING',
    discoveredAt: Date.now(),
    lastSeen: Date.now()
  };
  ulConidMap.set(ulConid, mapping);
  broadcastConidMapping(ulConid, mapping);
}

function getSymbolFromConid(conid) {
  const mapping = dynamicConidMap.get(conid) || ulConidMap.get(conid);
  return mapping ? mapping.symbol : 'UNKNOWN';
}

function getOptionDetails(conid) {
  const mapping = dynamicConidMap.get(conid);
  if (mapping) {
    return {
      symbol: mapping.symbol,
      strike: mapping.strike,
      right: mapping.right,
      expiry: mapping.expiry,
      description: `${mapping.symbol} ${mapping.strike}${mapping.right}`
    };
  }
  
  const ulMapping = ulConidMap.get(conid);
  if (ulMapping) {
    return {
      symbol: ulMapping.symbol,
      type: 'UNDERLYING',
      description: `${ulMapping.symbol} Underlying`
    };
  }
  
  return { symbol: 'UNKNOWN', strike: 0, right: 'U', description: 'Unknown' };
}

async function buildFuturesOptionSelection(symbol, underlyingPx){
  const meta = FUTURES_SYMBOLS[symbol];
  const fut  = await getFrontFuture(symbol);
  if (!fut) return { ulConid:null, options:[] };

  // month discovery from /trsrv/futures
  let month;
  try {
    const root = symbol.replace('/','').toUpperCase(); // ES, NQ, ...
    const monthsData = await ibGet('/trsrv/futures', { symbols: root });
    month = pickMonthFromTrsrv(root, monthsData); // returns YYYYMM
  } catch { month = null; }
  if (!month) {
    const d = new Date(); month = `${d.getUTCFullYear()}${String(d.getUTCMonth()+1).padStart(2,'0')}`;
  }

  let info = [];
  try {
    // 🔁 IMPORTANT: your CP expects exchange=CME for secdef/info (even though market data is GLOBEX)
    info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype: 'FOP', month, exchange: 'CME' });
    if (!Array.isArray(info) || info.length === 0) {
      info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype: 'FOP', month }); // retry w/o exchange
    }
    if (!Array.isArray(info) || info.length === 0) {
      // try the next month once
      const y = +month.slice(0,4), m = +month.slice(4,6);
      const dt = new Date(Date.UTC(y, m-1, 1)); dt.setUTCMonth(dt.getUTCMonth()+1);
      const month2 = `${dt.getUTCFullYear()}${String(dt.getUTCMonth()+1).padStart(2,'0')}`;
      info = await ibGet('/iserver/secdef/info', { conid: fut.conid, sectype: 'FOP', month: month2, exchange: 'CME' });
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
    exchange: 'CME',
    symbol
  }));

  const coarse = norm.filter(c => c.strike > 0);
  const near   = coarse.filter(c => Math.abs((c.strike - underlyingPx)/Math.max(1,underlyingPx)) < 0.20);
  const base   = near.length >= 12 ? near : coarse;
  const picked = pickContractsAroundATM({ contracts: base, underlyingPx, targetCount: 25 });

  return { ulConid: fut.conid, options: picked };
}

// Add this function for manual conid lookup
async function getManualFuturesOptions(symbol, underlyingPx) {
  // These are example conids - you'll need to look up real ones from IBKR
  const manualConids = {
    '/ES': [
      // Example: ES Dec 2024 calls and puts around current price
      { conid: '123456789', right: 'C', strike: 6850, expiry: '20241220', exchange: 'CME' },
      { conid: '123456790', right: 'P', strike: 6850, expiry: '20241220', exchange: 'CME' },
    ],
    '/NQ': [
      { conid: '123456791', right: 'C', strike: 25500, expiry: '20241220', exchange: 'CME' },
      { conid: '123456792', right: 'P', strike: 25500, expiry: '20241220', exchange: 'CME' },
    ]
  };
  
  return manualConids[symbol] || [];
}
app.get('/debug/contracts/:symbol', async (req, res) => {
  try {
    const { symbol } = req.params;
    console.log(`[DEBUG] Searching contracts for: ${symbol}`);
    
    // Test different security types
    const types = ['STK', 'OPT', 'FUT', 'FOP'];
    const results = {};
    
    for (const type of types) {
      try {
        const data = await secdefSearch(symbol, type);
        results[type] = data || [];
        console.log(`[DEBUG] ${type} results:`, data?.length || 0);
        if (data && data.length > 0) {
          console.log(`[DEBUG] First ${type} contract:`, JSON.stringify(data[0], null, 2));
        }
      } catch (e) {
        results[type] = { error: e.message };
      }
    }
    
    res.json(results);
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});
async function buildEquityOptionSelection(symbol, underlyingPx) {
  const stkConid = await findStockConid(symbol);
  if (!stkConid) return { ulConid: null, options: [] };

  console.log(`[EQ] Building option selection for ${symbol}, UL price: ${underlyingPx}`);

  let raw = [];
  try {
    // First get all expiries
    raw = await secdefSearch(symbol, 'OPT');
    console.log(`[EQ] Found ${raw?.length || 0} total option contracts for ${symbol}`);
  } catch (e) {
    console.error(`[EQ SEARCH] ${symbol}:`, e.response?.data || e.message);
    return { ulConid: stkConid, options: [] };
  }

  // Filter and normalize contracts with proper strike prices
  const norm = (Array.isArray(raw) ? raw : [])
    .map(x => {
      // Extract strike price - IBKR requires this field
      let strike = 0;
      
      if (x.strike && !isNaN(x.strike)) {
        strike = parseFloat(x.strike);
      } else if (x.localSymbol) {
        // Parse from localSymbol format (common in IBKR)
        // Example: "SPY   250117C00500000" -> strike 500
        const match = x.localSymbol.match(/[CP](\d{8})$/);
        if (match) {
          strike = parseInt(match[1]) / 1000;
        }
      } else if (x.description) {
        // Parse from description: "SPY Jan 17 2025 500 Call"
        const match = x.description.match(/\s(\d+)\s(?:Call|Put)/i);
        if (match) {
          strike = parseInt(match[1]);
        }
      }

      return {
        conid: x.conid,
        right: (x.right === 'C' || /C\b/.test(x.localSymbol || '') || /CALL/i.test(x.description || '')) ? 'C' : 'P',
        strike: strike,
        expiry: x.maturityDate || x.lastTradingDay || '',
        exchange: x.exchange || 'SMART',
        symbol
      };
    })
    .filter(x => x.conid && x.strike > 0 && x.strike < underlyingPx * 3); // Reasonable strike filter

  console.log(`[EQ] Normalized ${norm.length} options with valid strikes for ${symbol}`);

  if (norm.length === 0) {
    console.log(`[EQ] No valid options found for ${symbol}, showing first 5 raw contracts:`, raw?.slice(0, 5));
    return { ulConid: stkConid, options: [] };
  }

  const forExpiry = chooseExpiryNear15DTE(norm, { target: 15, window: 10 });
  const picked = pickContractsAroundATM({
    contracts: forExpiry.length ? forExpiry : norm.slice(0, 50), // Limit for performance
    underlyingPx,
    targetCount: 25
  });

  console.log(`[EQ] Selected ${picked.length} options for ${symbol}`);
  return { ulConid: stkConid, options: picked };
}
async function captureUnderlying(ulConid) {
  const snap = await mdSnapshot([ulConid]);
  const row = snap?.[0] || {};
  
  // Try to auto-discover UL symbol if not mapped
  if (!ulConidMap.has(ulConid)) {
    // Try to infer from known futures
    for (const [symbol, meta] of Object.entries(FUTURES_SYMBOLS)) {
      const fut = await getFrontFuture(symbol);
      if (fut && fut.conid === ulConid) {
        updateULMapping(ulConid, symbol);
        break;
      }
    }
  }
  
  broadcastLiveUL(ulConid, row);
  return { price: px(row['31']), row };
}
// function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){
function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){  
  const last = px(optRow['31']);
  // const vol  = +optRow['87'] || 0;
  // const oi   = +optRow['84'] || 0; // adjust if your OI field differs
  const vol  = +optRow['7762'] || 0; // day volume
  const oi   = optionMeta.oi ?? null; // see OI note below  
  const bid  = px(optRow['84']);
  const ask  = px(optRow['86']);
  const greeks = calcGreeks(optRow);

  // storeHistoricalData(optionMeta.conid, oi, vol);
  if (oi != null) storeHistoricalData(optionMeta.conid, oi, vol);
  const hist = getHistoricalAverages(optionMeta.conid);

  const size = vol;
  const premium = last * size * multiplier;
  const aggressor = last >= ask ? true : (last <= bid ? false : (ask && bid ? (Math.abs(last-ask) < Math.abs(last-bid)) : true));
  const volOiRatio = oi > 0 ? (vol/oi) : vol;

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

  const direction  = classifyTradeUWStyle(trade, oi, vol, hist);
  const confidence = confidenceScore(trade, oi, vol, hist);
  const tags       = classifySizeTags(trade, isFuture);

  console.log(`[TRADE DEBUG] ${optionMeta.symbol} ${optionMeta.right} ${optionMeta.strike} | 
    UL: ${ul.price} | OPT: ${px(optRow['31'])} | 
    Bid: ${px(optRow['84'])} | Ask: ${px(optRow['86'])} | 
    Volume: ${+optRow['87'] || 0}`);
    
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

async function processOptionConid(optionMeta, isFuture, ulConid, multiplier) {
  try {
    const [optSnap, ul] = await Promise.all([
      mdSnapshot([optionMeta.conid]),
      captureUnderlying(ulConid)
    ]);
    
    const optRow = optSnap?.[0];
    if (!optRow) return;

    // 🚀 AUTO-DISCOVER: Update mappings
    updateConidMapping(
      optionMeta.conid,
      optionMeta.symbol,
      optionMeta.strike,
      optionMeta.right,
      optionMeta.expiry
    );
    
    updateULMapping(ulConid, optionMeta.symbol);

    optionToUL.set(optionMeta.conid, ulConid);
    ulForOption.set(optionMeta.conid, {
      isFuture,
      mult: multiplier,
      symbol: optionMeta.symbol
    });

    const { payload, optRow: rowForPrint } = buildTradePayload({
      optionMeta,
      isFuture,
      ulConid,
      ul,
      optRow,
      multiplier
    });

    if (payload && payload.premium >= 1000) {
      broadcastAll(payload);
    }

    maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);
    broadcastLiveOption(optionMeta.conid, optRow);

  } catch (error) {
    console.error(`[PROCESS OPTION] ${optionMeta.symbol} ${optionMeta.conid} error:`, error.message);
  }
}

async function loopFuturesSymbol(symbol) {
  try {
    console.log(`[FUT LOOP] Starting ${symbol}`);
    const fut = await getFrontFuture(symbol);
    if (!fut) {
      console.log(`[FUT LOOP] No futures contract found for ${symbol}`);
      return;
    }

    const ulSnap = await mdSnapshot([fut.conid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = px(ulRow['31']);
    broadcastLiveUL(fut.conid, ulRow);

    if (!ulPx || ulPx < 0) {
      console.log(`[FUT LOOP] ${symbol} no valid price, skipping`);
      return;
    }

    const { ulConid, options } = await buildFuturesOptionSelection(symbol, ulPx);
    console.log(`[FUT LOOP] ${symbol} processing ${options.length} options`);

    for (const meta of options) {
      try {
        await processOptionConid(meta, true, ulConid, FUTURES_SYMBOLS[symbol].multiplier);
        await sleep(120);
      } catch (optError) {
        console.error(`[FUT OPTION] ${symbol} conid ${meta.conid} error:`, optError.message);
        // Continue with next option instead of breaking the whole loop
      }
    }
  } catch (e) {
    console.error(`[FUT LOOP] ${symbol} error:`, e.message);
    // Don't rethrow - continue with other symbols
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

      // const meta = ulForOption.get(conid);
      // if (meta) {
      //   const optionMeta = { conid, symbol: meta.symbol, right: (row.right==='C'?'C':'P'), strike: +(row.strike||0), expiry: row.maturityDate||'' };
      //   maybeEmitPrint(optionMeta, row, meta.isFuture, meta.mult);
      // }
      const meta = ulForOption.get(conid);
      if (meta) {
        // meta already carries { isFuture, mult, symbol, right, strike, expiry, oi? }
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
// Clean up old mappings (expired contracts)
function cleanupOldMappings() {
  const now = Date.now();
  const thirtyDaysAgo = now - (30 * 24 * 60 * 60 * 1000);
  
  let cleaned = 0;
  for (const [conid, mapping] of dynamicConidMap.entries()) {
    if (mapping.lastSeen < thirtyDaysAgo) {
      dynamicConidMap.delete(conid);
      cleaned++;
    }
  }
  
  if (cleaned > 0) {
    console.log(`[MAPPING] Cleaned up ${cleaned} old conid mappings`);
  }
}

// Run cleanup every hour
setInterval(cleanupOldMappings, 60 * 60 * 1000);
app.get('/debug/conid-mapping', (req, res) => {
  const mappings = {};
  
  dynamicConidMap.forEach((value, key) => {
    mappings[key] = {
      ...value,
      discoveredAgo: Math.round((Date.now() - value.discoveredAt) / 1000) + 's ago'
    };
  });
  
  const ulMappings = {};
  ulConidMap.forEach((value, key) => {
    ulMappings[key] = {
      ...value,
      discoveredAgo: Math.round((Date.now() - value.discoveredAt) / 1000) + 's ago'
    };
  });
  
  res.json({
    option_mappings: mappings,
    underlying_mappings: ulMappings,
    stats: {
      total_options: dynamicConidMap.size,
      total_underlyings: ulConidMap.size,
      last_cleanup: new Date().toISOString()
    }
  });
});

app.get('/debug/auto-discover', async (req, res) => {
  try {
    console.log('[MAPPING] Starting auto-discovery for all symbols...');
    
    for (const symbol of ['/ES', '/NQ']) {
      try {
        const fut = await getFrontFuture(symbol);
        if (fut) {
          updateULMapping(fut.conid, symbol);
          
          const ulSnap = await mdSnapshot([fut.conid]);
          const ulPx = px(ulSnap?.[0]?.['31']);
          
          if (ulPx) {
            const { options } = await buildFuturesOptionSelection(symbol, ulPx);
            options.forEach(opt => {
              updateConidMapping(opt.conid, symbol, opt.strike, opt.right, opt.expiry);
            });
            console.log(`[MAPPING] Discovered ${options.length} options for ${symbol}`);
          }
        }
      } catch (e) {
        console.log(`[MAPPING] Failed for ${symbol}:`, e.message);
      }
    }
    
    res.json({ 
      message: 'Auto-discovery completed',
      discovered: {
        options: dynamicConidMap.size,
        underlyings: ulConidMap.size
      }
    });
    
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});
// After server starts, run initial discovery
setTimeout(async () => {
  console.log('[MAPPING] Running initial conid discovery...');
  try {
    // This will automatically populate mappings as options are processed
    console.log('[MAPPING] Mappings will be populated during normal processing');
  } catch (e) {
    console.error('[MAPPING] Initial discovery failed:', e.message);
  }
}, 5000);
/* ------------------------- WS + UI ------------------------------------ */
const DEFAULT_SUBS = { futures:['/ES','/NQ'], equities:['SPY','QQQ'] };

wss.on('connection', (ws)=>{
  clients.add(ws);
  ws._subs = { ...DEFAULT_SUBS };
  
  // 🚀 Send initial conid mappings
  const initialMappings = {};
  dynamicConidMap.forEach((value, key) => {
    initialMappings[key] = value;
  });
  ulConidMap.forEach((value, key) => {
    initialMappings[key] = value;
  });
  
  ws.send(JSON.stringify({
    type:'connected',
    message:'Connected to IBKR Flow (auto 25 ATM, ~15 DTE) with live quotes, prints & BTO/STO/BTC/STC',
    availableFutures: Object.keys(FUTURES_SYMBOLS),
    availableEquities: EQUITY_SYMBOLS,
    conidMappings: initialMappings // Send mappings
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
      else if (d.action === 'get_mappings') {
        // Send current mappings
        const currentMappings = {};
        dynamicConidMap.forEach((value, key) => {
          currentMappings[key] = value;
        });
        ulConidMap.forEach((value, key) => {
          currentMappings[key] = value;
        });
        ws.send(JSON.stringify({ type: 'CONID_MAPPINGS', mappings: currentMappings }));
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
.unknown{color:#ff5555}
</style></head>
<body>
<h2>🚀 IBKR Flow (Futures Only - /ES, /NQ)</h2>
<div>WS: ws://localhost:${PORT}/ws</div>
<hr/>
<div id="out"></div>
<script>
const out = document.getElementById('out');
const ws = new WebSocket('ws://'+location.host+'/ws');

// Dynamic conid mapping storage
let conidMappings = {};

ws.onopen = () => {
  ws.send(JSON.stringify({action:'subscribe',futuresSymbols:['/ES','/NQ'],equitySymbols:[]}));
  console.log('Connected to IBKR Flow');
};

// Dynamic conid mapping function
function getOptionDetails(conid) {
  return conidMappings[conid] || { symbol: 'UNKNOWN', strike: 0, right: 'U', description: 'Unknown' };
}

function rowTrade(d){
  const classes = (d.classifications||[]).map(x=>x.toLowerCase()).join(' ');
  const ac = d.assetClass==='FUTURES_OPTION'?'futures':'equity';
  const dir=(d.direction||'').toLowerCase();
  const hist=d.historicalComparison||{};
  const g=d.greeks||{delta:0};
  
  const details = getOptionDetails(d.conid);
  const symbolDisplay = details.symbol === 'UNKNOWN' ? '<span class="unknown">conid '+d.conid+'</span>' : details.symbol;
  const strikeDisplay = details.strike > 0 ? '$'+details.strike : '';
  const rightDisplay = details.right !== 'U' ? details.right : '';
  
  return '<div class="row '+classes+' '+ac+'" id="t-'+d.conid+'">'+
    '<div><span class="'+dir+'">'+d.direction+'</span> '+d.confidence+'% |'+
      '<b> '+symbolDisplay+' '+rightDisplay+' '+strikeDisplay+'</b> '+(d.expiry||'')+' |'+
      ' size '+d.size+' prem $'+(d.premium||0).toFixed(0)+' |'+
      ' vol/OI '+((d.volOiRatio||0)).toFixed(2)+'</div>'+
    '<div class="q" id="q-'+d.conid+'">'+
      'UL $'+(d.underlyingPrice||0).toFixed(2)+' | OPT $'+(d.optionPrice||0).toFixed(2)+
      ' | bid $'+(d.bid||0).toFixed(2)+' ask $'+(d.ask||0).toFixed(2)+' | Δ '+((g.delta||0)).toFixed(3)+
    '</div>'+
    '<div class="q">hist: avgOI '+(hist.avgOI||'-')+' | avgVol '+(hist.avgVolume||'-')+' | OIΔ '+(hist.oiChange||'-')+' | Vol× '+(hist.volumeMultiple||'-')+' | days '+(hist.dataPoints||0)+'</div>'+
  '</div>';
}

function rowPrint(p){
  const details = getOptionDetails(p.conid);
  const symbolDisplay = details.symbol === 'UNKNOWN' ? '<span class="unknown">conid '+p.conid+'</span>' : details.symbol;
  const strikeDisplay = details.strike > 0 ? '$'+details.strike : '';
  
  return '<div class="row print">'+
    'PRINT '+symbolDisplay+' '+p.right+' '+strikeDisplay+' '+(p.expiry||'')+' |'+
    ' size '+p.tradeSize+' @ $'+p.tradePrice.toFixed(2)+' prem $'+p.premium.toFixed(0)+' |'+
    ' vol/OI '+((p.volOiRatio||0)).toFixed(2)+' | '+(p.aggressor?'BUY-agg':'SELL-agg')+
  '</div>';
}

function updateQuote(d) {
  const el = document.getElementById('q-'+d.conid);
  if(!el) return;
  
  const details = getOptionDetails(d.conid);
  
  if(d.type==='LIVE_QUOTE'){
    let displayText;
    if (details.symbol === 'UNKNOWN') {
      displayText = '<span class="unknown">conid '+d.conid+'</span> | OPT $'+d.last.toFixed(2)+' | Δ '+d.delta.toFixed(3);
    } else {
      const rightDisplay = details.right === 'C' ? 'CALL' : (details.right === 'P' ? 'PUT' : '');
      displayText = details.symbol+' '+rightDisplay+' $'+details.strike+' | OPT $'+d.last.toFixed(2)+' | Δ '+d.delta.toFixed(3);
    }
    
    el.innerHTML = displayText+' | vol '+d.volume+' | '+new Date(d.timestamp).toLocaleTimeString();
    
  } else if(d.type==='UL_LIVE_QUOTE') {
    const ulDetails = getOptionDetails(d.conid);
    let symbolDisplay;
    if (ulDetails.symbol === 'UNKNOWN') {
      symbolDisplay = '<span class="unknown">conid '+d.conid+'</span>';
    } else {
      symbolDisplay = ulDetails.symbol + (ulDetails.type === 'UNDERLYING' ? ' UL' : '');
    }
    
    el.innerHTML = symbolDisplay+' | last $'+d.last.toFixed(2)+' | vol '+d.volume+' | '+new Date(d.timestamp).toLocaleTimeString();
  }
}

ws.onmessage=(e)=>{
  const d=JSON.parse(e.data);
  
  if(d.type==='connected' && d.conidMappings){
    // Store initial mappings from server
    conidMappings = { ...conidMappings, ...d.conidMappings };
    console.log('Loaded', Object.keys(d.conidMappings).length, 'conid mappings');
  }
  else if(d.type==='CONID_MAPPING'){
    // Update mapping when new conid is discovered
    conidMappings[d.conid] = d.mapping;
    console.log('Updated mapping for conid', d.conid, '->', d.mapping.symbol);
  }
  else if(d.type==='TRADE'){
    const div=document.createElement('div'); 
    div.innerHTML=rowTrade(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  }
  else if(d.type==='PRINT'){
    const div=document.createElement('div'); 
    div.innerHTML=rowPrint(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  }
  else if(d.type==='LIVE_QUOTE' || d.type==='UL_LIVE_QUOTE'){
    updateQuote(d);
  }
};

// Auto-refresh mappings every 30 seconds
setInterval(() => {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({action: 'get_mappings'}));
  }
}, 30000);
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
      // For this drop-in, just run the defaults every tick. (WS subs are wired, but
      // you can also merge them here if you want per-client aggregation.)
      const futs = ['/ES','/NQ'];
      const eqs  = ['SPY','QQQ'];

      for (const f of futs) await loopFuturesSymbol(f);
      // for (const s of eqs)  await loopEquitySymbol(s);
      await pollLiveQuotes();
      await sleep(1500);
    }
  }

  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();

