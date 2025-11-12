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
 * IBKR_HOST=https://127.0.0.1:5000 PORT=3000 NODE_TLS_REJECT_UNAUTHORIZED=0 node index.js
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
  sweep: { minPremium: 50000, minContracts: 100 },
  block: { minPremium: 100000, minContracts: 50 },
  notable: { minPremium: 25000, minContracts: 25 },
  futuresSweep: { minPremium: 100000, minContracts: 50 },
  futuresBlock: { minPremium: 200000, minContracts: 25 },
  futuresNotable:{ minPremium: 50000, minContracts: 10 }
};

const FUTURES_SYMBOLS = {
  '/ES': { name: 'E-mini S&P 500', exchange: 'CME', multiplier: 50 },
  '/NQ': { name: 'E-mini NASDAQ-100', exchange: 'CME', multiplier: 20 },
  '/YM': { name: 'E-mini Dow', exchange: 'CBOT', multiplier: 5 },
  '/RTY': { name: 'E-mini Russell 2000', exchange: 'CME', multiplier: 50 },
  '/CL': { name: 'Crude Oil', exchange: 'NYMEX', multiplier: 1000 },
  '/GC': { name: 'Gold', exchange: 'COMEX', multiplier: 100 }
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA','NVDA','AMZN','MSFT','META','GOOGL'];

/* --------------------------- Auto-Trade Config ------------------------- */
const AUTO_TRADE_CONFIG = {
  enabled: process.env.AUTO_TRADE === 'true', // Set AUTO_TRADE=true to enable
  maxPositionSize: parseInt(process.env.MAX_POSITION_SIZE || '5'), // Max contracts per trade
  minConfidenceScore: 75, // Minimum confidence to consider
  minStanceScore: 40, // Minimum stance score (bull/bear conviction)
  signalWindow: 300000, // 5 minutes - time window to aggregate signals
  minSignalsRequired: 3, // Minimum signals pointing same direction
  riskPerTrade: 0.02, // 2% of account per trade
  accountBalance: parseFloat(process.env.ACCOUNT_BALANCE || '10000'),
  profitTarget: 0.25, // 25% profit target
  stopLoss: 0.40, // 40% stop loss
  maxDailyTrades: parseInt(process.env.MAX_DAILY_TRADES || '10'),
  symbols: ['SPY', 'QQQ'] // Only auto-trade these liquid symbols
};

/* --------------------------- Auto-Trade State -------------------------- */
const tradeSignals = new Map(); // symbol -> [{timestamp, stance, score, premium, ...}]
const activePositions = new Map(); // orderId -> {symbol, side, entry, target, stop, ...}
const dailyTradeCount = { date: todayKey(), count: 0 };
const orderHistory = []; // Track all orders

/* --------------------------- State ------------------------------------- */
const historicalData = new Map(); // conid -> [{date, oi, volume, ts}]
const liveQuotes = new Map(); // conid -> last quote cache
const optionToUL = new Map(); // optionConid -> underlyingConid
const prevVol = new Map(); // conid -> previous cumulative volume (for PRINT)
const ulForOption = new Map(); // option conid -> { isFuture, mult, symbol, right, strike, expiry, oi }
const dynamicConidMap = new Map(); // conid -> {symbol, strike, right, expiry, discoveredAt}
const ulConidMap = new Map(); // ulConid -> symbol

/* --------------------------- Utils ------------------------------------- */
const sleep = (ms)=>new Promise(r=>setTimeout(r,ms));
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
  const totV = arr.reduce((s,x)=>s+(x.volume||0),0);
  return {
    avgOI: totOI/arr.length,
    avgVolume: totV/arr.length,
    dataPoints: arr.length
  };
}

/* --------------------------- IB helpers -------------------------------- */
async function primeIB() {
  try { await ax.get('/sso/validate'); } catch {}
  for (let i = 0; i < 20; i++) {
    try {
      const { data } = await ax.get('/iserver/auth/status');
      if (data?.authenticated && data?.connected) {
        console.log('\\n\\n[IB] authenticated & connected\\n');
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

async function setMarketDataLive() {
  try {
    await ax.post('/iserver/marketdata/type', { marketDataType: 1 });
    console.log('[IB] market data type set to LIVE');
  } catch (e) {
    console.error('[IB] could not set market data type:', e.response?.status, e.response?.data || e.message);
  }
}

async function ibGet(path, params){
  const { data } = await ax.get(path, { params });
  return data;
}

async function secdefSearch(symbol, secType){
  return ibGet('/iserver/secdef/search', { symbol, secType });
}

async function findStockConid(symbol){
  const data = await secdefSearch(symbol,'STK');
  return data?.[0]?.conid;
}

async function mdSnapshot(conids){
  const FIELDS = '31,84,85,86,87,88,7762,7308,7309,7310,7311,7283';
  return ibGet('/iserver/marketdata/snapshot', {
    conids: conids.join(','),
    fields: FIELDS,
    since: 0
  });
}

/* ------------------------ Greeks / Classifiers ------------------------- */
function calcGreeks(row){
  return {
    delta: +row['7308']||0,
    gamma: +row['7309']||0,
    theta: +row['7310']||0,
    vega: +row['7311']||0,
    iv: +row['7283']||0
  };
}

function classifySizeTags(trade, isFuture){
  const t = isFuture
    ? { sweep: THRESHOLDS.futuresSweep, block: THRESHOLDS.futuresBlock, notable: THRESHOLDS.futuresNotable }
    : { sweep: THRESHOLDS.sweep, block: THRESHOLDS.block, notable: THRESHOLDS.notable };
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
function broadcastAll(o){
  const s = JSON.stringify(o);
  for (const ws of clients) {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(s);
    }
  }
}

function broadcastConidMapping(conid, mapping) {
  broadcastAll({ type: 'CONID_MAPPING', conid, mapping });
}

function broadcastLiveOption(conid, row){
  const msg = {
    type:'LIVE_QUOTE',
    conid,
    last:px(row['31']),
    bid:px(row['84']),
    ask:px(row['86']),
    volume:+row['7762']||0,
    delta:+row['7308']||0,
    timestamp: Date.now()
  };
  liveQuotes.set(conid, msg);
  broadcastAll(msg);
}

function broadcastLiveUL(conid, row){
  const msg = {
    type:'UL_LIVE_QUOTE',
    conid,
    last:px(row['31']),
    bid:px(row['84']),
    ask:px(row['86']),
    volume:+row['87']||0,
    timestamp: Date.now()
  };
  broadcastAll(msg);
}

/* --------------------------- Mapping ----------------------------------- */
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
    if (delta <= window && delta < bestDelta) {
      bestDelta = delta;
      bestExp = exp;
    }
  }
  if (!bestExp) {
    for (const [exp, arr] of byExp) {
      const d = dte(parseYYYYMMDD(exp));
      const delta = Math.abs(d - target);
      if (delta < bestDelta) {
        bestDelta = delta;
        bestExp = exp;
      }
    }
  }
  return bestExp ? byExp.get(bestExp) : [];
}

function pickContractsAroundATM({ contracts, underlyingPx, targetCount=25 }){
  const calls=[], puts=[];
  for (const c of contracts) {
    const isCall = c.right === 'C' || /C\\b/.test(c.right||'') || /C\\b/.test(c.localSymbol||'') || /C\\b/.test(c.description||'');
    const strike = +c.strike || 0;
    const rec = { ...c, isCall, strike, dist: Math.abs(strike - underlyingPx) };
    (isCall ? calls : puts).push(rec);
  }
  calls.sort((a,b)=>a.dist-b.dist);
  puts.sort((a,b)=>a.dist-b.dist);
  const out=[];
  let i=0;
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
  const volume = +row['7762'] || 0;
  const oi = optionMeta.oi ?? 0;
  
  if (!volume) return;
  
  const prevVolume = prevVol.get(conid) || 0;
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

/* --------------------- Futures helpers ------------------------ */
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
    if (score < bestScore) {
      bestScore=score;
      best=c;
    }
  }
  return best ? String(best.expirationDate).slice(0,6) : null;
}

async function getFrontFuture(symbol){
  const clean = symbol.replace('/','');
  const list = await secdefSearch(clean,'FUT');
  return list?.[0];
}

async function buildFuturesOptionSelection(symbol, underlyingPx){
  const meta = FUTURES_SYMBOLS[symbol];
  const fut = await getFrontFuture(symbol);
  if (!fut) return { ulConid:null, options:[] };
  
  let month;
  try {
    const root = symbol.replace('/','').toUpperCase();
    const monthsData = await ibGet('/trsrv/futures', { symbols: root });
    month = pickMonthFromTrsrv(root, monthsData);
  } catch { month = null; }
  
  if (!month) {
    const d = new Date();
    month = `${d.getUTCFullYear()}${String(d.getUTCMonth()+1).padStart(2,'0')}`;
  }
  
  let info = [];
  try {
    info = await ibGet('/iserver/secdef/info', {
      conid: fut.conid,
      sectype: 'FOP',
      month,
      exchange: 'CME'
    });
    if (!Array.isArray(info) || info.length === 0) {
      info = await ibGet('/iserver/secdef/info', {
        conid: fut.conid,
        sectype: 'FOP',
        month
      });
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
  const near = coarse.filter(c => Math.abs((c.strike - underlyingPx)/Math.max(1,underlyingPx)) < 0.20);
  const base = near.length >= 12 ? near : coarse;
  const picked = pickContractsAroundATM({ contracts: base, underlyingPx, targetCount: 25 });
  
  return { ulConid: fut.conid, options: picked };
}

/* ------------------------- Equity Builders --------------------------- */
async function buildEquityOptionSelection(symbol, underlyingPx) {
  const stkConid = await findStockConid(symbol);
  if (!stkConid) return { ulConid: null, options: [] };
  
  console.log(`[EQ] Building option selection for ${symbol}, UL price: ${underlyingPx}, Stock conid: ${stkConid}`);
  
  let allOptions = [];
  
  try {
    // Step 1: Get available expiries from search
    const searchResult = await secdefSearch(symbol, 'OPT');
    const optSection = searchResult?.[0]?.sections?.find(s => s.secType === 'OPT');
    const monthsStr = optSection?.months; // e.g., "NOV25;DEC25;JAN26;..."
    
    if (!monthsStr) {
      console.log(`[EQ] No option months found for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
    console.log(`[EQ] Available months for ${symbol}: ${monthsStr}`);
    
    // Step 2: Pick the expiry closest to 15 DTE
    const targetExpiry = pickEquityYYYYMMFromMonthsString(monthsStr, { targetDte: 15 });
    
    if (!targetExpiry) {
      console.log(`[EQ] Could not determine target expiry for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
    console.log(`[EQ] Target expiry for ${symbol}: ${targetExpiry} (YYYYMM)`);
    
    // Step 3: Get strikes using secdef/strikes
    const strikesData = await ibGet('/iserver/secdef/strikes', {
      conid: stkConid,
      sectype: 'OPT',
      month: targetExpiry
    });
    
    if (!strikesData || !strikesData.call || !strikesData.put) {
      console.log(`[EQ] No strikes data for ${symbol} month ${targetExpiry}`);
      return { ulConid: stkConid, options: [] };
    }
    
    const callStrikes = strikesData.call || [];
    const putStrikes = strikesData.put || [];
    
    console.log(`[EQ] Strikes for ${symbol}: ${callStrikes.length} calls, ${putStrikes.length} puts`);
    
    // Step 4: Filter strikes to ATM range (±20% from underlying)
    const minStrike = underlyingPx * 0.80;
    const maxStrike = underlyingPx * 1.20;
    
    const atmCallStrikes = callStrikes
      .filter(s => s >= minStrike && s <= maxStrike)
      .sort((a, b) => Math.abs(a - underlyingPx) - Math.abs(b - underlyingPx))
      .slice(0, 15); // Top 15 closest
    
    const atmPutStrikes = putStrikes
      .filter(s => s >= minStrike && s <= maxStrike)
      .sort((a, b) => Math.abs(a - underlyingPx) - Math.abs(b - underlyingPx))
      .slice(0, 15); // Top 15 closest
    
    console.log(`[EQ] ATM strikes: ${atmCallStrikes.length} calls, ${atmPutStrikes.length} puts`);
    
    // Step 5: Get conids for each strike using secdef/info
    const strikesToQuery = [
      ...atmCallStrikes.map(s => ({ strike: s, right: 'C' })),
      ...atmPutStrikes.map(s => ({ strike: s, right: 'P' }))
    ];
    
    for (const { strike, right } of strikesToQuery) {
      try {
        const info = await ibGet('/iserver/secdef/info', {
          conid: stkConid,
          sectype: 'OPT',
          month: targetExpiry,
          strike: strike.toString(),
          right: right
        });
        
        if (info && info[0] && info[0].conid) {
          allOptions.push({
            conid: info[0].conid,
            right: right,
            strike: parseFloat(strike),
            expiry: info[0].maturityDate || info[0].lastTradingDay || targetExpiry,
            exchange: info[0].exchange || 'SMART',
            symbol
          });
        }
        
        await sleep(50); // Rate limit
      } catch (e) {
        console.log(`[EQ] Failed to get conid for ${symbol} ${right} ${strike}:`, e.message);
      }
    }
    
    console.log(`[EQ] ✅ Found ${allOptions.length} option conids for ${symbol}`);
    
    if (allOptions.length === 0) {
      console.log(`[EQ] ❌ No valid options found for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
    // Step 6: Interleave calls and puts for balanced selection
    const picked = pickContractsAroundATM({
      contracts: allOptions,
      underlyingPx,
      targetCount: 25
    });
    
    console.log(`[EQ] ✅ Selected ${picked.length} options for ${symbol}`);
    return { ulConid: stkConid, options: picked };
    
  } catch (e) {
    console.error(`[EQ BUILD] ${symbol}:`, e.response?.data || e.message);
    return { ulConid: stkConid, options: [] };
  }
}

/* === helper: choose a YYYYMM for equities from the 'months' string === */
function pickEquityYYYYMMFromMonthsString(monthsStr, { targetDte = 15 } = {}) {
  if (!monthsStr) return null;
  const TOK = monthsStr.split(';').map(s => s.trim()).filter(Boolean);
  if (!TOK.length) return null;
  
  const M = { JAN:1,FEB:2,MAR:3,APR:4,MAY:5,JUN:6,JUL:7,AUG:8,SEP:9,OCT:10,NOV:11,DEC:12 };
  const now = new Date();
  const candidates = [];
  
  for (const t of TOK) {
    const mm3 = t.slice(0,3).toUpperCase();
    const yy2 = t.slice(3);
    const m = M[mm3];
    if (!m) continue;
    const y = 2000 + (+yy2 || 0);
    const midMonth = new Date(Date.UTC(y, m - 1, 15));
    const dte = Math.ceil((midMonth - now) / 86400000);
    candidates.push({
      yyyymm: `${y}${String(m).padStart(2,'0')}`,
      delta: Math.abs(dte - targetDte)
    });
  }
  
  if (!candidates.length) return null;
  candidates.sort((a,b)=>a.delta-b.delta);
  return candidates[0].yyyymm;
}

/* ------------------------- Core Processing --------------------------- */
async function captureUnderlying(ulConid) {
  const snap = await mdSnapshot([ulConid]);
  const row = snap?.[0] || {};
  
  if (!ulConidMap.has(ulConid)) {
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

function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){
  const last = px(optRow['31']);
  const vol = +optRow['7762'] || 0;
  const oi = optionMeta.oi ?? 0;
  const bid = px(optRow['84']);
  const ask = px(optRow['86']);
  const greeks = calcGreeks(optRow);
  
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
    bid,
    ask,
    size,
    openInterest: oi,
    premium,
    aggressor,
    underlyingConid: ulConid,
    underlyingPrice: ul.price,
    multiplier,
    exchange: optionMeta.exchange || (isFuture ? 'CME' : 'SMART'),
    timestamp: nowISO(),
    greeks,
    volOiRatio
  };
  
  const direction = classifyTradeUWStyle(trade, oi, vol, hist);
  const confidence = confidenceScore(trade, oi, vol, hist);
  const tags = classifySizeTags(trade, isFuture);
  
  return {
    payload: {
      type:'TRADE',
      ...trade,
      direction,
      confidence,
      classifications: tags,
      historicalComparison: {
        avgOI: Math.round(hist.avgOI),
        avgVolume: Math.round(hist.avgVolume),
        oiChange: Math.round(oi - (hist.avgOI||0)),
        volumeMultiple: hist.avgVolume>0 ? +(vol/hist.avgVolume).toFixed(2) : null,
        dataPoints: hist.dataPoints
      },
      marketSession: isFuture ? (isFuturesMarketOpen() ? 'OPEN' : 'CLOSED') : (isEquityMarketOpen() ? 'REGULAR/EXTENDED' : 'CLOSED')
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
      symbol: optionMeta.symbol,
      right: optionMeta.right,
      strike: optionMeta.strike,
      expiry: optionMeta.expiry,
      oi: optionMeta.oi ?? null
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
      
      // Record signal for auto-trading
      recordTradeSignal(payload);
    }
    
    maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);
    broadcastLiveOption(optionMeta.conid, optRow);
  } catch (error) {
    console.error(`[PROCESS OPTION] ${optionMeta.symbol} ${optionMeta.conid} error:`, error.message);
  }
}

async function loopFuturesSymbol(symbol) {
  try {
    const fut = await getFrontFuture(symbol);
    if (!fut) return;
    
    const ulSnap = await mdSnapshot([fut.conid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = px(ulRow['31']);
    broadcastLiveUL(fut.conid, ulRow);
    
    if (!ulPx || ulPx < 0) return;
    
    const { ulConid, options } = await buildFuturesOptionSelection(symbol, ulPx);
    
    for (const meta of options) {
      try {
        await processOptionConid(meta, true, ulConid, FUTURES_SYMBOLS[symbol].multiplier);
        await sleep(120);
      } catch (optError) {
        console.error(`[FUT OPTION] ${symbol} conid ${meta.conid} error:`, optError.message);
      }
    }
  } catch (e) {
    console.error(`[FUT LOOP] ${symbol} error:`, e.message);
  }
}

async function loopEquitySymbol(symbol){
  try{
    const stkConid = await findStockConid(symbol);
    if (!stkConid) return;
    
    const ulSnap = await mdSnapshot([stkConid]);
    const ulRow = ulSnap?.[0] || {};
    const ulPx = px(ulRow['31']);
    broadcastLiveUL(stkConid, ulRow);
    
    if (!ulPx || ulPx < 0) return;
    
    const { ulConid, options } = await buildEquityOptionSelection(symbol, ulPx);
    
    console.log(`[EQ LOOP] ${symbol} processing ${options.length} options`);
    
    for (const meta of options) {
      try {
        await processOptionConid(meta, false, ulConid, 100);
        await sleep(90);
      } catch (optError) {
        console.error(`[EQ OPTION] ${symbol} conid ${meta.conid} error:`, optError.message);
      }
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
        const optionMeta = {
          conid,
          symbol: meta.symbol,
          right: meta.right,
          strike: meta.strike,
          expiry: meta.expiry,
          oi: meta.oi ?? null
        };
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

setInterval(cleanupOldMappings, 60 * 60 * 1000);

/* ------------------------- HTTP Routes -------------------------------- */
app.get('/health', (req,res)=>res.json({ ok:true, ts:Date.now() }));

app.get('/auto-trade/status', (req, res) => {
  res.json({
    enabled: AUTO_TRADE_CONFIG.enabled,
    config: AUTO_TRADE_CONFIG,
    positions: Array.from(activePositions.values()),
    dailyTrades: dailyTradeCount,
    recentOrders: orderHistory.slice(-20),
    signals: Object.fromEntries(
      Array.from(tradeSignals.entries()).map(([symbol, signals]) => [
        symbol,
        {
          count: signals.length,
          bullish: signals.filter(s => s.stanceScore > 30).length,
          bearish: signals.filter(s => s.stanceScore < -30).length,
          avgStance: signals.reduce((sum, s) => sum + s.stanceScore, 0) / signals.length || 0
        }
      ])
    )
  });
});

app.post('/auto-trade/enable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = true;
  console.log('[AUTO-TRADE] ✅ Enabled');
  res.json({ enabled: true, message: 'Auto-trading enabled' });
});

app.post('/auto-trade/disable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = false;
  console.log('[AUTO-TRADE] ❌ Disabled');
  res.json({ enabled: false, message: 'Auto-trading disabled' });
});

app.post('/auto-trade/close-all', async (req, res) => {
  try {
    const closedPositions = [];
    
    for (const [orderId, position] of activePositions.entries()) {
      if (position.status === 'OPEN') {
        const optSnap = await mdSnapshot([position.optionConid]);
        const currentPrice = px(optSnap?.[0]?.['31']);
        
        if (currentPrice > 0) {
          await closePosition(orderId, position, currentPrice, 'MANUAL_CLOSE_ALL');
          closedPositions.push(position.symbol);
        }
      }
    }
    
    res.json({
      message: 'All positions closed',
      closed: closedPositions
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

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

app.get('/debug/equity-options/:symbol', async (req, res) => {
  try {
    const { symbol } = req.params;
    const stkConid = await findStockConid(symbol);
    
    if (!stkConid) {
      return res.json({ error: 'Stock not found', symbol });
    }
    
    // Get underlying price
    const ulSnap = await mdSnapshot([stkConid]);
    const ulPx = px(ulSnap?.[0]?.['31']);
    
    const results = {
      symbol,
      stkConid,
      underlyingPrice: ulPx,
      methods: {}
    };
    
    // Try Method 1: secdef/strikes
    try {
      const strikes = await ibGet('/iserver/secdef/strikes', {
        conid: stkConid,
        sectype: 'OPT',
        month: 'ALL'
      });
      results.methods.strikes = strikes;
    } catch (e) {
      results.methods.strikes = { error: e.message };
    }
    
    // Try Method 2: secdef/info
    try {
      const info = await ibGet('/iserver/secdef/info', {
        conid: stkConid,
        sectype: 'OPT',
        month: 'ALL'
      });
      results.methods.info = {
        count: info?.length || 0,
        sample: info?.slice(0, 3)
      };
    } catch (e) {
      results.methods.info = { error: e.message };
    }
    
    // Try Method 3: secdef/search
    try {
      const search = await secdefSearch(symbol, 'OPT');
      results.methods.search = {
        count: search?.length || 0,
        sample: search?.slice(0, 3)
      };
    } catch (e) {
      results.methods.search = { error: e.message };
    }
    
    res.json(results);
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.get('/debug/contracts/:symbol', async (req, res) => {
  try {
    const { symbol } = req.params;
    console.log(`[DEBUG] Searching contracts for: ${symbol}`);
    
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

/* ------------------------- WS + UI ------------------------------------ */
const DEFAULT_SUBS = {
  futures:['/ES','/NQ'],
  equities:['SPY','QQQ']
};

wss.on('connection', (ws)=>{
  clients.add(ws);
  ws._subs = { ...DEFAULT_SUBS };
  
  const initialMappings = {};
  dynamicConidMap.forEach((value, key) => {
    initialMappings[key] = value;
  });
  ulConidMap.forEach((value, key) => {
    initialMappings[key] = value;
  });
  
  ws.send(JSON.stringify({
    type:'connected',
    message:'Connected to IBKR Flow (Equities + Futures) - 25 ATM, ~15 DTE with live quotes, prints & BTO/STO/BTC/STC',
    availableFutures: Object.keys(FUTURES_SYMBOLS),
    availableEquities: EQUITY_SYMBOLS,
    conidMappings: initialMappings
  }));
  
  ws.on('message', (m)=>{
    try{
      const d = JSON.parse(m.toString());
      if (d.action === 'subscribe') {
        ws._subs = {
          futures: Array.isArray(d.futuresSymbols) ? d.futuresSymbols : DEFAULT_SUBS.futures,
          equities: Array.isArray(d.equitySymbols) ? d.equitySymbols : DEFAULT_SUBS.equities
        };
        ws.send(JSON.stringify({
          type:'subscribed',
          futures: ws._subs.futures,
          equities: ws._subs.equities
        }));
      } else if (d.action === 'get_mappings') {
        const currentMappings = {};
        dynamicConidMap.forEach((value, key) => {
          currentMappings[key] = value;
        });
        ulConidMap.forEach((value, key) => {
          currentMappings[key] = value;
        });
        ws.send(JSON.stringify({
          type: 'CONID_MAPPINGS',
          mappings: currentMappings
        }));
      }
    }catch(e){}
  });
  
  ws.on('close', ()=>clients.delete(ws));
});

app.get('/', (req,res)=>{
  res.setHeader('content-type','text/html; charset=utf-8');
  res.end(`<!doctype html>
<html><head><title>IBKR Flow + Auto-Trade</title>
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
.bull{color:#00ff00;font-weight:bold}
.bear{color:#ff3333;font-weight:bold}
.neutral{color:#ffff00}
.q{font-size:12px;color:#9a9a9a}
.print{font-size:12px;color:#0ff}
.unknown{color:#ff5555}
.auto-trade{border:2px solid #ffff00;background:#1a1a00}
.position{border:2px solid #00ffff;background:#001a1a;padding:8px;margin:5px 0}
.header{background:#1a1a1a;padding:10px;margin-bottom:10px;border:1px solid #333}
.btn{padding:5px 10px;margin:5px;cursor:pointer;background:#333;color:#0f0;border:1px solid #0f0}
.btn:hover{background:#0f0;color:#000}
</style></head>
<body>
<h2>🚀 IBKR Flow + Auto-Trade (Equities + Futures)</h2>
<div class="header">
  <div>WS: ws://localhost:${PORT}/ws | Auto-Trade: <span id="autoTradeStatus">...</span></div>
  <div>
    <button class="btn" onclick="toggleAutoTrade()">Toggle Auto-Trade</button>
    <button class="btn" onclick="closeAllPositions()">Close All Positions</button>
    <button class="btn" onclick="refreshStatus()">Refresh Status</button>
  </div>
  <div>Futures: /ES, /NQ | Equities: SPY, QQQ, AAPL, TSLA</div>
  <div id="positions"></div>
</div>
<hr/>
<div id="out"></div>
<script>
const out = document.getElementById('out');
const positionsDiv = document.getElementById('positions');
const ws = new WebSocket('ws://'+location.host+'/ws');

let conidMappings = {};
let autoTradeEnabled = false;

ws.onopen = () => {
  ws.send(JSON.stringify({
    action:'subscribe',
    futuresSymbols:['/ES','/NQ'],
    equitySymbols:['SPY','QQQ','AAPL','TSLA']
  }));
  console.log('Connected to IBKR Flow');
  refreshStatus();
};

async function refreshStatus() {
  const res = await fetch('/auto-trade/status');
  const data = await res.json();
  autoTradeEnabled = data.enabled;
  document.getElementById('autoTradeStatus').innerHTML = 
    data.enabled ? '<span style="color:#0f0">✅ ENABLED</span>' : '<span style="color:#f00">❌ DISABLED</span>';
  
  // Display positions
  if (data.positions && data.positions.length > 0) {
    positionsDiv.innerHTML = '<h3>Active Positions:</h3>' +
      data.positions.filter(p => p.status === 'OPEN').map(p => {
        const pnl = ((p.current - p.entry) / p.entry * 100).toFixed(1);
        const color = parseFloat(pnl) >= 0 ? '#0f0' : '#f00';
        return '<div class="position">' +
          '<strong>' + p.symbol + ' ' + p.type + ' 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + p.strike + '</strong> | ' +
          'Entry: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + p.entry.toFixed(2) + ' | Current: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + p.current.toFixed(2) + ' | ' +
          '<span style="color:' + color + '">P&L: ' + pnl + '%</span> | ' +
          'Target: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + p.profitTarget.toFixed(2) + ' | Stop: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + p.stopLoss.toFixed(2) +
          '</div>';
      }).join('');
  } else {
    positionsDiv.innerHTML = '<div>No active positions</div>';
  }
  
  // Display signals
  if (data.signals) {
    const signalsHtml = Object.entries(data.signals).map(([sym, sig]) => {
      const stanceColor = sig.avgStance > 30 ? '#0f0' : sig.avgStance < -30 ? '#f00' : '#ff0';
      return '<div style="display:inline-block;margin:5px;padding:5px;border:1px solid #333">' +
        '<strong>' + sym + '</strong>: ' + sig.count + ' signals | ' +
        '<span style="color:' + stanceColor + '">Stance: ' + sig.avgStance.toFixed(0) + '</span> | ' +
        '🟢' + sig.bullish + ' 🔴' + sig.bearish +
        '</div>';
    }).join('');
    
    if (!positionsDiv.innerHTML.includes('Signals:')) {
      positionsDiv.innerHTML += '<h3>Recent Signals (5min window):</h3>' + signalsHtml;
    }
  }
}

async function toggleAutoTrade() {
  const endpoint = autoTradeEnabled ? '/auto-trade/disable' : '/auto-trade/enable';
  await fetch(endpoint, { method: 'POST' });
  refreshStatus();
}

async function closeAllPositions() {
  if (!confirm('Close all open positions?')) return;
  await fetch('/auto-trade/close-all', { method: 'POST' });
  refreshStatus();
}

setInterval(refreshStatus, 5000); // Refresh every 5 seconds

function getOptionDetails(conid) {
  return conidMappings[conid] || {
    symbol: 'UNKNOWN',
    strike: 0,
    right: 'U',
    description: 'Unknown'
  };
}

function rowTrade(d){
  const classes = (d.classifications||[]).map(x=>x.toLowerCase()).join(' ');
  const ac = d.assetClass==='FUTURES_OPTION'?'futures':'equity';
  const dir=(d.direction||'').toLowerCase();
  const hist=d.historicalComparison||{};
  const g=d.greeks||{delta:0};
  const details = getOptionDetails(d.conid);
  const symbolDisplay = details.symbol === 'UNKNOWN' 
    ? '<span class="unknown">conid '+d.conid+'</span>' 
    : details.symbol;
  const strikeDisplay = details.strike > 0 ? '

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+details.strike : '';
  const rightDisplay = details.right !== 'U' ? details.right : '';
  
  // Stance display
  const stanceClass = d.stanceLabel === 'BULL' ? 'bull' : d.stanceLabel === 'BEAR' ? 'bear' : 'neutral';
  const stanceDisplay = d.stanceLabel ? 
    '<span class="' + stanceClass + '">' + d.stanceLabel + ' ' + d.stanceScore + '</span>' : '';
  
  return '<div class="row '+classes+' '+ac+'" id="t-'+d.conid+'">'+
    '<div><span class="'+dir+'">'+d.direction+'</span> '+d.confidence+'% | ' + stanceDisplay + ' | '+
    '<b> '+symbolDisplay+' '+rightDisplay+' '+strikeDisplay+'</b> '+(d.expiry||'')+' |'+
    ' size '+d.size+' prem 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+(d.premium||0).toFixed(0)+' |'+
    ' vol/OI '+((d.volOiRatio||0)).toFixed(2)+'</div>'+
    '<div class="q" id="q-'+d.conid+'">'+
    'UL 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+(d.underlyingPrice||0).toFixed(2)+' | OPT 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+(d.optionPrice||0).toFixed(2)+
    ' | bid 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+(d.bid||0).toFixed(2)+' ask 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+(d.ask||0).toFixed(2)+' | Δ '+((g.delta||0)).toFixed(3)+
    '</div>'+
    '<div class="q">hist: avgOI '+(hist.avgOI||'-')+' | avgVol '+(hist.avgVolume||'-')+
    ' | OIΔ '+(hist.oiChange||'-')+' | Vol× '+(hist.volumeMultiple||'-')+' | days '+(hist.dataPoints||0)+'</div>'+
    '</div>';
}

function rowPrint(p){
  const details = getOptionDetails(p.conid);
  const symbolDisplay = details.symbol === 'UNKNOWN' 
    ? '<span class="unknown">conid '+p.conid+'</span>' 
    : details.symbol;
  const strikeDisplay = details.strike > 0 ? '

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+details.strike : '';
  
  // Stance display for prints
  const stanceClass = p.stance === 'BULL' ? 'bull' : p.stance === 'BEAR' ? 'bear' : 'neutral';
  const stanceDisplay = p.stance ? 
    ' | <span class="' + stanceClass + '">' + p.stance + ' ' + p.stanceScore + '</span>' : '';
  
  return '<div class="row print">'+
    'PRINT '+symbolDisplay+' '+p.right+' '+strikeDisplay+' '+(p.expiry||'')+' |'+
    ' size '+p.tradeSize+' @ 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+p.tradePrice.toFixed(2)+' prem 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+p.premium.toFixed(0)+' |'+
    ' vol/OI '+((p.volOiRatio||0)).toFixed(2)+' | '+(p.aggressor?'BUY-agg':'SELL-agg')+
    stanceDisplay +
    '</div>';
}

function updateQuote(d) {
  const el = document.getElementById('q-'+d.conid);
  if(!el) return;
  const details = getOptionDetails(d.conid);
  
  if(d.type==='LIVE_QUOTE'){
    let displayText;
    if (details.symbol === 'UNKNOWN') {
      displayText = '<span class="unknown">conid '+d.conid+'</span> | OPT 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+d.last.toFixed(2)+' | Δ '+d.delta.toFixed(3);
    } else {
      const rightDisplay = details.right === 'C' ? 'CALL' : (details.right === 'P' ? 'PUT' : '');
      displayText = details.symbol+' '+rightDisplay+' 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+details.strike+' | OPT 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+d.last.toFixed(2)+' | Δ '+d.delta.toFixed(3);
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
    el.innerHTML = symbolDisplay+' | last 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();+d.last.toFixed(2)+' | vol '+d.volume+' | '+new Date(d.timestamp).toLocaleTimeString();
  }
}

ws.onmessage=(e)=>{
  const d=JSON.parse(e.data);
  
  if(d.type==='connected' && d.conidMappings){
    conidMappings = { ...conidMappings, ...d.conidMappings };
    console.log('Loaded', Object.keys(d.conidMappings).length, 'conid mappings');
  } else if(d.type==='CONID_MAPPING'){
    conidMappings[d.conid] = d.mapping;
  } else if(d.type==='TRADE'){
    const div=document.createElement('div');
    div.innerHTML=rowTrade(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  } else if(d.type==='PRINT'){
    const div=document.createElement('div');
    div.innerHTML=rowPrint(d);
    out.insertBefore(div.firstElementChild,out.firstChild);
    while(out.children.length>80) out.removeChild(out.lastChild);
  } else if(d.type==='LIVE_QUOTE' || d.type==='UL_LIVE_QUOTE'){
    updateQuote(d);
  } else if(d.type==='AUTO_TRADE_EXECUTED'){
    const div=document.createElement('div');
    div.innerHTML = '<div class="row auto-trade">'+
      '🎯 AUTO-TRADE EXECUTED: ' + d.side + ' ' + d.symbol + ' | ' +
      'Contracts: ' + d.contracts + ' @ 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + d.entry.toFixed(2) + ' | ' +
      'Target: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + d.profitTarget.toFixed(2) + ' | Stop: 

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + d.stopLoss.toFixed(2) +
      '<br/><small>Reasoning: ' + d.reasoning.join(', ') + '</small>' +
      '</div>';
    out.insertBefore(div.firstElementChild,out.firstChild);
    refreshStatus();
  } else if(d.type==='AUTO_TRADE_CLOSED'){
    const div=document.createElement('div');
    const pnlColor = parseFloat(d.pnl) >= 0 ? '#0f0' : '#f00';
    div.innerHTML = '<div class="row auto-trade">'+
      '🔄 POSITION CLOSED: ' + d.symbol + ' | ' +
      '<span style="color:' + pnlColor + '">P&L: ' + d.pnl + ' (

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})(); + d.dollarPnl + ')</span> | ' +
      'Reason: ' + d.reason +
      '</div>';
    out.insertBefore(div.firstElementChild,out.firstChild);
    refreshStatus();
  }
};

setInterval(() => {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({action: 'get_mappings'}));
  }
}, 30000);
</script>
</body></html>`);
});

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ'];
      const eqs = ['SPY','QQQ','AAPL','TSLA'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      // Monitor auto-trade positions
      await monitorPositions();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();
