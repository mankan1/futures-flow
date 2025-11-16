/* eslint-disable no-console */
/**
 * IBKR Advanced Options Flow Server - COMPLETE VERSION
 * With Auto-Trading, Stance Analysis, and Full UI Support
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

if (!process.env.NODE_TLS_REJECT_UNAUTHORIZED) {
  process.env.NODE_TLS_REJECT_UNAUTHORIZED = '0';
  console.log('[SSL] Disabled certificate verification');
}

/* --------------------------- App Setup --------------------------------- */
const app = express();
app.use(compression());
app.use(cors());
app.use(morgan('tiny'));
app.use(express.json());

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
const FUTURES_SYMBOLS = {
  '/ES': { name: 'E-mini S&P 500', exchange: 'CME', multiplier: 50 },
  '/NQ': { name: 'E-mini NASDAQ-100', exchange: 'CME', multiplier: 20 }
};

const EQUITY_SYMBOLS = ['SPY','QQQ','AAPL','TSLA'];

const AUTO_TRADE_CONFIG = {
  enabled: process.env.AUTO_TRADE === 'true',
  paperTrade: process.env.PAPER_TRADE !== 'false',
  maxPositionSize: parseInt(process.env.MAX_POSITION_SIZE || '5'),
  minConfidenceScore: 75,
  minStanceScore: 40,
  signalWindow: 300000,
  minSignalsRequired: 3,
  profitTarget: 0.25,
  stopLoss: 0.40,
  maxDailyTrades: parseInt(process.env.MAX_DAILY_TRADES || '10'),
  symbols: ['SPY', 'QQQ']
};

/* --------------------------- State ------------------------------------- */
const historicalData = new Map();
const liveQuotes = new Map();
const optionToUL = new Map();
const prevVol = new Map();
const ulForOption = new Map();
const dynamicConidMap = new Map();
const ulConidMap = new Map();

const tradeSignals = new Map();
const activePositions = new Map();
const paperPositions = new Map();
const simulatedPositions = new Map();
const dailyTradeCount = { date: todayKey(), count: 0 };
const orderHistory = [];
let simulatedTradeIdCounter = 1;
let paperTradeIdCounter = 1;

/* --------------------------- Utils ------------------------------------- */
const sleep = (ms) => new Promise(r => setTimeout(r, ms));
const nowISO = () => new Date().toISOString();
function todayKey() { return new Date().toISOString().split('T')[0]; }

function px(v) {
  if (v == null) return 0;
  const n = parseFloat(String(v).replace(/[^\d\.\-\+]/g, ''));
  return isFinite(n) ? n : 0;
}

/* ========================= STANCE CALCULATION ========================== */

function calculateStanceScore(trade, greeks, hist) {
  let score = 0;
  const isCall = trade.type === 'CALL';
  const isPut = trade.type === 'PUT';
  const delta = greeks.delta || 0;
  
  // Direction weight
  if (trade.direction === 'BTO' && isCall) score += 30;
  if (trade.direction === 'BTO' && isPut) score -= 30;
  if (trade.direction === 'STO' && isCall) score -= 20;
  if (trade.direction === 'STO' && isPut) score += 20;
  
  // Delta weight
  if (Math.abs(delta) > 0.7) score += (isCall ? 15 : -15);
  if (Math.abs(delta) > 0.5 && Math.abs(delta) <= 0.7) score += (isCall ? 10 : -10);
  
  // Aggressor weight
  if (trade.aggressor && isCall) score += 10;
  if (trade.aggressor && isPut) score -= 10;
  if (!trade.aggressor && isCall) score -= 5;
  if (!trade.aggressor && isPut) score += 5;
  
  // Volume/OI weight
  if (trade.volOiRatio > 2) score += (isCall ? 10 : -10);
  if (trade.volOiRatio > 5) score += (isCall ? 15 : -15);
  
  // Premium size weight
  if (trade.premium > 100000) score += (isCall ? 5 : -5);
  if (trade.premium > 500000) score += (isCall ? 10 : -10);
  
  // Clamp between -100 and +100
  return Math.max(-100, Math.min(100, score));
}

function getStanceLabel(stanceScore) {
  if (stanceScore > 30) return 'BULL';
  if (stanceScore < -30) return 'BEAR';
  return 'NEUTRAL';
}

/* ========================= HISTORY & ANALYSIS ========================== */

function storeHistoricalData(conid, oi, volume) {
  const ts = Date.now();
  const arr = historicalData.get(conid) || [];
  arr.push({ date: todayKey(), oi: +oi || 0, volume: +volume || 0, ts });
  const cutoff = ts - 12 * 24 * 60 * 60 * 1000;
  historicalData.set(conid, arr.filter(x => x.ts >= cutoff));
}

function getHistoricalAverages(conid) {
  const arr = historicalData.get(conid) || [];
  if (!arr.length) return { avgOI: 0, avgVolume: 0, dataPoints: 0 };
  const totOI = arr.reduce((s, x) => s + (x.oi || 0), 0);
  const totV = arr.reduce((s, x) => s + (x.volume || 0), 0);
  return {
    avgOI: totOI / arr.length,
    avgVolume: totV / arr.length,
    dataPoints: arr.length
  };
}

function classifyTradeUWStyle(trade, oi, vol, hist) {
  const isAggBuy = !!trade.aggressor;
  if (trade.size > (oi + vol)) return isAggBuy ? 'BTO' : 'STO';
  const volRatio = hist.avgVolume > 0 ? (vol / hist.avgVolume) : 1;
  const oiChange = oi - (hist.avgOI || 0);
  const spike = volRatio >= 2;
  if (spike && oiChange > 0) return isAggBuy ? 'BTO' : 'STO';
  if (spike && oiChange <= 0) return isAggBuy ? 'BTC' : 'STC';
  if (oi > 0 && trade.size / oi > 0.4) return isAggBuy ? 'BTO' : 'STO';
  return isAggBuy ? 'BTC' : 'STC';
}

function confidenceScore(trade, oi, vol, hist) {
  let c = 50;
  const vr = hist.avgVolume > 0 ? (vol / hist.avgVolume) : 1;
  if (vr > 3) c += 20; else if (vr > 2) c += 10;
  if (oi > 0) {
    const r = trade.size / oi;
    if (r > 0.5) c += 20; else if (r > 0.25) c += 10;
  }
  if (trade.premium > 100000) c += 10;
  if (hist.dataPoints >= 5) c += 10;
  return Math.min(100, c);
}

function classifySizeTags(trade) {
  const out = [];
  if (trade.premium >= 50000 && trade.size >= 100 && trade.aggressor) out.push('SWEEP');
  if (trade.premium >= 100000 && trade.size >= 50) out.push('BLOCK');
  if (trade.premium >= 25000 && trade.size >= 25) out.push('NOTABLE');
  return out.length ? out : ['REGULAR'];
}

function calcGreeks(row) {
  return {
    delta: +row['7308'] || 0,
    gamma: +row['7309'] || 0,
    theta: +row['7310'] || 0,
    vega: +row['7311'] || 0,
    iv: +row['7283'] || 0
  };
}

/* ========================= BROADCAST =================================== */

function broadcastAll(o) {
  const s = JSON.stringify(o);
  for (const ws of clients) {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(s);
    }
  }
}

/* ========================= AUTO-TRADING ================================ */

function recordTradeSignal(trade) {
  if (!AUTO_TRADE_CONFIG.enabled) return;
  if (!AUTO_TRADE_CONFIG.symbols.includes(trade.symbol)) return;
  if (!trade.stanceScore || !trade.confidence) return;
  
  const signals = tradeSignals.get(trade.symbol) || [];
  
  signals.push({
    timestamp: Date.now(),
    stance: trade.stanceLabel,
    stanceScore: trade.stanceScore,
    confidence: trade.confidence,
    direction: trade.direction,
    premium: trade.premium,
    size: trade.size,
    volOiRatio: trade.volOiRatio,
    type: trade.type,
    classifications: trade.classifications,
    delta: trade.greeks?.delta || 0,
    underlyingPrice: trade.underlyingPrice
  });
  
  const cutoff = Date.now() - AUTO_TRADE_CONFIG.signalWindow;
  const recent = signals.filter(s => s.timestamp >= cutoff);
  tradeSignals.set(trade.symbol, recent);
  
  analyzeAndExecuteTrade(trade.symbol, recent);
}

function analyzeAndExecuteTrade(symbol, signals) {
  if (!AUTO_TRADE_CONFIG.enabled) return;
  if (signals.length < AUTO_TRADE_CONFIG.minSignalsRequired) return;
  
  if (dailyTradeCount.date !== todayKey()) {
    dailyTradeCount.date = todayKey();
    dailyTradeCount.count = 0;
  }
  if (dailyTradeCount.count >= AUTO_TRADE_CONFIG.maxDailyTrades) return;
  
  const hasPosition = Array.from(activePositions.values())
    .some(p => p.symbol === symbol && p.status === 'OPEN');
  const hasPaperPosition = Array.from(paperPositions.values())
    .some(p => p.symbol === symbol && p.status === 'OPEN');
  
  if (hasPosition || hasPaperPosition) return;
  
  // Analyze signals
  const analysis = {
    bullSignals: 0,
    bearSignals: 0,
    totalStanceScore: 0,
    avgConfidence: 0,
    totalPremium: 0,
    sweeps: 0,
    blocks: 0
  };
  
  signals.forEach(s => {
    if (s.stanceScore > 30) analysis.bullSignals++;
    if (s.stanceScore < -30) analysis.bearSignals++;
    analysis.totalStanceScore += s.stanceScore;
    analysis.avgConfidence += s.confidence;
    analysis.totalPremium += s.premium;
    
    if (s.classifications.includes('SWEEP')) analysis.sweeps++;
    if (s.classifications.includes('BLOCK')) analysis.blocks++;
  });
  
  analysis.avgConfidence /= signals.length;
  const avgStanceScore = analysis.totalStanceScore / signals.length;
  
  const totalDirectional = analysis.bullSignals + analysis.bearSignals;
  const bullRatio = analysis.bullSignals / totalDirectional;
  const bearRatio = analysis.bearSignals / totalDirectional;
  
  let tradeSide = null;
  if (bullRatio >= 0.70 && avgStanceScore > AUTO_TRADE_CONFIG.minStanceScore) {
    tradeSide = 'BULL';
  } else if (bearRatio >= 0.70 && avgStanceScore < -AUTO_TRADE_CONFIG.minStanceScore) {
    tradeSide = 'BEAR';
  }
  
  const shouldTrade = tradeSide && analysis.avgConfidence >= AUTO_TRADE_CONFIG.minConfidenceScore;
  
  console.log(`[AUTO-TRADE] ${symbol}: ${signals.length} signals, ${tradeSide || 'NO TRADE'}`);
  
  if (shouldTrade) {
    const tradeDetails = {
      symbol,
      side: tradeSide,
      avgStanceScore,
      confidence: analysis.avgConfidence,
      premium: analysis.totalPremium,
      signals: signals.length
    };
    
    executeAutoTrade(tradeDetails);
  }
}

async function executeAutoTrade(details) {
  console.log(`[AUTO-TRADE] 🎯 Executing ${details.side} trade on ${details.symbol}`);
  
  try {
    const paperId = `PAPER-${paperTradeIdCounter++}`;
    
    const position = {
      paperId,
      symbol: details.symbol,
      side: details.side,
      status: 'OPEN',
      openTime: Date.now(),
      entry: 100, // Placeholder - would get real price
      profitTarget: 125,
      stopLoss: 60,
      contracts: 3,
      current: 100
    };
    
    paperPositions.set(paperId, position);
    dailyTradeCount.count++;
    
    broadcastAll({
      type: 'AUTO_TRADE_EXECUTED',
      ...details,
      ...position,
      timestamp: Date.now()
    });
    
  } catch (error) {
    console.error('[AUTO-TRADE] Error:', error.message);
  }
}

async function monitorPositions() {
  if (!AUTO_TRADE_CONFIG.enabled) return;
  
  for (const [paperId, position] of paperPositions.entries()) {
    if (position.status !== 'OPEN') continue;
    
    try {
      // Simulate price movement
      const randomMove = (Math.random() - 0.5) * 5;
      position.current = Math.max(1, (position.current || position.entry) + randomMove);
      
      const pnl = (position.current - position.entry) / position.entry;
      const dollarPnl = (position.current - position.entry) * position.contracts * 100;
      
      position.dollarPnl = dollarPnl;
      
      let shouldExit = false;
      let exitReason = '';
      
      if (position.current >= position.profitTarget) {
        shouldExit = true;
        exitReason = 'PROFIT_TARGET';
      } else if (position.current <= position.stopLoss) {
        shouldExit = true;
        exitReason = 'STOP_LOSS';
      }
      
      if (shouldExit) {
        position.status = 'CLOSED';
        position.exitPrice = position.current;
        position.exitReason = exitReason;
        position.closeTime = Date.now();
        position.pnl = pnl;
        
        console.log(`[PAPER] Closed ${position.symbol} | P&L: ${(pnl * 100).toFixed(1)}%`);
        
        broadcastAll({
          type: 'PAPER_TRADE_CLOSED',
          paperId,
          symbol: position.symbol,
          pnl: (pnl * 100).toFixed(1) + '%',
          dollarPnl: dollarPnl.toFixed(0),
          reason: exitReason,
          timestamp: Date.now()
        });
      }
      
    } catch (error) {
      console.error(`[PAPER] Error monitoring ${position.symbol}:`, error.message);
    }
  }
}

/* ========================= IB API HELPERS ============================== */

async function primeIB() {
  try { await ax.get('/sso/validate'); } catch {}
  for (let i = 0; i < 20; i++) {
    try {
      const { data } = await ax.get('/iserver/auth/status');
      if (data?.authenticated && data?.connected) {
        console.log('[IB] authenticated & connected');
        return;
      }
    } catch (e) {
      console.log('[IB] status error:', e.message);
    }
    await sleep(1000);
  }
  throw new Error('IB not authenticated');
}

async function setMarketDataLive() {
  try {
    await ax.post('/iserver/marketdata/type', { marketDataType: 1 });
    console.log('[IB] market data set to LIVE');
  } catch (e) {
    console.error('[IB] could not set market data type:', e.message);
  }
}

async function ibGet(path, params) {
  const { data } = await ax.get(path, { params });
  return data;
}

async function mdSnapshot(conids) {
  const FIELDS = '31,84,85,86,87,88,7762,7308,7309,7310,7311,7283';
  return ibGet('/iserver/marketdata/snapshot', {
    conids: conids.join(','),
    fields: FIELDS,
    since: 0
  });
}

async function secdefSearch(symbol, secType) {
  return ibGet('/iserver/secdef/search', { symbol, secType });
}

async function findStockConid(symbol) {
  const data = await secdefSearch(symbol, 'STK');
  return data?.[0]?.conid;
}

/* ========================= PROCESSING ================================== */

async function processOptionConid(optionMeta, isFuture, ulConid, multiplier, ulPrice) {
  try {
    const optSnap = await mdSnapshot([optionMeta.conid]);
    const optRow = optSnap?.[0];
    if (!optRow) return;
    
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
    const aggressor = last >= ask ? true : (last <= bid ? false : true);
    const volOiRatio = oi > 0 ? (vol / oi) : vol;
    
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
      underlyingPrice: ulPrice,
      multiplier,
      exchange: optionMeta.exchange || 'SMART',
      timestamp: nowISO(),
      greeks,
      volOiRatio
    };
    
    const direction = classifyTradeUWStyle(trade, oi, vol, hist);
    const confidence = confidenceScore(trade, oi, vol, hist);
    const stanceScore = calculateStanceScore(trade, greeks, hist);
    const stanceLabel = getStanceLabel(stanceScore);
    const tags = classifySizeTags(trade);
    
    const payload = {
      type: 'TRADE',
      ...trade,
      direction,
      confidence,
      stanceScore,
      stanceLabel,
      classifications: tags,
      historicalComparison: {
        avgOI: Math.round(hist.avgOI),
        avgVolume: Math.round(hist.avgVolume),
        oiChange: Math.round(oi - (hist.avgOI || 0)),
        volumeMultiple: hist.avgVolume > 0 ? +(vol / hist.avgVolume).toFixed(2) : null,
        dataPoints: hist.dataPoints
      }
    };
    
    if (payload.premium >= 1000) {
      broadcastAll(payload);
      recordTradeSignal(payload);
    }
    
  } catch (error) {
    console.error(`[PROCESS] ${optionMeta.symbol} error:`, error.message);
  }
}

async function loopEquitySymbol(symbol) {
  try {
    const stkConid = await findStockConid(symbol);
    if (!stkConid) return;
    
    const ulSnap = await mdSnapshot([stkConid]);
    const ulPx = px(ulSnap?.[0]?.['31']);
    if (!ulPx || ulPx < 0) return;
    
    // Mock some option data for demo
    const mockOptions = [
      { conid: `${stkConid}1`, right: 'C', strike: ulPx + 5, expiry: '20251219', exchange: 'SMART', oi: 1000 },
      { conid: `${stkConid}2`, right: 'P', strike: ulPx - 5, expiry: '20251219', exchange: 'SMART', oi: 1200 }
    ];
    
    for (const meta of mockOptions) {
      await processOptionConid({ ...meta, symbol }, false, stkConid, 100, ulPx);
      await sleep(100);
    }
    
  } catch (e) {
    console.error('[EQ LOOP]', symbol, e.message);
  }
}

/* ========================= HTTP ROUTES ================================= */

app.get('/health', (req, res) => res.json({ ok: true, ts: Date.now() }));

app.get('/auto-trade/status', (req, res) => {
  const allPositions = [
    ...Array.from(activePositions.values()).map(p => ({ ...p, tradeType: 'LIVE' })),
    ...Array.from(paperPositions.values()).map(p => ({ ...p, tradeType: 'PAPER' })),
    ...Array.from(simulatedPositions.values()).map(p => ({ ...p, tradeType: 'MANUAL_SIM' }))
  ];
  
  res.json({
    enabled: AUTO_TRADE_CONFIG.enabled,
    paperTrade: AUTO_TRADE_CONFIG.paperTrade,
    config: AUTO_TRADE_CONFIG,
    positions: allPositions,
    dailyTrades: dailyTradeCount,
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
    ),
    stats: {
      paper: {
        open: Array.from(paperPositions.values()).filter(p => p.status === 'OPEN').length,
        closed: Array.from(paperPositions.values()).filter(p => p.status === 'CLOSED').length,
        totalPnL: Array.from(paperPositions.values())
          .filter(p => p.status === 'CLOSED')
          .reduce((sum, p) => sum + (p.dollarPnl || 0), 0)
      }
    }
  });
});

app.post('/auto-trade/enable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = true;
  console.log('[AUTO-TRADE] ✅ Enabled');
  res.json({ enabled: true });
});

app.post('/auto-trade/disable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = false;
  console.log('[AUTO-TRADE] ❌ Disabled');
  res.json({ enabled: false });
});

app.post('/auto-trade/simulate', async (req, res) => {
  try {
    const { symbol, side } = req.body;
    
    if (!symbol || !side) {
      return res.status(400).json({ error: 'Symbol and side required' });
    }
    
    const simId = `SIM-${simulatedTradeIdCounter++}`;
    const position = {
      simId,
      symbol,
      side,
      type: side === 'BULL' ? 'CALL' : 'PUT',
      strike: 500,
      expiry: '20251219',
      contracts: 3,
      entry: 100,
      current: 100,
      profitTarget: 125,
      stopLoss: 60,
      status: 'OPEN',
      openTime: Date.now(),
      isSimulated: true
    };
    
    simulatedPositions.set(simId, position);
    
    console.log(`[SIMULATED] ${side} trade on ${symbol}`);
    
    broadcastAll({
      type: 'SIMULATED_TRADE',
      ...position,
      timestamp: Date.now()
    });
    
    res.json({ success: true, position });
    
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

/* ========================= WEBSOCKET =================================== */

wss.on('connection', (ws) => {
  clients.add(ws);
  
  ws.send(JSON.stringify({
    type: 'connected',
    message: 'Connected to IBKR Flow Server',
    availableFutures: Object.keys(FUTURES_SYMBOLS),
    availableEquities: EQUITY_SYMBOLS
  }));
  
  ws.on('message', (m) => {
    try {
      const d = JSON.parse(m.toString());
      if (d.action === 'subscribe') {
        ws.send(JSON.stringify({
          type: 'subscribed',
          futures: d.futuresSymbols || [],
          equities: d.equitySymbols || []
        }));
      }
    } catch (e) {}
  });
  
  ws.on('close', () => clients.delete(ws));
});

/* ========================= MAIN LOOP =================================== */

(async () => {
  console.log(`🚀 Server starting on :${PORT}`);
  console.log(`📡 IBKR: ${IBKR_HOST}`);
  console.log(`🤖 Auto-Trade: ${AUTO_TRADE_CONFIG.enabled ? 'ENABLED' : 'DISABLED'}`);
  console.log(`📄 Paper Trade: ${AUTO_TRADE_CONFIG.paperTrade ? 'YES' : 'NO'}`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e.message);
  }
  
  server.listen(PORT, () => console.log(`✅ Server listening on :${PORT}`));
  
  async function coordinatorLoop() {
    while (true) {
      const eqs = ['SPY', 'QQQ'];
      
      for (const s of eqs) await loopEquitySymbol(s);
      await monitorPositions();
      await sleep(2000);
    }
  }
  
  coordinatorLoop().catch(e => console.error('[coordinator]', e.message));
})();
