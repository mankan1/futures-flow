/* eslint-disable no-console */
/**
 * IBKR Advanced Options Flow Server (Equities + Futures) with Auto-Trading
 * - Auto-picks ~15DTE expiry and ~25 ATM contracts (C+P interleaved)
 * - Captures UL & OPT price at "trade time"
 * - Streams live quotes (incl. delta) for options and underlying
 * - Classifies BTO/STO/BTC/STC (UW-style; OPEN if size > (OI+Vol))
 * - Tracks 12 days of OI/Vol history
 * - Emits TRADE + PRINT events; PRINT includes volume/OI ratio
 * - AUTO-TRADING: Places trades based on flow signals and market conditions
 * - SIMULATION: Paper trading mode with realistic P&L tracking
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

// Auto-trading configuration
const AUTO_TRADE_CONFIG = {
  enabled: process.env.AUTO_TRADE_ENABLED === 'true',
  simulation: process.env.AUTO_TRADE_SIMULATION !== 'false', // Default to simulation
  maxPositionSize: parseFloat(process.env.MAX_POSITION_SIZE || '5000'),
  maxDailyLoss: parseFloat(process.env.MAX_DAILY_LOSS || '2000'),
  maxOpenPositions: parseInt(process.env.MAX_OPEN_POSITIONS || '5'),
  minStanceScore: parseInt(process.env.MIN_STANCE_SCORE || '40'),
  maxDte: parseInt(process.env.MAX_DTE || '45'),
  minPremium: parseFloat(process.env.MIN_PREMIUM || '50000'),
  // Aggression levels based on flow signals
  aggressionMultipliers: {
    SWEEP: 1.5,
    BLOCK: 1.2,
    NOTABLE: 1.0,
    REGULAR: 0.5
  },
  // Position sizing based on signal strength
  tradeSizes: {
    small: parseFloat(process.env.SMALL_TRADE_SIZE || '1000'),
    medium: parseFloat(process.env.MEDIUM_TRADE_SIZE || '2500'),
    large: parseFloat(process.env.LARGE_TRADE_SIZE || '5000')
  },
  // Advanced flow aggregation settings
  flowAggregation: {
    timeWindow: 300000, // 5 minutes for flow aggregation
    minFlowCount: 3,    // Minimum flows to consider a trend
    bullishThreshold: 60, // Minimum average stance score for bullish
    bearishThreshold: -60 // Maximum average stance score for bearish
  }
};

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
/* ------------------------ Enhanced Historical Data Storage & Analysis ------------------------ */

// Enhanced historical data storage with full array of data points
const enhancedHistoricalData = new Map(); // conid -> { data: [], stats: {}, patterns: {} }

/* --------------------------- State ------------------------------------- */
const historicalData = new Map(); // conid -> [{date, oi, volume, ts}]
const liveQuotes = new Map(); // conid -> last quote cache
const optionToUL = new Map(); // optionConid -> underlyingConid
const prevVol = new Map(); // conid -> previous cumulative volume (for PRINT)
const ulForOption = new Map(); // option conid -> { isFuture, mult, symbol, right, strike, expiry, oi }
const dynamicConidMap = new Map(); // conid -> {symbol, strike, right, expiry, discoveredAt}
const ulConidMap = new Map(); // ulConid -> symbol

/* --------------------------- Auto-Trading State ------------------------ */
const activePositions = new Map(); // positionId -> position data
const tradingStats = {
  daily: {
    date: new Date().toISOString().split('T')[0],
    pnl: 0,
    trades: 0,
    wins: 0,
    losses: 0,
    openPositions: 0
  },
  totalTrades: 0,
  totalPnL: 0,
  simulation: AUTO_TRADE_CONFIG.simulation
};
const orderHistory = []; // Array of completed orders
const recentFlows = []; // Track recent flows for aggregation
const symbolFlowTrends = new Map(); // symbol -> {bullishFlows, bearishFlows, lastUpdated}

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

/**
 * Store comprehensive historical data with full data points
 */
function storeHistoricalData(conid, oi, volume, price = null, timestamp = Date.now()) {
    if (!enhancedHistoricalData.has(conid)) {
        enhancedHistoricalData.set(conid, {
            data: [],
            stats: {},
            patterns: {},
            lastUpdated: timestamp
        });
    }
    
    const historicalRecord = enhancedHistoricalData.get(conid);
    const dateKey = new Date(timestamp).toISOString().split('T')[0];
    
    // Check if we already have data for this date
    const existingIndex = historicalRecord.data.findIndex(item => 
        new Date(item.timestamp).toISOString().split('T')[0] === dateKey
    );
    
    const dataPoint = {
        date: dateKey,
        timestamp: timestamp,
        oi: +oi || 0,
        volume: +volume || 0,
        price: price || null,
        dateObj: new Date(timestamp)
    };
    
    if (existingIndex >= 0) {
        // Update existing day's data (use latest values)
        historicalRecord.data[existingIndex] = {
            ...historicalRecord.data[existingIndex],
            oi: +oi || historicalRecord.data[existingIndex].oi,
            volume: +volume || historicalRecord.data[existingIndex].volume,
            price: price || historicalRecord.data[existingIndex].price
        };
    } else {
        // Add new data point
        historicalRecord.data.push(dataPoint);
    }
    
    // Keep only last 30 days of data for performance
    const thirtyDaysAgo = timestamp - (30 * 24 * 60 * 60 * 1000);
    historicalRecord.data = historicalRecord.data.filter(item => item.timestamp >= thirtyDaysAgo);
    
    // Sort by timestamp (oldest first)
    historicalRecord.data.sort((a, b) => a.timestamp - b.timestamp);
    
    // Update statistics and patterns
    updateHistoricalStats(conid);
    analyzeHistoricalPatterns(conid);
    
    historicalRecord.lastUpdated = timestamp;
}

/**
 * Get enhanced historical statistics
 */
function getEnhancedHistoricalAverages(conid) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || !record.data.length) {
        return { 
            avgOI: 0, 
            avgVolume: 0, 
            dataPoints: 0,
            oiStdDev: 0,
            volumeStdDev: 0,
            maxOI: 0,
            maxVolume: 0,
            minOI: 0,
            minVolume: 0
        };
    }
    
    return record.stats;
}

/**
 * Analyze historical patterns for trading insights
 */
function analyzeHistoricalPatterns(conid) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || record.data.length < 5) return;
    
    const data = record.data;
    const patterns = {
        oiTrend: 'neutral',
        volumeTrend: 'neutral',
        accumulationDays: 0,
        distributionDays: 0,
        unusualActivityDays: 0,
        recentActivitySpike: false,
        supportResistanceLevels: [],
        volumeClusters: []
    };
    
    // Analyze OI and Volume trends
    patterns.oiTrend = analyzeTrend(data.map(d => d.oi));
    patterns.volumeTrend = analyzeTrend(data.map(d => d.volume));
    
    // Count accumulation/distribution days
    patterns.accumulationDays = countAccumulationDays(data);
    patterns.distributionDays = countDistributionDays(data);
    
    // Detect unusual activity
    patterns.unusualActivityDays = countUnusualActivityDays(data, record.stats);
    patterns.recentActivitySpike = detectRecentActivitySpike(data, record.stats);
    
    // Volume cluster analysis (where is most trading happening?)
    patterns.volumeClusters = analyzeVolumeClusters(data);
    
    record.patterns = patterns;
}

/**
 * Update comprehensive historical statistics
 */
function updateHistoricalStats(conid) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || !record.data.length) return;
    
    const data = record.data;
    const oiValues = data.map(d => d.oi).filter(oi => oi > 0);
    const volumeValues = data.map(d => d.volume).filter(vol => vol > 0);
    
    // Basic averages
    const avgOI = oiValues.length ? oiValues.reduce((a, b) => a + b, 0) / oiValues.length : 0;
    const avgVolume = volumeValues.length ? volumeValues.reduce((a, b) => a + b, 0) / volumeValues.length : 0;
    
    // Standard deviations
    const oiVariance = oiValues.length ? 
        oiValues.reduce((acc, val) => acc + Math.pow(val - avgOI, 2), 0) / oiValues.length : 0;
    const volumeVariance = volumeValues.length ? 
        volumeValues.reduce((acc, val) => acc + Math.pow(val - avgVolume, 2), 0) / volumeValues.length : 0;
    
    record.stats = {
        avgOI: Math.round(avgOI),
        avgVolume: Math.round(avgVolume),
        dataPoints: data.length,
        oiStdDev: Math.sqrt(oiVariance),
        volumeStdDev: Math.sqrt(volumeVariance),
        maxOI: oiValues.length ? Math.max(...oiValues) : 0,
        maxVolume: volumeValues.length ? Math.max(...volumeValues) : 0,
        minOI: oiValues.length ? Math.min(...oiValues) : 0,
        minVolume: volumeValues.length ? Math.min(...volumeValues) : 0,
        // Additional metrics traders care about
        oiRange: oiValues.length ? Math.max(...oiValues) - Math.min(...oiValues) : 0,
        volumeRange: volumeValues.length ? Math.max(...volumeValues) - Math.min(...volumeValues) : 0,
        oiVolatility: oiValues.length ? (Math.sqrt(oiVariance) / avgOI) * 100 : 0,
        volumeVolatility: volumeValues.length ? (Math.sqrt(volumeVariance) / avgVolume) * 100 : 0
    };
}

/**
 * Analyze trend direction from data series
 */
function analyzeTrend(dataSeries, lookbackPeriod = 5) {
    if (dataSeries.length < lookbackPeriod) return 'neutral';
    
    const recentData = dataSeries.slice(-lookbackPeriod);
    let increases = 0;
    let decreases = 0;
    
    for (let i = 1; i < recentData.length; i++) {
        if (recentData[i] > recentData[i-1]) increases++;
        else if (recentData[i] < recentData[i-1]) decreases++;
    }
    
    if (increases >= lookbackPeriod - 1) return 'strong_uptrend';
    if (decreases >= lookbackPeriod - 1) return 'strong_downtrend';
    if (increases > decreases * 2) return 'uptrend';
    if (decreases > increases * 2) return 'downtrend';
    return 'neutral';
}

/**
 * Count accumulation days (OI increasing with volume)
 */
function countAccumulationDays(data) {
    let count = 0;
    for (let i = 1; i < data.length; i++) {
        if (data[i].oi > data[i-1].oi && data[i].volume > data[i-1].volume * 0.8) {
            count++;
        }
    }
    return count;
}

/**
 * Count distribution days (OI decreasing with volume)
 */
function countDistributionDays(data) {
    let count = 0;
    for (let i = 1; i < data.length; i++) {
        if (data[i].oi < data[i-1].oi && data[i].volume > data[i-1].volume * 0.8) {
            count++;
        }
    }
    return count;
}

/**
 * Count days with unusual activity (volume > 2x average)
 */
function countUnusualActivityDays(data, stats) {
    if (!stats.avgVolume) return 0;
    return data.filter(day => day.volume > stats.avgVolume * 2).length;
}

/**
 * Detect recent activity spike (last 2 days > 3x average)
 */
function detectRecentActivitySpike(data, stats) {
    if (data.length < 2 || !stats.avgVolume) return false;
    const recentDays = data.slice(-2);
    return recentDays.some(day => day.volume > stats.avgVolume * 3);
}


/**
 * Analyze volume clusters (identify common trading levels)
 */
function analyzeVolumeClusters(data) {
    if (data.length < 5) return [];
    
    const volumes = data.map(d => d.volume).filter(v => v > 0);
    const avgVolume = volumes.reduce((a, b) => a + b, 0) / volumes.length;
    
    const clusters = [
        { range: 'Very High', min: avgVolume * 3, count: 0 },
        { range: 'High', min: avgVolume * 1.5, max: avgVolume * 3, count: 0 },
        { range: 'Normal', min: avgVolume * 0.5, max: avgVolume * 1.5, count: 0 },
        { range: 'Low', max: avgVolume * 0.5, count: 0 }
    ];
    
    volumes.forEach(volume => {
        for (const cluster of clusters) {
            const aboveMin = cluster.min === undefined || volume >= cluster.min;
            const belowMax = cluster.max === undefined || volume <= cluster.max;
            if (aboveMin && belowMax) {
                cluster.count++;
                break;
            }
        }
    });
    
    return clusters;
}

/**
 * Get recent historical data points (last N days)
 */
function getRecentHistoricalData(conid, days = 5) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || !record.data.length) return [];
    
    const cutoff = Date.now() - (days * 24 * 60 * 60 * 1000);
    return record.data.filter(item => item.timestamp >= cutoff);
}

/**
 * Get OI trend with multiple timeframes
 */
function getOITrendMultiTimeframe(conid) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || record.data.length < 3) return { short: 'neutral', medium: 'neutral', long: 'neutral' };
    
    const oiSeries = record.data.map(d => d.oi);
    
    return {
        short: analyzeTrend(oiSeries, 3),    // 3 days
        medium: analyzeTrend(oiSeries, 7),   // 1 week
        long: analyzeTrend(oiSeries, 14)     // 2 weeks
    };
}

/**
 * Calculate volume-weighted metrics
 */
function getVolumeWeightedMetrics(conid) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || !record.data.length) return null;
    
    const data = record.data;
    let totalVolume = 0;
    let volumeWeightedOI = 0;
    
    data.forEach(day => {
        totalVolume += day.volume;
        volumeWeightedOI += day.oi * day.volume;
    });
    
    return {
        volumeWeightedAvgOI: totalVolume > 0 ? volumeWeightedOI / totalVolume : 0,
        totalVolume: totalVolume,
        avgDailyVolume: totalVolume / data.length
    };
}

/* ------------------------ Enhanced Classification Functions ------------------------ */

/**
 * Comprehensive historical pattern analysis for trade classification
 */
function analyzeHistoricalPattern(conid, currentOi, currentVol, tradeSize) {
    const record = enhancedHistoricalData.get(conid);
    const stats = record?.stats || { avgVolume: 0, avgOI: 0 };
    const patterns = record?.patterns || {};
    
    const volumeSpike = currentVol > (stats.avgVolume * 2);
    const oiSpike = currentOi > (stats.avgOI * 1.5);
    const largeTradeRelativeToOi = currentOi > 0 ? (tradeSize / currentOi > 0.25) : false;
    
    // Get multi-timeframe OI trends
    const oiTrends = getOITrendMultiTimeframe(conid);
    
    // Check for recent OI buildup pattern
    const hasRecentOIBuildup = checkRecentOIBuildup(conid);
    
    // Check if this is consistent with recent patterns
    const consistentWithPattern = checkConsistencyWithPattern(conid, currentOi, currentVol, tradeSize);
    
    return {
        volumeSpike,
        oiSpike,
        largeTradeRelativeToOi,
        hasRecentOIBuildup,
        unusualActivity: currentVol > (stats.avgVolume * 5) || tradeSize > (stats.avgVolume * 10),
        oiTrendShort: oiTrends.short,
        oiTrendMedium: oiTrends.medium,
        consistentWithPattern,
        accumulationPattern: patterns.accumulationDays > patterns.distributionDays,
        distributionPattern: patterns.distributionDays > patterns.accumulationDays,
        recentActivitySpike: patterns.recentActivitySpike
    };
}

/**
 * Check for recent OI buildup (last 3-5 days)
 */
function checkRecentOIBuildup(conid) {
    const recentData = getRecentHistoricalData(conid, 5);
    if (recentData.length < 3) return false;
    
    let oiIncreases = 0;
    for (let i = 1; i < recentData.length; i++) {
        if (recentData[i].oi > recentData[i-1].oi) {
            oiIncreases++;
        }
    }
    
    return oiIncreases >= recentData.length - 1;
}

/**
 * Check if current activity is consistent with recent patterns
 */
function checkConsistencyWithPattern(conid, currentOi, currentVol, tradeSize) {
    const record = enhancedHistoricalData.get(conid);
    if (!record || record.data.length < 5) return true; // Default to consistent if not enough data
    
    const recentData = getRecentHistoricalData(conid, 5);
    const recentOIs = recentData.map(d => d.oi);
    const recentVolumes = recentData.map(d => d.volume);
    
    const avgRecentOI = recentOIs.reduce((a, b) => a + b, 0) / recentOIs.length;
    const avgRecentVolume = recentVolumes.reduce((a, b) => a + b, 0) / recentVolumes.length;
    
    // Check if current values are within 2 standard deviations of recent averages
    const oiStdDev = Math.sqrt(recentOIs.reduce((acc, oi) => acc + Math.pow(oi - avgRecentOI, 2), 0) / recentOIs.length);
    const volumeStdDev = Math.sqrt(recentVolumes.reduce((acc, vol) => acc + Math.pow(vol - avgRecentVolume, 2), 0) / recentVolumes.length);
    
    const oiConsistent = Math.abs(currentOi - avgRecentOI) <= (2 * oiStdDev);
    const volumeConsistent = Math.abs(currentVol - avgRecentVolume) <= (2 * volumeStdDev);
    
    return oiConsistent && volumeConsistent;
}


/**
 * Enhanced trader-classification logic
 */
function classifyTradeUWStyle(trade, currentOi, currentVol, hist) {
    const isAggBuy = !!trade.aggressor;
    
    // Get comprehensive historical context
    const historicalContext = analyzeHistoricalPattern(trade.conid, currentOi, currentVol, trade.size);
    
    // Rule 1: If trade size > (OI + current volume), it's definitely opening
    if (trade.size > (currentOi + currentVol)) {
        return isAggBuy ? 'BTO' : 'STO';
    }
    
    // Rule 2: Volume spike analysis with historical context
    const volumeSpike = historicalContext.volumeSpike;
    const oiIncrease = currentOi > (hist.avgOI * 1.2);
    
    // TRADER LOGIC: Multi-factor classification
    
    // SCENARIO 1: Strong accumulation pattern - OPENING
    if (volumeSpike && oiIncrease && historicalContext.accumulationPattern) {
        // High volume, OI increasing, in accumulation phase = new positions
        console.log(`[TRADE-CLASS] Accumulation pattern detected for ${trade.symbol}: BTO/STO`);
        return isAggBuy ? 'BTO' : 'STO';
    }
    
    // SCENARIO 2: Distribution pattern with volume spike - CLOSING
    if (volumeSpike && !oiIncrease && historicalContext.distributionPattern) {
        // High volume, OI not increasing, in distribution phase = closing positions
        console.log(`[TRADE-CLASS] Distribution pattern detected for ${trade.symbol}: BTC/STC`);
        return isAggBuy ? 'BTC' : 'STC';
    }
    
    // SCENARIO 3: Recent OI buildup followed by volume spike - PROFIT TAKING (CLOSING)
    if (volumeSpike && historicalContext.hasRecentOIBuildup && !oiIncrease) {
        // Built up positions now being liquidated
        console.log(`[TRADE-CLASS] Profit-taking detected for ${trade.symbol} after OI buildup: BTC/STC`);
        return isAggBuy ? 'BTC' : 'STC';
    }
    
    // SCENARIO 4: Volume spike with stable OI - POSITION ADJUSTMENTS (likely closing)
    if (volumeSpike && Math.abs(currentOi - hist.avgOI) / hist.avgOI < 0.1) {
        // Volume spike but OI unchanged = rolling positions (closing old, opening new)
        // More weight to closing since we're seeing the closing leg
        console.log(`[TRADE-CLASS] Position adjustment detected for ${trade.symbol}: BTC/STC`);
        return isAggBuy ? 'BTC' : 'STC';
    }
    
    // SCENARIO 5: Large trade relative to OI in uptrend - OPENING
    if (historicalContext.largeTradeRelativeToOi && historicalContext.oiTrendMedium === 'uptrend') {
        // Large trade during uptrend = new positions being opened
        console.log(`[TRADE-CLASS] Large opening trade detected in uptrend for ${trade.symbol}: BTO/STO`);
        return isAggBuy ? 'BTO' : 'STO';
    }
    
    // SCENARIO 6: Unusual activity inconsistent with pattern - likely OPENING
    if (historicalContext.unusualActivity && !historicalContext.consistentWithPattern) {
        // Break from normal pattern = likely new institutional activity
        console.log(`[TRADE-CLASS] Unusual activity break detected for ${trade.symbol}: BTO/STO`);
        return isAggBuy ? 'BTO' : 'STO';
    }
    
    // DEFAULT: Use trend-following logic
    if (historicalContext.oiTrendShort === 'uptrend') {
        return isAggBuy ? 'BTO' : 'STO';
    } else if (historicalContext.oiTrendShort === 'downtrend') {
        return isAggBuy ? 'BTC' : 'STC';
    }
    
    // Fallback to basic aggressor logic
    console.log(`[TRADE-CLASS] Using fallback classification for ${trade.symbol}`);
    return isAggBuy ? 'BTC' : 'STC';
}

/* ------------------------ History (12 days) ---------------------------- */
// function storeHistoricalData(conid, oi, volume){
//   const ts = Date.now();
//   const arr = historicalData.get(conid) || [];
//   arr.push({ date: todayKey(), oi:+oi||0, volume:+volume||0, ts });
//   const cutoff = ts - 12*24*60*60*1000;
//   historicalData.set(conid, arr.filter(x=>x.ts >= cutoff));
// }

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
  try { 
    await ax.get('/sso/validate'); 
  } catch (e) {
    console.log('[IB] SSO validate attempt:', e.message);
  }
  
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

// function classifyTradeUWStyle(trade, oi, vol, hist){
//   const isAggBuy = !!trade.aggressor;
//   if (trade.size > (oi + vol)) return isAggBuy ? 'BTO' : 'STO';
//   const volRatio = hist.avgVolume > 0 ? (vol / hist.avgVolume) : 1;
//   const oiChange = oi - (hist.avgOI || 0);
//   const spike = volRatio >= 2;
//   if (spike && oiChange > 0) return isAggBuy ? 'BTO' : 'STO';
//   if (spike && oiChange <= 0) return isAggBuy ? 'BTC' : 'STC';
//   if (oi > 0 && trade.size/oi > 0.4) return isAggBuy ? 'BTO' : 'STO';
//   return isAggBuy ? 'BTC' : 'STC';
// }

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
    const isCall = c.right === 'C' || /C\b/.test(c.right||'') || /C\b/.test(c.localSymbol||'') || /C\b/.test(c.description||'');
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
    
    const delta = +row['7308'] || null;

    let dteDays = null;
    if (optionMeta.expiry) {
      const expDate = parseYYYYMMDD(String(optionMeta.expiry));
      if (expDate) dteDays = Math.ceil((expDate - new Date())/86400000);
    }

    const stance = stanceForOptionPrint({
      right: optionMeta.right === 'C' ? 'CALL' : 'PUT',
      aggressor,
      direction: undefined,
      delta,
      moneyness: null,
      dte: dteDays,
      volOiRatio,
      size: tradeSize,
      premium
    });

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
      timestamp: Date.now(),
      stance: stance.label,
      stanceScore: stance.score,
      stanceNotes: stance.notes
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
    const searchResult = await secdefSearch(symbol, 'OPT');
    const optSection = searchResult?.[0]?.sections?.find(s => s.secType === 'OPT');
    const monthsStr = optSection?.months;
    
    if (!monthsStr) {
      console.log(`[EQ] No option months found for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
    const targetExpiry = pickEquityYYYYMMFromMonthsString(monthsStr, { targetDte: 15 });
    
    if (!targetExpiry) {
      console.log(`[EQ] Could not determine target expiry for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
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
    
    const minStrike = underlyingPx * 0.80;
    const maxStrike = underlyingPx * 1.20;
    
    const atmCallStrikes = callStrikes
      .filter(s => s >= minStrike && s <= maxStrike)
      .sort((a, b) => Math.abs(a - underlyingPx) - Math.abs(b - underlyingPx))
      .slice(0, 15);
    
    const atmPutStrikes = putStrikes
      .filter(s => s >= minStrike && s <= maxStrike)
      .sort((a, b) => Math.abs(a - underlyingPx) - Math.abs(b - underlyingPx))
      .slice(0, 15);
    
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
        
        await sleep(50);
      } catch (e) {
        console.log(`[EQ] Failed to get conid for ${symbol} ${right} ${strike}:`, e.message);
      }
    }
    
    console.log(`[EQ] ✅ Found ${allOptions.length} option conids for ${symbol}`);
    
    if (allOptions.length === 0) {
      console.log(`[EQ] ❌ No valid options found for ${symbol}`);
      return { ulConid: stkConid, options: [] };
    }
    
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

/* ===================== Bull/Bear Stance ===================== */
function stanceForOptionPrint({
  right, aggressor, direction, delta, moneyness, dte, volOiRatio, size, premium
}){
  const reasons = [];

  let base = 0;
  if (right === 'CALL') {
    base = aggressor ? +35 : -35;
    reasons.push(`${aggressor ? 'BUY' : 'SELL'}-agg CALL`);
  } else {
    base = aggressor ? -35 : +35;
    reasons.push(`${aggressor ? 'BUY' : 'SELL'}-agg PUT`);
  }

  const dirMap = { BTO: +10, STO: -10, BTC: +5, STC: -5 };
  const dirNudge = dirMap[direction] ?? 0;
  base += dirNudge;
  if (dirNudge) reasons.push(`dir:${direction}`);

  if (premium >= 1000000) { base *= 1.20; reasons.push('prem≥1M'); }
  else if (premium >= 100000) { base *= 1.10; reasons.push('prem≥100k'); }

  if (volOiRatio != null) {
    if (volOiRatio >= 5) { base *= 1.35; reasons.push('vol/OI≥5x'); }
    else if (volOiRatio >= 3) { base *= 1.25; reasons.push('vol/OI≥3x'); }
    else if (volOiRatio >= 1) { base *= 1.10; reasons.push('vol/OI≥1x'); }
  }

  if (Number.isFinite(dte)) {
    if (dte <= 3) { base *= 1.25; reasons.push('DTE≤3'); }
    else if (dte <= 7) { base *= 1.15; reasons.push('DTE≤7'); }
  }

  if (Number.isFinite(delta)) {
    const mag = Math.min(Math.abs(delta), 1);
    const weight = 0.9 + 0.3 * Math.exp(-Math.pow((mag - 0.5)/0.2, 2));
    base *= weight;
    reasons.push(`|Δ|≈${mag.toFixed(2)}`);
  }

  if (Number.isFinite(moneyness) && moneyness > 0) {
    const farOTMCall = right === 'CALL' && moneyness >= 1.15;
    const farOTMPut  = right === 'PUT'  && moneyness <= 0.85;
    if (farOTMCall || farOTMPut) {
      base *= 0.9;
      reasons.push('farOTM');
    }
  }

  if (size >= 500) { base *= 1.10; reasons.push('size≥500'); }
  else if (size >= 100) { base *= 1.05; reasons.push('size≥100'); }

  const score = Math.max(-100, Math.min(100, Math.round(base)));
  const label = score > 30 ? 'BULL' : score < -30 ? 'BEAR' : 'NEUTRAL';

  return { score, label, reasons };
}

/* ------------------------ Enhanced Trade Payload with Historical Insights ------------------------ */

function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }) {
    const last  = px(optRow['31']);
    const bid   = px(optRow['84']);
    const ask   = px(optRow['86']);
    const vol   = +optRow['7762'] || 0;
    const oi    = optionMeta.oi ?? 0;
    const greeks = calcGreeks(optRow);

    const size = vol;
    const premium = last * size * multiplier;
    const aggressor = last >= ask ? true
                   : last <= bid ? false
                   : (ask && bid ? (Math.abs(last - ask) < Math.abs(last - bid)) : true);
    const volOiRatio = oi > 0 ? (vol / oi) : vol;

    // Store enhanced historical data
    storeHistoricalData(optionMeta.conid, oi, vol, last);
    
    const hist = getEnhancedHistoricalAverages(optionMeta.conid);
    const historicalContext = analyzeHistoricalPattern(optionMeta.conid, oi, vol, size);
    const oiTrends = getOITrendMultiTimeframe(optionMeta.conid);
    const volumeMetrics = getVolumeWeightedMetrics(optionMeta.conid);
    
    const record = enhancedHistoricalData.get(optionMeta.conid);
    const patterns = record?.patterns || {};

    const type = optionMeta.right === 'C' ? 'CALL' : 'PUT';

    const trade = {
        symbol: optionMeta.symbol,
        assetClass: isFuture ? 'FUTURES_OPTION' : 'EQUITY_OPTION',
        conid: optionMeta.conid,
        type,
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

    const direction  = classifyTradeUWStyle(trade, oi, vol, hist);
    const confidence = confidenceScore(trade, oi, vol, hist);
    const tags       = classifySizeTags(trade, isFuture);

    const mny = (optionMeta.strike && ul.price) ? (optionMeta.strike / ul.price) : null;
    const dteDays = optionMeta.expiry
        ? Math.ceil((parseYYYYMMDD(String(optionMeta.expiry)) - new Date())/86400000)
        : null;

    const { score: stanceScore, label: stanceLabel, reasons: stanceReasons } = stanceForOptionPrint({
        right: type,
        aggressor,
        direction,
        delta: greeks?.delta ?? null,
        moneyness: mny,
        dte: dteDays,
        volOiRatio,
        size,
        premium
    });

    return {
        payload: {
            type: 'TRADE',
            ...trade,
            direction,
            confidence,
            classifications: tags,
            stanceScore,
            stanceLabel,
            stanceReasons,
            dte: dteDays,
            moneyness: mny,
            historicalAnalysis: {
                // Basic stats
                avgOI: Math.round(hist.avgOI),
                avgVolume: Math.round(hist.avgVolume),
                oiChange: Math.round(oi - (hist.avgOI||0)),
                oiChangePercent: hist.avgOI > 0 ? +((oi - hist.avgOI) / hist.avgOI * 100).toFixed(1) : 0,
                volumeMultiple: hist.avgVolume>0 ? +(vol/hist.avgVolume).toFixed(2) : null,
                dataPoints: hist.dataPoints,
                
                // Enhanced metrics
                oiStdDev: +(hist.oiStdDev || 0).toFixed(0),
                volumeStdDev: +(hist.volumeStdDev || 0).toFixed(0),
                oiVolatility: +(hist.oiVolatility || 0).toFixed(1),
                volumeVolatility: +(hist.volumeVolatility || 0).toFixed(1),
                
                // Trend analysis
                oiTrendShort: oiTrends.short,
                oiTrendMedium: oiTrends.medium,
                oiTrendLong: oiTrends.long,
                volumeTrend: patterns.volumeTrend,
                
                // Pattern recognition
                accumulationDays: patterns.accumulationDays || 0,
                distributionDays: patterns.distributionDays || 0,
                unusualActivityDays: patterns.unusualActivityDays || 0,
                recentActivitySpike: patterns.recentActivitySpike || false,
                hasRecentOIBuildup: historicalContext.hasRecentOIBuildup,
                
                // Volume analysis
                volumeWeightedAvgOI: volumeMetrics ? Math.round(volumeMetrics.volumeWeightedAvgOI) : 0,
                totalVolume: volumeMetrics ? Math.round(volumeMetrics.totalVolume) : 0,
                
                // Context flags
                volumeSpike: historicalContext.volumeSpike,
                oiSpike: historicalContext.oiSpike,
                unusualActivity: historicalContext.unusualActivity,
                consistentWithPattern: historicalContext.consistentWithPattern
            },
            marketSession: isFuture
                ? (isFuturesMarketOpen() ? 'OPEN' : 'CLOSED')
                : (isEquityMarketOpen() ? 'REGULAR/EXTENDED' : 'CLOSED')
        },
        optRow
    };
}

/* ------------------------ Debug Endpoints for Historical Analysis ------------------------ */

app.get('/debug/historical/:conid', (req, res) => {
    const { conid } = req.params;
    const record = enhancedHistoricalData.get(parseInt(conid));
    
    if (!record) {
        return res.json({ error: 'No historical data found for conid', conid });
    }
    
    res.json({
        conid: parseInt(conid),
        dataPoints: record.data.length,
        lastUpdated: record.lastUpdated,
        stats: record.stats,
        patterns: record.patterns,
        recentData: record.data.slice(-10), // Last 10 data points
        oiTrends: getOITrendMultiTimeframe(parseInt(conid)),
        volumeMetrics: getVolumeWeightedMetrics(parseInt(conid))
    });
});

app.get('/debug/historical-stats', (req, res) => {
    const stats = {};
    enhancedHistoricalData.forEach((record, conid) => {
        stats[conid] = {
            dataPoints: record.data.length,
            lastUpdated: record.lastUpdated,
            patterns: record.patterns
        };
    });
    
    res.json({
        totalContracts: enhancedHistoricalData.size,
        stats: stats
    });
});

// /* ===================== Trade Payload Builder ===================== */
// function buildTradePayload({ optionMeta, isFuture, ulConid, ul, optRow, multiplier }){
//   const last  = px(optRow['31']);
//   const bid   = px(optRow['84']);
//   const ask   = px(optRow['86']);
//   const vol   = +optRow['7762'] || 0;
//   const oi    = optionMeta.oi ?? 0;
//   const greeks = calcGreeks(optRow);

//   const size = vol;
//   const premium = last * size * multiplier;
//   const aggressor = last >= ask ? true
//                    : last <= bid ? false
//                    : (ask && bid ? (Math.abs(last - ask) < Math.abs(last - bid)) : true);
//   const volOiRatio = oi > 0 ? (vol / oi) : vol;

//   if (oi != null) storeHistoricalData(optionMeta.conid, oi, vol);
//   const hist = getHistoricalAverages(optionMeta.conid);

//   const type = optionMeta.right === 'C' ? 'CALL' : 'PUT';

//   const trade = {
//     symbol: optionMeta.symbol,
//     assetClass: isFuture ? 'FUTURES_OPTION' : 'EQUITY_OPTION',
//     conid: optionMeta.conid,
//     type,
//     strike: optionMeta.strike,
//     expiry: optionMeta.expiry,
//     optionPrice: last,
//     bid,
//     ask,
//     size,
//     openInterest: oi,
//     premium,
//     aggressor,
//     underlyingConid: ulConid,
//     underlyingPrice: ul.price,
//     multiplier,
//     exchange: optionMeta.exchange || (isFuture ? 'CME' : 'SMART'),
//     timestamp: nowISO(),
//     greeks,
//     volOiRatio
//   };

//   const direction  = classifyTradeUWStyle(trade, oi, vol, hist);
//   const confidence = confidenceScore(trade, oi, vol, hist);
//   const tags       = classifySizeTags(trade, isFuture);

//   const mny = (optionMeta.strike && ul.price) ? (optionMeta.strike / ul.price) : null;
//   const dteDays = optionMeta.expiry
//     ? Math.ceil((parseYYYYMMDD(String(optionMeta.expiry)) - new Date())/86400000)
//     : null;

//   const { score: stanceScore, label: stanceLabel, reasons: stanceReasons } = stanceForOptionPrint({
//     right: type,
//     aggressor,
//     direction,
//     delta: greeks?.delta ?? null,
//     moneyness: mny,
//     dte: dteDays,
//     volOiRatio,
//     size,
//     premium
//   });

//   return {
//     payload: {
//       type: 'TRADE',
//       ...trade,
//       direction,
//       confidence,
//       classifications: tags,
//       stanceScore,
//       stanceLabel,
//       stanceReasons,
//       dte: dteDays,
//       moneyness: mny,
//       historicalComparison: {
//         avgOI: Math.round(hist.avgOI),
//         avgVolume: Math.round(hist.avgVolume),
//         oiChange: Math.round(oi - (hist.avgOI||0)),
//         volumeMultiple: hist.avgVolume>0 ? +(vol/hist.avgVolume).toFixed(2) : null,
//         dataPoints: hist.dataPoints
//       },
//       marketSession: isFuture
//         ? (isFuturesMarketOpen() ? 'OPEN' : 'CLOSED')
//         : (isEquityMarketOpen() ? 'REGULAR/EXTENDED' : 'CLOSED')
//     },
//     optRow
//   };
// }

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
      
      // Track flow for aggregation and auto-trading
      trackFlowForAggregation(payload);
      
      // AUTO-TRADE: Check if we should trade based on this signal
      if (AUTO_TRADE_CONFIG.enabled && 
          payload.stanceScore >= AUTO_TRADE_CONFIG.minStanceScore &&
          payload.premium >= AUTO_TRADE_CONFIG.minPremium) {
        
        // Add small random delay to avoid trading on every single signal
        const randomDelay = Math.random() * 2000 + 1000; // 1-3 seconds
        setTimeout(() => {
          executeAutoTrade(payload).catch(error => {
            console.error('[AUTO-TRADE] Execution error:', error.message);
          });
        }, randomDelay);
      }
    }
    
    maybeEmitPrint(optionMeta, rowForPrint, isFuture, multiplier);
    broadcastLiveOption(optionMeta.conid, optRow);
  } catch (error) {
    console.error(`[PROCESS OPTION] ${optionMeta.symbol} ${optionMeta.conid} error:`, error.message);
  }
}

/* ------------------------ Auto-Trading Functions ----------------------- */

/**
 * Track recent flows for trend analysis
 */
function trackFlowForAggregation(flow) {
  const flowRecord = {
    ...flow,
    timestamp: Date.now(),
    weight: calculateFlowWeight(flow)
  };
  
  recentFlows.push(flowRecord);
  
  // Remove flows older than aggregation window
  const cutoff = Date.now() - AUTO_TRADE_CONFIG.flowAggregation.timeWindow;
  while (recentFlows.length > 0 && recentFlows[0].timestamp < cutoff) {
    recentFlows.shift();
  }
  
  // Update symbol trends
  updateSymbolTrend(flow.symbol, flow.stanceScore, flow.weight);
}

/**
 * Calculate weight for flow based on multiple factors
 */
function calculateFlowWeight(flow) {
  let weight = 1.0;
  
  // Premium size weighting
  if (flow.premium >= 1000000) weight *= 2.0;
  else if (flow.premium >= 100000) weight *= 1.5;
  
  // Volume/OI ratio weighting
  if (flow.volOiRatio >= 5) weight *= 1.8;
  else if (flow.volOiRatio >= 3) weight *= 1.3;
  
  // Classification weighting
  if (flow.classifications.includes('SWEEP')) weight *= 2.0;
  else if (flow.classifications.includes('BLOCK')) weight *= 1.5;
  else if (flow.classifications.includes('NOTABLE')) weight *= 1.2;
  
  // Confidence weighting
  weight *= (flow.confidence / 100);
  
  return Math.min(weight, 5.0); // Cap at 5x
}

/**
 * Update symbol trend analysis
 */
function updateSymbolTrend(symbol, stanceScore, weight) {
  if (!symbolFlowTrends.has(symbol)) {
    symbolFlowTrends.set(symbol, {
      bullishFlows: 0,
      bearishFlows: 0,
      totalWeight: 0,
      avgStanceScore: 0,
      lastUpdated: Date.now(),
      flowCount: 0
    });
  }
  
  const trend = symbolFlowTrends.get(symbol);
  trend.flowCount++;
  trend.totalWeight += weight;
  
  if (stanceScore > 0) {
    trend.bullishFlows += weight;
  } else {
    trend.bearishFlows += weight;
  }
  
  // Update average stance score (weighted)
  trend.avgStanceScore = 
    ((trend.avgStanceScore * (trend.flowCount - 1)) + (stanceScore * weight)) / trend.flowCount;
  
  trend.lastUpdated = Date.now();
}

/**
 * Get current market trend for a symbol
 */
function getMarketTrend(symbol) {
  const trend = symbolFlowTrends.get(symbol);
  if (!trend || trend.flowCount < AUTO_TRADE_CONFIG.flowAggregation.minFlowCount) {
    return 'NEUTRAL';
  }
  
  const bullishRatio = trend.bullishFlows / trend.totalWeight;
  const bearishRatio = trend.bearishFlows / trend.totalWeight;
  
  if (trend.avgStanceScore >= AUTO_TRADE_CONFIG.flowAggregation.bullishThreshold && 
      bullishRatio > 0.6) {
    return 'BULLISH';
  } else if (trend.avgStanceScore <= AUTO_TRADE_CONFIG.flowAggregation.bearishThreshold && 
             bearishRatio > 0.6) {
    return 'BEARISH';
  }
  
  return 'NEUTRAL';
}

/**
 * Calculate position size based on multiple factors
 */
function calculatePositionSize(tradeSignal, availableCapital, marketTrend) {
  if (!AUTO_TRADE_CONFIG.enabled) return 0;
  
  const {
    stanceScore,
    premium,
    classifications,
    confidence,
    volOiRatio,
    size
  } = tradeSignal;

  // Base size on stance score and confidence
  let baseSize = AUTO_TRADE_CONFIG.tradeSizes.small;
  
  if (stanceScore >= 70 && confidence >= 80) {
    baseSize = AUTO_TRADE_CONFIG.tradeSizes.large;
  } else if (stanceScore >= 50 && confidence >= 70) {
    baseSize = AUTO_TRADE_CONFIG.tradeSizes.medium;
  }

  // Apply aggression multiplier based on trade classification
  const aggression = classifications.reduce((max, classification) => {
    return Math.max(max, AUTO_TRADE_CONFIG.aggressionMultipliers[classification] || 1.0);
  }, 1.0);

  // Adjust for volume/OI ratio (higher ratio = more conviction)
  const volMultiplier = Math.min(volOiRatio / 3, 2.0);

  // Market trend alignment bonus
  const trendMultiplier = (marketTrend === (tradeSignal.stanceLabel === 'BULL' ? 'BULLISH' : 'BEARISH')) ? 1.3 : 1.0;

  // Size-based adjustment
  const sizeMultiplier = Math.min(size / 100, 2.0);

  let positionSize = baseSize * aggression * volMultiplier * trendMultiplier * sizeMultiplier;
  
  // Cap at max position size and available capital
  positionSize = Math.min(
    positionSize,
    AUTO_TRADE_CONFIG.maxPositionSize,
    availableCapital * 0.1 // Never risk more than 10% of available capital
  );

  return Math.max(100, positionSize); // Minimum $100 position
}

/**
 * Enhanced trade decision logic
 */
function shouldEnterTrade(tradeSignal, currentPositions, marketTrend) {
  if (!AUTO_TRADE_CONFIG.enabled) return false;

  const {
    stanceScore,
    stanceLabel,
    premium,
    dte,
    confidence,
    symbol,
    direction,
    classifications,
    greeks,
    volOiRatio
  } = tradeSignal;

  // Basic filters
  if (stanceScore < AUTO_TRADE_CONFIG.minStanceScore) return false;
  if (premium < AUTO_TRADE_CONFIG.minPremium) return false;
  if (dte > AUTO_TRADE_CONFIG.maxDte) return false;
  if (confidence < 60) return false;

  // Check max open positions
  if (currentPositions.size >= AUTO_TRADE_CONFIG.maxOpenPositions) return false;

  // Check if we already have a position in this symbol
  const existingSymbolPositions = Array.from(currentPositions.values())
    .filter(p => p.symbol === symbol && p.status === 'open');
  if (existingSymbolPositions.length > 0) return false;

  // Market hours check
  const isFuture = Object.keys(FUTURES_SYMBOLS).includes(symbol);
  if (isFuture && !isFuturesMarketOpen()) return false;
  if (!isFuture && !isEquityMarketOpen()) return false;

  // Advanced filters
  // Avoid far OTM options unless they're high conviction
  const delta = greeks?.delta || 0;
  if (Math.abs(delta) < 0.2 && stanceScore < 70) return false;

  // Require higher confidence for closing trades (BTC/STC)
  if ((direction === 'BTC' || direction === 'STC') && confidence < 75) return false;

  // Volume/OI spike requirement for regular trades
  if (volOiRatio < 1 && !classifications.includes('SWEEP') && !classifications.includes('BLOCK')) return false;

  // Market trend alignment - prefer trades that align with overall flow trend
  if (marketTrend !== 'NEUTRAL') {
    const tradeDirection = stanceLabel === 'BULL' ? 'BULLISH' : 'BEARISH';
    if (marketTrend !== tradeDirection && stanceScore < 70) return false;
  }

  return true;
}

/**
 * Place simulated trade (paper trading)
 */
async function placeSimulatedTrade(orderDetails) {
  const { conid, symbol, quantity, orderType, side, price, isOption } = orderDetails;
  
  console.log(`[SIM-TRADE] Placing ${side} order: ${symbol} x${quantity} @ ${price || 'MKT'}`);
  
  // Simulate order execution with slight price variation
  const executedPrice = orderType === 'MKT' 
    ? price * (0.995 + Math.random() * 0.01) // 0.5% spread simulation
    : price;
  
  const positionId = `sim_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  
  return {
    success: true,
    orderId: positionId,
    executedPrice: executedPrice,
    simulated: true
  };
}

/**
 * Place real trade through IBKR API
 */
async function placeRealOrder(orderDetails) {
  try {
    const { conid, symbol, quantity, orderType, side, price, isOption } = orderDetails;
    
    const orderPayload = {
      acctId: process.env.IBKR_ACCOUNT_ID || 'DU####',
      conid: conid,
      secType: isOption ? 'OPT' : 'FOP',
      orderType: orderType,
      side: side,
      quantity: quantity,
      price: price || 0,
      tif: 'DAY',
      outsideRTH: true
    };

    if (orderType === 'LMT') {
      orderPayload.price = price;
    }

    console.log(`[REAL-TRADE] Placing ${side} order: ${symbol} x${quantity} @ ${price || 'MKT'}`);

    const response = await ax.post('/iserver/account/orders', orderPayload);
    
    if (response.data && response.data.length > 0) {
      const orderId = response.data[0].id;
      console.log(`[REAL-TRADE] Order placed successfully: ${orderId}`);
      
      // Confirm order
      await sleep(1000);
      const confirmResponse = await ax.post(`/iserver/reply/${response.data[0].id}`, {
        confirmed: true
      });

      return {
        success: true,
        orderId: orderId,
        executedPrice: price,
        simulated: false
      };
    }

    return { success: false, error: 'No order ID returned' };
  } catch (error) {
    console.error('[REAL-TRADE] Order placement error:', error.message);
    return { success: false, error: error.message };
  }
}

/**
 * Determine optimal trade strategy based on flow and market conditions
 */
function determineTradeStrategy(tradeSignal, marketTrend) {
  const isBullish = tradeSignal.stanceLabel === 'BULL';
  const isCall = tradeSignal.type === 'CALL';
  
  // Base strategy: follow the flow signal
  if (isBullish) {
    if (isCall) {
      return { side: 'BUY', type: 'LONG_CALL' };
    } else {
      return { side: 'SELL', type: 'SHORT_PUT' };
    }
  } else {
    if (isCall) {
      return { side: 'SELL', type: 'SHORT_CALL' };
    } else {
      return { side: 'BUY', type: 'LONG_PUT' };
    }
  }
}

/**
 * Execute auto-trade based on comprehensive flow analysis
 */
async function executeAutoTrade(tradeSignal) {
  if (!AUTO_TRADE_CONFIG.enabled) return;

  // Get market trend for this symbol
  const marketTrend = getMarketTrend(tradeSignal.symbol);

  // Check trading limits
  if (tradingStats.daily.pnl <= -AUTO_TRADE_CONFIG.maxDailyLoss) {
    console.log('[AUTO-TRADE] Daily loss limit reached, skipping trade');
    return;
  }

  // Enhanced trade decision with market trend consideration
  if (!shouldEnterTrade(tradeSignal, activePositions, marketTrend)) {
    return;
  }

  // Simulate available capital for position sizing
  const availableCapital = AUTO_TRADE_CONFIG.maxPositionSize * 10; // 10x max position
  const positionSize = calculatePositionSize(tradeSignal, availableCapital, marketTrend);
  
  if (positionSize <= 0) {
    console.log('[AUTO-TRADE] Position size too small, skipping trade');
    return;
  }

  // Determine trade strategy based on flow signal and market trend
  const tradeStrategy = determineTradeStrategy(tradeSignal, marketTrend);
  
  const optionPrice = tradeSignal.optionPrice;
  const quantity = Math.max(1, Math.floor(positionSize / (optionPrice * 100)));
  
  const orderDetails = {
    conid: tradeSignal.conid,
    symbol: tradeSignal.symbol,
    quantity: quantity,
    orderType: 'MKT',
    side: tradeStrategy.side,
    price: optionPrice,
    isOption: true,
    strategy: tradeStrategy.type
  };

  // Place order (real or simulated)
  const orderResult = AUTO_TRADE_CONFIG.simulation 
    ? await placeSimulatedTrade(orderDetails)
    : await placeRealOrder(orderDetails);

  if (orderResult.success) {
    // Track the new position
    const positionId = orderResult.orderId;
    const position = {
      id: positionId,
      conid: tradeSignal.conid,
      symbol: tradeSignal.symbol,
      quantity: quantity,
      side: tradeStrategy.side,
      orderType: 'MKT',
      avgPrice: orderResult.executedPrice,
      currentPrice: orderResult.executedPrice,
      openedAt: new Date().toISOString(),
      status: 'open',
      simulated: orderResult.simulated,
      strategy: tradeStrategy.type,
      signal: {
        stanceScore: tradeSignal.stanceScore,
        stanceLabel: tradeSignal.stanceLabel,
        premium: tradeSignal.premium,
        confidence: tradeSignal.confidence,
        marketTrend: marketTrend
      },
      pnl: 0,
      pnlPercent: 0
    };

    activePositions.set(positionId, position);
    tradingStats.daily.trades++;
    tradingStats.totalTrades++;
    tradingStats.daily.openPositions = activePositions.size;

    // Broadcast trade execution
    broadcastAll({
      type: 'AUTO_TRADE_EXECUTED',
      positionId: positionId,
      symbol: tradeSignal.symbol,
      side: tradeStrategy.side,
      quantity: quantity,
      price: orderResult.executedPrice,
      size: positionSize,
      signal: tradeSignal.stanceLabel,
      confidence: tradeSignal.confidence,
      marketTrend: marketTrend,
      strategy: tradeStrategy.type,
      simulated: orderResult.simulated,
      timestamp: new Date().toISOString()
    });

    // Broadcast updated trading stats
    broadcastTradingStats();

    console.log(`[AUTO-TRADE] ${orderResult.simulated ? 'SIMULATED' : 'LIVE'} Trade executed: ${tradeStrategy.side} ${quantity} ${tradeSignal.symbol} ${tradeSignal.type}`);
    console.log(`[AUTO-TRADE] Market Trend: ${marketTrend}, Strategy: ${tradeStrategy.type}`);
  }
}

/**
 * Monitor and manage open positions with realistic P&L
 */
async function monitorPositions() {
  if (!AUTO_TRADE_CONFIG.enabled) return;

  let totalPnL = 0;
  let updated = false;

  for (const [positionId, position] of activePositions) {
    if (position.status !== 'open') continue;

    try {
      // Get current quote for position
      const snapshot = await mdSnapshot([position.conid]);
      const currentRow = snapshot?.[0] || {};
      const currentPrice = px(currentRow['31']);
      
      if (!currentPrice) continue;

      // Calculate P&L
      const priceChange = currentPrice - position.avgPrice;
      const pnl = priceChange * position.quantity * 100;
      const pnlPercent = (priceChange / position.avgPrice) * 100;

      // Update position with current P&L
      position.currentPrice = currentPrice;
      position.pnl = pnl;
      position.pnlPercent = pnlPercent;
      position.lastUpdated = new Date().toISOString();

      totalPnL += pnl;
      updated = true;

      // Enhanced exit logic
      const timeInTrade = Date.now() - new Date(position.openedAt).getTime();
      const hoursInTrade = timeInTrade / (1000 * 60 * 60);

      let shouldClose = false;
      let closeReason = '';

      // Dynamic exit logic based on strategy and market conditions
      if (position.strategy.includes('LONG')) {
        // Long positions: take profits earlier, tighter stops
        if (pnlPercent >= 20) {
          shouldClose = true;
          closeReason = 'Profit target reached (20%)';
        } else if (pnlPercent <= -12) {
          shouldClose = true;
          closeReason = 'Stop loss triggered (12%)';
        }
      } else {
        // Short positions: different risk parameters
        if (pnlPercent >= 15) {
          shouldClose = true;
          closeReason = 'Profit target reached (15%)';
        } else if (pnlPercent <= -20) {
          shouldClose = true;
          closeReason = 'Stop loss triggered (20%)';
        }
      }

      // Time-based exit
      if (hoursInTrade >= 4 && Math.abs(pnlPercent) < 5) {
        shouldClose = true;
        closeReason = 'Time-based exit (no movement)';
      }

      // End of day close for day trading
      if (hoursInTrade >= 6) {
        shouldClose = true;
        closeReason = 'End of day close';
      }

      if (shouldClose) {
        await closePosition(positionId, currentPrice, closeReason);
      }

    } catch (error) {
      console.error(`[AUTO-TRADE] Error monitoring position ${positionId}:`, error.message);
    }
  }

  // Broadcast updated P&L if positions changed
  if (updated) {
    broadcastAll({
      type: 'LIVE_PNL_UPDATE',
      totalPnL: totalPnL,
      openPositions: Array.from(activePositions.values()).filter(p => p.status === 'open'),
      timestamp: new Date().toISOString()
    });
  }
}

/**
 * Close position with P&L tracking
 */
async function closePosition(positionId, currentPrice, reason) {
  const position = activePositions.get(positionId);
  if (!position) return;

  const closeSide = position.side === 'BUY' ? 'SELL' : 'BUY';
  
  const orderDetails = {
    conid: position.conid,
    symbol: position.symbol,
    quantity: position.quantity,
    orderType: 'MKT',
    side: closeSide,
    price: currentPrice,
    isOption: true
  };

  const orderResult = AUTO_TRADE_CONFIG.simulation 
    ? await placeSimulatedTrade(orderDetails)
    : await placeRealOrder(orderDetails);

  if (orderResult.success) {
    const finalPnL = (currentPrice - position.avgPrice) * position.quantity * 100;
    
    position.status = 'closed';
    position.closedAt = new Date().toISOString();
    position.closePrice = currentPrice;
    position.pnl = finalPnL;
    position.pnlPercent = ((currentPrice - position.avgPrice) / position.avgPrice) * 100;
    position.closeReason = reason;

    // Update trading stats
    tradingStats.daily.pnl += finalPnL;
    tradingStats.totalPnL += finalPnL;
    tradingStats.daily.openPositions = Array.from(activePositions.values()).filter(p => p.status === 'open').length;
    
    if (finalPnL > 0) {
      tradingStats.daily.wins++;
    } else {
      tradingStats.daily.losses++;
    }

    orderHistory.push(position);

    broadcastAll({
      type: 'AUTO_TRADE_CLOSED',
      positionId: positionId,
      symbol: position.symbol,
      pnl: finalPnL,
      pnlPercent: position.pnlPercent,
      reason: reason,
      timestamp: new Date().toISOString()
    });

    // Broadcast updated stats
    broadcastTradingStats();

    console.log(`[AUTO-TRADE] 🔒 Position closed: ${position.symbol} PnL: $${finalPnL.toFixed(2)} (${reason})`);
  }
}

/**
 * Broadcast current trading statistics
 */
function broadcastTradingStats() {
  const openPositions = Array.from(activePositions.values()).filter(p => p.status === 'open');
  const totalOpenPnL = openPositions.reduce((sum, pos) => sum + pos.pnl, 0);
  
  const stats = {
    ...tradingStats,
    openPnL: totalOpenPnL,
    openPositionsCount: openPositions.length
  };

  broadcastAll({
    type: 'TRADING_STATS',
    stats: stats,
    timestamp: new Date().toISOString()
  });
}

/* --------------------------- Trading Loops --------------------------- */
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

/* ------------------------- HTTP Routes -------------------------------- */
app.get('/health', (req,res)=>res.json({ ok:true, ts:Date.now() }));

app.get('/trading/status', (req, res) => {
  const openPositions = Array.from(activePositions.values()).filter(p => p.status === 'open');
  const totalOpenPnL = openPositions.reduce((sum, pos) => sum + pos.pnl, 0);
  
  res.json({
    autoTrading: AUTO_TRADE_CONFIG.enabled,
    simulation: AUTO_TRADE_CONFIG.simulation,
    config: AUTO_TRADE_CONFIG,
    stats: {
      ...tradingStats,
      openPnL: totalOpenPnL,
      openPositionsCount: openPositions.length
    },
    openPositions: openPositions,
    symbolTrends: Object.fromEntries(symbolFlowTrends),
    today: tradingStats.daily
  });
});

app.post('/trading/enable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = true;
  res.json({ message: 'Auto-trading enabled', enabled: true });
});

app.post('/trading/disable', (req, res) => {
  AUTO_TRADE_CONFIG.enabled = false;
  res.json({ message: 'Auto-trading disabled', enabled: false });
});

app.post('/trading/simulation', (req, res) => {
  AUTO_TRADE_CONFIG.simulation = req.body.simulation !== false;
  tradingStats.simulation = AUTO_TRADE_CONFIG.simulation;
  res.json({ 
    message: `Simulation mode ${AUTO_TRADE_CONFIG.simulation ? 'enabled' : 'disabled'}`,
    simulation: AUTO_TRADE_CONFIG.simulation 
  });
});

app.post('/trading/close-all', async (req, res) => {
  try {
    const closePromises = Array.from(activePositions.entries())
      .filter(([id, position]) => position.status === 'open')
      .map(([id, position]) => closePosition(id, position.currentPrice, 'Manual close all'));
    
    await Promise.all(closePromises);
    res.json({ message: 'All positions closed', closed: closePromises.length });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.get('/trading/history', (req, res) => {
  res.json({
    orderHistory: orderHistory.slice(-50),
    stats: tradingStats,
    recentFlows: recentFlows.slice(-20)
  });
});

app.post('/trading/config', (req, res) => {
  const { minStanceScore, maxPositionSize, maxDte } = req.body;
  
  if (minStanceScore !== undefined) AUTO_TRADE_CONFIG.minStanceScore = parseInt(minStanceScore);
  if (maxPositionSize !== undefined) AUTO_TRADE_CONFIG.maxPositionSize = parseFloat(maxPositionSize);
  if (maxDte !== undefined) AUTO_TRADE_CONFIG.maxDte = parseInt(maxDte);
  
  res.json({ 
    message: 'Configuration updated',
    config: AUTO_TRADE_CONFIG 
  });
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
    message:'Connected to IBKR Flow (Equities + Futures) with Auto-Trading',
    availableFutures: Object.keys(FUTURES_SYMBOLS),
    availableEquities: EQUITY_SYMBOLS,
    conidMappings: initialMappings,
    autoTrading: AUTO_TRADE_CONFIG.enabled,
    simulation: AUTO_TRADE_CONFIG.simulation
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
      } else if (d.action === 'get_trading_stats') {
        broadcastTradingStats();
      }
    }catch(e){}
  });
  
  ws.on('close', ()=>clients.delete(ws));
});

/* --------------------------- Runner ----------------------------------- */
(async () => {
  console.log(`HTTP+WS @ :${PORT}  IBKR=${IBKR_HOST}/v1/api`);
  console.log(`AUTO-TRADING: ${AUTO_TRADE_CONFIG.enabled ? 'ENABLED' : 'DISABLED'}`);
  console.log(`MODE: ${AUTO_TRADE_CONFIG.simulation ? 'SIMULATION' : 'LIVE TRADING'}`);
  
  try {
    await primeIB();
    await setMarketDataLive();
  } catch (e) {
    console.error('[boot]', e?.response?.data || e.message || e);
  }
  
  server.listen(PORT, () => console.log('[server] listening on :'+PORT));
  
  // Position monitoring loop
  setInterval(async () => {
    await monitorPositions();
  }, 30000); // Check every 30 seconds

  // Stats broadcasting loop
  setInterval(() => {
    broadcastTradingStats();
  }, 10000); // Broadcast stats every 10 seconds

  // Reset daily stats if date changed
  setInterval(() => {
    const today = new Date().toISOString().split('T')[0];
    if (tradingStats.daily.date !== today) {
      tradingStats.daily = {
        date: today,
        pnl: 0,
        trades: 0,
        wins: 0,
        losses: 0,
        openPositions: Array.from(activePositions.values()).filter(p => p.status === 'open').length
      };
      console.log('[AUTO-TRADE] Reset daily trading stats');
    }
  }, 60000); // Check every minute

  async function coordinatorLoop(){
    while(true){
      const futs = ['/ES','/NQ', '/YM'];
      const eqs = ['SPY','PLTR','NVDA','META'];
      
      // Process futures
      for (const f of futs) await loopFuturesSymbol(f);
      
      // Process equities
      for (const s of eqs) await loopEquitySymbol(s);
      
      // Poll live quotes
      await pollLiveQuotes();
      
      await sleep(1500);
    }
  }
  
  coordinatorLoop().catch(e=>console.error('[coordinator]', e.message));
})();
