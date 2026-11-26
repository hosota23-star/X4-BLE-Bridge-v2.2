package com.x4tether.bridge

import android.net.Uri
import org.json.JSONArray
import org.json.JSONObject
import java.io.ByteArrayOutputStream
import java.io.InputStream
import java.net.HttpURLConnection
import java.net.URL
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.TimeZone
import java.util.concurrent.Callable
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.zip.GZIPInputStream
import kotlin.math.abs
import kotlin.math.pow
import kotlin.math.roundToInt

/**
 * Real-time Hybrid Market Data Engine running directly on the user's smartphone in Japan.
 *
 * Sources combined in parallel:
 *  1. Japanese TSE equities & Nikkei/TOPIX spot -> Yahoo! Finance Japan (finance.yahoo.co.jp, 0-min real-time)
 *  2. 24h Index CFDs, FX & US Extended Hours   -> TradingView Scanner API (with premarket/postmarket columns)
 *  3. Crypto 24/7 Spot                         -> Coinbase Exchange real-time stats API
 *  4. 1-minute intraday & Pre/Post charts      -> Yahoo Finance v8 chart API (interval=1m, includePrePost=true)
 */
object StockQuoteEngine {

    private const val ENGINE_VER = "2.2-rt"
    private const val MICRO_CACHE_MS = 3000L
    private const val UA_BROWSER =
        "Mozilla/5.0 (Linux; Android 15; Pixel) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36"

    private val workerPool = Executors.newFixedThreadPool(6)
    private val microCache = ConcurrentHashMap<String, CachedPayload>()

    private data class CachedPayload(val tsMs: Long, val jsonBytes: ByteArray)

    private data class SymbolSpec(
        val id: String,
        val tv: List<String>,
        val yf: String?,
        val yfAlt: String? = null,
        val yjCode: String? = null,
        val spotYjCode: String? = null,
        val spotTv: String? = null,
        val spotYf: String? = null,
        val cbProduct: String? = null,
        val isUsEquity: Boolean = false,
        val name: String = "",
        val cur: String = "USD"
    )

    private data class QuoteTick(
        val name: String,
        val price: Double,
        val chg: Double,
        val pct: Double,
        val prevClose: Double? = null,
        val cur: String = "",
        val src: String = "RT",
        val sess: String = "",
        val regPrice: Double? = null,
        val extDiff: Double? = null,
        val extPct: Double? = null
    )

    private data class ChartResult(
        val name: String,
        val price: Double?,
        val prevClose: Double?,
        val chg: Double,
        val pct: Double,
        val cur: String,
        val pts: List<Double>,
        val prePrice: Double? = null,
        val preChg: Double? = null,
        val prePct: Double? = null,
        val preTime: Long = 0L,
        val postPrice: Double? = null,
        val postChg: Double? = null,
        val postPct: Double? = null,
        val postTime: Long = 0L,
        val regTime: Long = 0L
    )

    private val PRESET_MAP: Map<String, SymbolSpec> = mapOf(
        "NI225" to SymbolSpec(
            id = "NI225",
            tv = listOf("OANDA:JP225JPY", "FX:JPN225"),
            yf = "NKD=F",
            yfAlt = "^N225",
            spotYjCode = "998407.O",
            spotTv = "TVC:NI225",
            spotYf = "^N225",
            name = "Nikkei 225 CFD",
            cur = "JPY"
        ),
        "JP225" to SymbolSpec(
            id = "JP225",
            tv = listOf("OANDA:JP225JPY", "FX:JPN225"),
            yf = "NKD=F",
            yfAlt = "^N225",
            spotYjCode = "998407.O",
            spotTv = "TVC:NI225",
            spotYf = "^N225",
            name = "Nikkei 225 CFD",
            cur = "JPY"
        ),
        "NK225" to SymbolSpec(
            id = "NK225",
            tv = listOf("OANDA:JP225JPY", "FX:JPN225"),
            yf = "NKD=F",
            yfAlt = "^N225",
            spotYjCode = "998407.O",
            spotTv = "TVC:NI225",
            spotYf = "^N225",
            name = "Nikkei 225 CFD",
            cur = "JPY"
        ),
        "N225" to SymbolSpec(
            id = "N225",
            tv = listOf("TVC:NI225"),
            yf = "^N225",
            yjCode = "998407.O",
            name = "Nikkei 225 Spot",
            cur = "JPY"
        ),
        "TOPIX" to SymbolSpec(
            id = "TOPIX",
            tv = listOf("TVC:TOPIX", "TSE:TOPIX"),
            yf = "1306.T",
            yjCode = "998405.T",
            name = "TOPIX",
            cur = "JPY"
        ),
        "SPX" to SymbolSpec(
            id = "SPX",
            tv = listOf("SP:SPX", "OANDA:SPX500USD", "FOREXCOM:SPXUSD", "TVC:SPX"),
            yf = "^GSPC",
            yfAlt = "ES=F",
            name = "S&P 500",
            cur = "USD"
        ),
        "SP500" to SymbolSpec(
            id = "SP500",
            tv = listOf("SP:SPX", "OANDA:SPX500USD", "TVC:SPX"),
            yf = "^GSPC",
            yfAlt = "ES=F",
            name = "S&P 500",
            cur = "USD"
        ),
        "US500" to SymbolSpec(
            id = "US500",
            tv = listOf("OANDA:SPX500USD", "FOREXCOM:SPXUSD", "SP:SPX"),
            yf = "ES=F",
            yfAlt = "^GSPC",
            spotTv = "SP:SPX",
            spotYf = "^GSPC",
            name = "US500 CFD",
            cur = "USD"
        ),
        "NDX" to SymbolSpec(
            id = "NDX",
            tv = listOf("NASDAQ:NDX", "TVC:NDX", "OANDA:NAS100USD"),
            yf = "^NDX",
            yfAlt = "NQ=F",
            name = "NASDAQ 100",
            cur = "USD"
        ),
        "NAS100" to SymbolSpec(
            id = "NAS100",
            tv = listOf("OANDA:NAS100USD", "NASDAQ:NDX"),
            yf = "NQ=F",
            yfAlt = "^NDX",
            name = "NAS100 CFD",
            cur = "USD"
        ),
        "DJI" to SymbolSpec(
            id = "DJI",
            tv = listOf("DJ:DJI", "TVC:DJI", "OANDA:US30USD"),
            yf = "^DJI",
            yfAlt = "YM=F",
            name = "Dow Jones",
            cur = "USD"
        ),
        "US30" to SymbolSpec(
            id = "US30",
            tv = listOf("OANDA:US30USD", "DJ:DJI"),
            yf = "YM=F",
            yfAlt = "^DJI",
            name = "US30 CFD",
            cur = "USD"
        ),
        "VIX" to SymbolSpec(
            id = "VIX",
            tv = listOf("TVC:VIX", "CBOE:VIX"),
            yf = "^VIX",
            name = "VIX Index",
            cur = "USD"
        ),
        "GOLD" to SymbolSpec(
            id = "GOLD",
            tv = listOf("OANDA:XAUUSD", "TVC:GOLD"),
            yf = "GC=F",
            name = "Gold / USD",
            cur = "USD"
        ),
        "XAUUSD" to SymbolSpec(
            id = "XAUUSD",
            tv = listOf("OANDA:XAUUSD", "TVC:GOLD"),
            yf = "GC=F",
            name = "Gold / USD",
            cur = "USD"
        ),
        "BTCUSD" to SymbolSpec(
            id = "BTCUSD",
            tv = listOf("COINBASE:BTCUSD", "BITSTAMP:BTCUSD"),
            yf = "BTC-USD",
            cbProduct = "BTC-USD",
            name = "BTC / USD",
            cur = "USD"
        ),
        "BTC" to SymbolSpec(
            id = "BTC",
            tv = listOf("COINBASE:BTCUSD", "BITSTAMP:BTCUSD"),
            yf = "BTC-USD",
            cbProduct = "BTC-USD",
            name = "BTC / USD",
            cur = "USD"
        ),
        "ETHUSD" to SymbolSpec(
            id = "ETHUSD",
            tv = listOf("COINBASE:ETHUSD", "BITSTAMP:ETHUSD"),
            yf = "ETH-USD",
            cbProduct = "ETH-USD",
            name = "ETH / USD",
            cur = "USD"
        ),
        "USDJPY" to SymbolSpec(
            id = "USDJPY",
            tv = listOf("FX:USDJPY", "OANDA:USDJPY"),
            yf = "JPY=X",
            name = "USD / JPY",
            cur = "JPY"
        ),
        "9984" to SymbolSpec(
            id = "9984",
            tv = listOf("TSE:9984"),
            yf = "9984.T",
            yjCode = "9984.T",
            name = "SoftBank Group",
            cur = "JPY"
        ),
        "285A" to SymbolSpec(
            id = "285A",
            tv = listOf("TSE:285A"),
            yf = "285A.T",
            yjCode = "285A.T",
            name = "Kioxia HD",
            cur = "JPY"
        )
    )

    private val YF_INDEX_ALIAS = mapOf(
        "SPX" to "^GSPC",
        "SP500" to "^GSPC",
        "NDX" to "^NDX",
        "DJI" to "^DJI",
        "VIX" to "^VIX",
        "NI225" to "^N225",
        "GOLD" to "GC=F"
    )

    fun executeLocalStockUrl(
        urlStr: String,
        wantZlib: Boolean,
        isCancelled: () -> Boolean = { false }
    ): HttpProxyEngine.ProxyResponse {
        return try {
            val uri = Uri.parse(urlStr)
            val rawSymbols = (uri.getQueryParameter("symbols") ?: "NI225,SPX,BTCUSD,9984,285A").trim()
            val wantChart = uri.getQueryParameter("chart") == "1" || uri.getQueryParameter("chart") == "true"
            val range = validateRange(uri.getQueryParameter("range") ?: "1d")

            val symbols = rawSymbols.split(",")
                .map { it.trim().uppercase(Locale.US) }
                .filter { it.isNotEmpty() }
                .distinct()
                .take(12)

            if (symbols.isEmpty()) {
                return errorJson("no symbols")
            }

            val cacheKey = "${symbols.joinToString(",")}|$wantChart|$range"
            val nowMs = System.currentTimeMillis()
            val hit = microCache[cacheKey]
            if (hit != null && (nowMs - hit.tsMs) in 0..MICRO_CACHE_MS) {
                return wrapPayload(hit.jsonBytes, wantZlib, "rt-stock(cached)")
            }

            val specs = symbols.map { resolveSymbol(it) }

            // Launch TradingView batch + per-symbol real-time tasks concurrently
            val tvFuture = workerPool.submit(Callable {
                if (isCancelled()) emptyMap() else fetchTradingViewBatch(specs)
            })

            val yjFutures = HashMap<String, java.util.concurrent.Future<QuoteTick?>>()
            val cbFutures = HashMap<String, java.util.concurrent.Future<QuoteTick?>>()
            val chartFutures = HashMap<String, java.util.concurrent.Future<ChartResult?>>()

            for (spec in specs) {
                if (spec.yjCode != null && !yjFutures.containsKey(spec.yjCode)) {
                    val code = spec.yjCode
                    yjFutures[code] = workerPool.submit(Callable {
                        if (isCancelled()) null else fetchYahooJapanRealtime(code)
                    })
                }
                if (spec.spotYjCode != null && !yjFutures.containsKey(spec.spotYjCode)) {
                    val scode = spec.spotYjCode
                    yjFutures[scode] = workerPool.submit(Callable {
                        if (isCancelled()) null else fetchYahooJapanRealtime(scode)
                    })
                }
                if (spec.cbProduct != null && !cbFutures.containsKey(spec.cbProduct)) {
                    val prod = spec.cbProduct
                    cbFutures[prod] = workerPool.submit(Callable {
                        if (isCancelled()) null else fetchCoinbaseRealtime(prod)
                    })
                }
                if ((wantChart || spec.isUsEquity || spec.yjCode == null) && spec.yf != null) {
                    chartFutures[spec.id] = workerPool.submit(Callable {
                        if (isCancelled()) return@Callable null
                        fetchYahooGlobalChart(spec.yf, range, includePrePost = spec.isUsEquity)
                            ?: (if (spec.yfAlt != null && spec.yfAlt != spec.yf) {
                                fetchYahooGlobalChart(spec.yfAlt, range, includePrePost = spec.isUsEquity)
                            } else null)
                    })
                }
            }

            val tvMap = try {
                tvFuture.get(10, TimeUnit.SECONDS)
            } catch (_: Exception) {
                emptyMap()
            }

            val itemsArr = JSONArray()
            for (spec in specs) {
                if (isCancelled()) return errorJson("cancelled")

                val yjTick = spec.yjCode?.let { code ->
                    try { yjFutures[code]?.get(9, TimeUnit.SECONDS) } catch (_: Exception) { null }
                }
                val cbTick = spec.cbProduct?.let { prod ->
                    try { cbFutures[prod]?.get(7, TimeUnit.SECONDS) } catch (_: Exception) { null }
                }
                var chartData = try {
                    chartFutures[spec.id]?.get(10, TimeUnit.SECONDS)
                } catch (_: Exception) {
                    null
                }

                var tvTick: QuoteTick? = null
                var matchedTv = spec.tv.firstOrNull() ?: ""
                for (cand in spec.tv) {
                    val found = tvMap[cand]
                    if (found != null) {
                        tvTick = found
                        matchedTv = cand
                        break
                    }
                }

                // Merge priority by asset type for true real-time accuracy:
                // 1) Japanese TSE / Nikkei Spot / TOPIX -> Yahoo! Finance Japan (0-min delay)
                // 2) Crypto -> Coinbase real-time ticker
                // 3) US Equities -> Extended-hours aware merge (Yahoo 1m Pre/Post + TradingView Pre/Post)
                // 4) Global CFDs / FX / Indices -> TradingView real-time stream -> Yahoo Chart
                var chosen: QuoteTick? = when {
                    yjTick != null -> yjTick
                    cbTick != null -> cbTick
                    spec.isUsEquity -> mergeUsRealtime(tvTick, chartData, spec)
                    tvTick != null -> tvTick
                    else -> null
                }

                if (chosen == null && chartData == null && spec.yf != null) {
                    chartData = fetchYahooGlobalChart(spec.yf, range, includePrePost = spec.isUsEquity)
                }

                if (chosen == null && chartData != null && chartData.price != null) {
                    chosen = QuoteTick(
                        name = chartData.name,
                        price = chartData.price,
                        chg = chartData.chg,
                        pct = chartData.pct,
                        prevClose = chartData.prevClose,
                        cur = chartData.cur.ifEmpty { spec.cur },
                        src = "YF-1M"
                    )
                }

                if (chosen == null) {
                    itemsArr.put(JSONObject().apply {
                        put("id", spec.id)
                        put("name", spec.name.ifEmpty { spec.id })
                        put("tv", matchedTv)
                        put("src", "ERR")
                        put("price", JSONObject.NULL)
                        put("chg", JSONObject.NULL)
                        put("pct", JSONObject.NULL)
                        put("cur", spec.cur)
                        put("err", "unavailable")
                    })
                    continue
                }

                val itemObj = JSONObject().apply {
                    put("id", spec.id)
                    put("name", cleanAsciiSafeName(spec.name.ifEmpty { chosen.name.ifEmpty { spec.id } }, spec.id))
                    put("tv", matchedTv)
                    put("src", chosen.src)
                    if (chosen.sess.isNotEmpty()) put("sess", chosen.sess)
                    putRoundSmart("price", chosen.price)
                    putRoundSmart("chg", chosen.chg)
                    putRoundFixed("pct", chosen.pct, 2)
                    put("cur", chosen.cur.ifEmpty { spec.cur })
                }

                // Populate sub-line: either CFD-vs-Spot real-time spread OR US Extended-Hours vs Regular close
                if (spec.spotYjCode != null || spec.spotTv != null || spec.spotYf != null) {
                    val spotYj = spec.spotYjCode?.let { scode ->
                        try { yjFutures[scode]?.get(6, TimeUnit.SECONDS) } catch (_: Exception) { null }
                    }
                    val spotPrice: Double? = spotYj?.price
                        ?: spec.spotTv?.let { tvMap[it]?.price }
                        ?: spec.spotYf?.let { fetchYahooGlobalChart(it, "1d", false)?.price }

                    if (spotPrice != null && spotPrice.isFinite() && spotPrice != 0.0) {
                        val diff = chosen.price - spotPrice
                        itemObj.putRoundSmart("spot", spotPrice)
                        itemObj.putRoundSmart("spread", diff)
                        itemObj.putRoundFixed("spreadPct", (diff / spotPrice) * 100.0, 2)
                    }
                } else if (chosen.regPrice != null && chosen.extDiff != null && chosen.extPct != null) {
                    itemObj.put("spotLabel", "Reg")
                    itemObj.put("diffLabel", chosen.sess.ifEmpty { "Ext" })
                    itemObj.putRoundSmart("spot", chosen.regPrice)
                    itemObj.putRoundSmart("spread", chosen.extDiff)
                    itemObj.putRoundFixed("spreadPct", chosen.extPct, 2)
                }

                if (wantChart && chartData != null && chartData.pts.isNotEmpty()) {
                    val mergedPts = ArrayList<Double>(chartData.pts.size + 1)
                    mergedPts.addAll(chartData.pts)
                    // Append the live real-time tick at the right tip of 1D chart so chart matches live price
                    if (range == "1d" && chosen.price.isFinite()) {
                        val lastPt = mergedPts.lastOrNull()
                        if (lastPt == null || abs(lastPt - chosen.price) > 1e-6) {
                            mergedPts.add(roundSmartVal(chosen.price))
                        }
                    }
                    if (mergedPts.size >= 2) {
                        val ds = downsample(mergedPts, 36)
                        val ptsJson = JSONArray()
                        for (v in ds) ptsJson.put(v)
                        itemObj.put("pts", ptsJson)
                        val pv = chosen.prevClose ?: chartData.prevClose
                        if (pv != null && pv.isFinite()) {
                            itemObj.putRoundSmart("prev", pv)
                        }
                    }
                }

                itemsArr.put(itemObj)
            }

            val jst = TimeZone.getTimeZone("Asia/Tokyo")
            val now = Date()
            val fmtHms = SimpleDateFormat("HH:mm:ss", Locale.US).apply { timeZone = jst }
            val fmtMd = SimpleDateFormat("MM/dd", Locale.US).apply { timeZone = jst }

            val outJson = JSONObject().apply {
                put("ok", true)
                put("ver", ENGINE_VER)
                put("ts", now.time / 1000L)
                put("updated", fmtHms.format(now))
                put("date", fmtMd.format(now))
                put("items", itemsArr)
            }.toString().toByteArray(Charsets.UTF_8)

            microCache[cacheKey] = CachedPayload(System.currentTimeMillis(), outJson)
            wrapPayload(outJson, wantZlib, "rt-stock(${symbols.size})")
        } catch (e: Exception) {
            errorJson("${e.javaClass.simpleName}: ${e.message ?: "err"}")
        }
    }

    private fun mergeUsRealtime(tv: QuoteTick?, yf: ChartResult?, spec: SymbolSpec): QuoteTick? {
        // Check Yahoo Finance 1m + Pre/Post timestamps first (accurate session detection)
        if (yf != null && yf.price != null) {
            val regP = yf.price
            // Post-market active if postTime > regTime and postPrice is present
            if (yf.postPrice != null && yf.postTime > yf.regTime && yf.regTime > 0L) {
                val prev = yf.prevClose ?: regP
                val totalChg = yf.postPrice - prev
                val totalPct = if (prev != 0.0) (totalChg / prev) * 100.0 else 0.0
                val extDiff = yf.postChg ?: (yf.postPrice - regP)
                val extPct = yf.postPct ?: (if (regP != 0.0) (extDiff / regP) * 100.0 else 0.0)
                return QuoteTick(
                    name = tv?.name ?: yf.name,
                    price = yf.postPrice,
                    chg = totalChg,
                    pct = totalPct,
                    prevClose = prev,
                    cur = yf.cur.ifEmpty { spec.cur },
                    src = "RT-AFT",
                    sess = "AFT",
                    regPrice = regP,
                    extDiff = extDiff,
                    extPct = extPct
                )
            }
            // Pre-market active if preTime > regTime and prePrice is present
            if (yf.prePrice != null && yf.preTime > yf.regTime && yf.regTime > 0L) {
                val prev = regP
                val extDiff = yf.preChg ?: (yf.prePrice - regP)
                val extPct = yf.prePct ?: (if (regP != 0.0) (extDiff / regP) * 100.0 else 0.0)
                return QuoteTick(
                    name = tv?.name ?: yf.name,
                    price = yf.prePrice,
                    chg = extDiff,
                    pct = extPct,
                    prevClose = prev,
                    cur = yf.cur.ifEmpty { spec.cur },
                    src = "RT-PRE",
                    sess = "PRE",
                    regPrice = regP,
                    extDiff = extDiff,
                    extPct = extPct
                )
            }
        }

        if (tv != null) return tv
        if (yf != null && yf.price != null) {
            return QuoteTick(
                name = yf.name,
                price = yf.price,
                chg = yf.chg,
                pct = yf.pct,
                prevClose = yf.prevClose,
                cur = yf.cur.ifEmpty { spec.cur },
                src = "YF-RT",
                sess = "RT"
            )
        }
        return null
    }

    private fun resolveSymbol(raw: String): SymbolSpec {
        PRESET_MAP[raw]?.let { return it }

        if (raw.contains(":")) {
            val parts = raw.split(":", limit = 2)
            val ex = parts[0]
            val sym = parts[1]
            if (ex == "TSE" || ex == "TYO") {
                return SymbolSpec(
                    id = raw,
                    tv = listOf("TSE:$sym"),
                    yf = "$sym.T",
                    yjCode = "$sym.T",
                    cur = "JPY"
                )
            }
            if (ex == "FX" || ex == "OANDA") {
                val yf = if (sym.length == 6) "$sym=X" else sym
                val cur = if (sym.length == 6) sym.substring(3) else "USD"
                return SymbolSpec(id = raw, tv = listOf(raw), yf = yf, cur = cur)
            }
            if (ex == "COINBASE" || ex == "BITSTAMP" || ex == "BINANCE") {
                val cb = when {
                    sym.endsWith("USDT") -> sym.dropLast(4) + "-USD"
                    sym.endsWith("USD") -> sym.dropLast(3) + "-USD"
                    else -> null
                }
                return SymbolSpec(id = raw, tv = listOf(raw), yf = cb, cbProduct = cb, cur = "USD")
            }
            val isUs = (ex == "NASDAQ" || ex == "NYSE" || ex == "AMEX")
            return SymbolSpec(
                id = raw,
                tv = listOf(raw),
                yf = YF_INDEX_ALIAS[sym] ?: sym,
                isUsEquity = isUs,
                cur = "USD"
            )
        }

        // 4-char Japanese TSE code (including new alphanumeric codes like 285A)
        if (Regex("^[0-9][0-9A-Z]{3}$").matches(raw)) {
            return SymbolSpec(
                id = raw,
                tv = listOf("TSE:$raw"),
                yf = "$raw.T",
                yjCode = "$raw.T",
                cur = "JPY"
            )
        }
        if (Regex("^[0-9][0-9A-Z]{3}\\.T$").matches(raw)) {
            val code = raw.substring(0, 4)
            return SymbolSpec(
                id = code,
                tv = listOf("TSE:$code"),
                yf = raw,
                yjCode = raw,
                cur = "JPY"
            )
        }
        // FX 6-letter pair like EURJPY, GBPJPY, EURUSD
        if (Regex("^[A-Z]{6}$").matches(raw) &&
            (raw.endsWith("JPY") || raw.endsWith("USD") || raw.startsWith("USD") || raw.startsWith("EUR"))
        ) {
            val cur = raw.substring(3)
            return SymbolSpec(
                id = raw,
                tv = listOf("FX:$raw", "OANDA:$raw"),
                yf = "$raw=X",
                name = "${raw.substring(0, 3)} / $cur",
                cur = cur
            )
        }
        // Crypto pair like SOLUSD, XRPUSD, DOGEUSD
        if (Regex("^[A-Z]{2,5}USD$").matches(raw)) {
            val coin = raw.dropLast(3)
            return SymbolSpec(
                id = raw,
                tv = listOf("COINBASE:$raw", "BITSTAMP:$raw"),
                yf = "$coin-USD",
                cbProduct = "$coin-USD",
                name = "$coin / USD",
                cur = "USD"
            )
        }

        // Default: US Stock / ETF / Index
        val isIdx = YF_INDEX_ALIAS.containsKey(raw)
        return SymbolSpec(
            id = raw,
            tv = listOf("NASDAQ:$raw", "NYSE:$raw", "AMEX:$raw", "SP:$raw", "TVC:$raw"),
            yf = YF_INDEX_ALIAS[raw] ?: raw,
            yfAlt = "^$raw",
            isUsEquity = !isIdx,
            cur = "USD"
        )
    }

    /**
     * Fetches 0-second real-time TSE / Nikkei / TOPIX quotes from Yahoo! Finance Japan.
     */
    private fun fetchYahooJapanRealtime(yjCode: String): QuoteTick? {
        val url = "https://finance.yahoo.co.jp/quote/$yjCode"
        val html = httpGetString(url, maxBytes = 786432, timeoutMs = 8000) ?: return null

        val stateJsonStr = extractJsonObjectAfter(html, "window.__PRELOADED_STATE__")
        if (stateJsonStr != null) {
            try {
                val root = JSONObject(stateJsonStr)
                val candidates = ArrayList<JSONObject>()

                root.optJSONObject("mainStocksPriceBoard")?.optJSONObject("priceBoard")?.let { candidates.add(it) }
                root.optJSONObject("mainDomesticIndexPriceBoard")?.let { dom ->
                    dom.optJSONObject("indexPrices")?.let { candidates.add(it) }
                    dom.optJSONObject("priceBoard")?.let { candidates.add(it) }
                    candidates.add(dom)
                }
                root.optJSONObject("mainEtfPriceBoard")?.optJSONObject("priceBoard")?.let { candidates.add(it) }
                collectPriceBoardsRecursive(root, candidates, 0)

                val prevDetail = root.optJSONObject("mainStocksDetail")
                    ?.optJSONObject("detail")
                    ?.optJSONObject("previousPrice")
                    ?.optString("value")
                    ?.let { parseJpNum(it) }

                for (board in candidates) {
                    val livePrice = parseJpNum(board.optString("price", ""))
                        ?: parseJpNum(board.optString("realTimePrice", ""))
                        ?: parseJpNum(board.optString("savePrice", ""))
                        ?: prevDetail

                    if (livePrice != null && livePrice.isFinite() && livePrice > 0.0) {
                        val prev = parseJpNum(board.optString("savePrice", ""))
                            ?: parseJpNum(board.optString("previousPrice", ""))
                            ?: prevDetail
                        val chg = parseJpNum(board.optString("priceChange", ""))
                            ?: parseJpNum(board.optString("changePrice", ""))
                            ?: (if (prev != null) livePrice - prev else 0.0)
                        val pct = parseJpNum(board.optString("priceChangeRate", ""))
                            ?: parseJpNum(board.optString("changePriceRate", ""))
                            ?: (if (prev != null && prev != 0.0) (chg / prev) * 100.0 else 0.0)
                        val rawName = board.optString("name", "")
                            .ifEmpty { board.optString("stockName", "") }
                            .ifEmpty { board.optString("indexName", "") }

                        return QuoteTick(
                            name = rawName,
                            price = livePrice,
                            chg = chg,
                            pct = pct,
                            prevClose = prev ?: (livePrice - chg),
                            cur = "JPY",
                            src = "YJ-RT",
                            sess = "RT"
                        )
                    }
                }
            } catch (_: Exception) {
            }
        }
        return null
    }

    private fun collectPriceBoardsRecursive(obj: JSONObject, out: MutableList<JSONObject>, depth: Int) {
        if (depth > 3) return
        val keys = obj.keys()
        while (keys.hasNext()) {
            val k = keys.next()
            val child = obj.optJSONObject(k) ?: continue
            if (child.has("price") && (child.has("priceChange") || child.has("changePrice") || child.has("savePrice"))) {
                out.add(child)
            } else if (k.contains("Price", ignoreCase = true) || k.contains("Board", ignoreCase = true) || k.contains("Index", ignoreCase = true)) {
                collectPriceBoardsRecursive(child, out, depth + 1)
            }
        }
    }

    /**
     * Extracts `{ ... }` JSON literal immediately following `marker` using string-aware brace matching.
     */
    private fun extractJsonObjectAfter(text: String, marker: String): String? {
        val mIdx = text.indexOf(marker)
        if (mIdx < 0) return null
        val start = text.indexOf('{', mIdx + marker.length)
        if (start < 0) return null

        var depth = 0
        var inStr = false
        var escape = false
        val n = text.length
        for (i in start until n) {
            val c = text[i]
            if (inStr) {
                if (escape) {
                    escape = false
                } else if (c == '\\') {
                    escape = true
                } else if (c == '"') {
                    inStr = false
                }
            } else {
                when (c) {
                    '"' -> inStr = true
                    '{' -> depth++
                    '}' -> {
                        depth--
                        if (depth == 0) {
                            return text.substring(start, i + 1)
                        }
                    }
                }
            }
        }
        return null
    }

    /**
     * Fetches 24/7 real-time spot price & 24h change from Coinbase Exchange public API.
     */
    private fun fetchCoinbaseRealtime(product: String): QuoteTick? {
        val raw = httpGetString("https://api.exchange.coinbase.com/products/$product/stats", maxBytes = 16384, timeoutMs = 6000)
            ?: return null
        return try {
            val obj = JSONObject(raw)
            val last = obj.optString("last", "").toDoubleOrNull() ?: return null
            val open = obj.optString("open", "").toDoubleOrNull()
            val chg = if (open != null) last - open else 0.0
            val pct = if (open != null && open != 0.0) (chg / open) * 100.0 else 0.0
            QuoteTick(
                name = product.replace("-", " / "),
                price = last,
                chg = chg,
                pct = pct,
                prevClose = open,
                cur = "USD",
                src = "CB-RT",
                sess = "24H"
            )
        } catch (_: Exception) {
            null
        }
    }

    /**
     * Fetches batch quotes from TradingView Scanner API including Pre-Market & Post-Market columns.
     */
    private fun fetchTradingViewBatch(specs: List<SymbolSpec>): Map<String, QuoteTick> {
        val out = HashMap<String, QuoteTick>()
        val tickers = LinkedHashSet<String>()
        for (s in specs) {
            for (t in s.tv) if (t.isNotEmpty()) tickers.add(t)
            if (!s.spotTv.isNullOrEmpty()) tickers.add(s.spotTv)
        }
        if (tickers.isEmpty()) return out

        val payload = JSONObject().apply {
            put("symbols", JSONObject().apply {
                put("tickers", JSONArray(tickers.toList()))
                put("query", JSONObject().put("types", JSONArray()))
            })
            put("columns", JSONArray(listOf(
                "name",
                "description",
                "close",
                "change",
                "change_abs",
                "currency",
                "update_mode",
                "premarket_close",
                "premarket_change",
                "premarket_change_abs",
                "postmarket_close",
                "postmarket_change",
                "postmarket_change_abs"
            )))
        }.toString().toByteArray(Charsets.UTF_8)

        val conn = (URL("https://scanner.tradingview.com/global/scan").openConnection() as HttpURLConnection).apply {
            requestMethod = "POST"
            connectTimeout = 5000
            readTimeout = 7000
            doOutput = true
            useCaches = false
            setRequestProperty("Content-Type", "application/json; charset=utf-8")
            setRequestProperty("Accept-Encoding", "gzip")
            setRequestProperty("User-Agent", UA_BROWSER)
        }

        try {
            conn.setFixedLengthStreamingMode(payload.size)
            conn.outputStream.use { it.write(payload) }
            if (conn.responseCode != 200) return out
            val bodyStr = readConnString(conn, 262144) ?: return out
            val dataArr = JSONObject(bodyStr).optJSONArray("data") ?: return out

            for (i in 0 until dataArr.length()) {
                val row = dataArr.optJSONObject(i) ?: continue
                val sym = row.optString("s", "")
                val d = row.optJSONArray("d") ?: continue
                if (sym.isEmpty() || d.length() < 6) continue

                val regClose = d.optDouble(2)
                if (!regClose.isFinite()) continue
                val regPct = d.optDouble(3, 0.0).let { if (it.isFinite()) it else 0.0 }
                val regChg = d.optDouble(4, Double.NaN).let {
                    if (it.isFinite()) it else (regClose * regPct / (100.0 + regPct))
                }
                val cur = if (d.isNull(5)) "" else d.optString(5, "")
                val updMode = if (d.length() > 6 && !d.isNull(6)) d.optString(6, "") else ""
                val isDelayed = updMode.contains("delayed", ignoreCase = true)
                val srcLabel = when {
                    sym.startsWith("OANDA:") || sym.startsWith("FOREXCOM:") -> "RT-CFD"
                    isDelayed -> "TV-DLY"
                    else -> "TV-RT"
                }

                out[sym] = QuoteTick(
                    name = d.optString(1, "").ifEmpty { d.optString(0, sym) },
                    price = regClose,
                    chg = regChg,
                    pct = regPct,
                    prevClose = regClose - regChg,
                    cur = cur,
                    src = srcLabel,
                    sess = if (isDelayed) "" else "RT"
                )
            }
        } catch (_: Exception) {
        } finally {
            conn.disconnect()
        }
        return out
    }

    /**
     * Fetches 1-minute real-time chart + US Pre/Post market metadata from Yahoo Finance v8 API.
     */
    private fun fetchYahooGlobalChart(symbol: String, range: String, includePrePost: Boolean): ChartResult? {
        val interval = when (range) {
            "1d" -> "1m"
            "5d" -> "15m"
            else -> "1d"
        }
        val prePostParam = if (includePrePost && range == "1d") "&includePrePost=true" else ""
        val url = "https://query1.finance.yahoo.com/v8/finance/chart/${Uri.encode(symbol)}" +
                "?range=${Uri.encode(range)}&interval=$interval$prePostParam"

        val raw = httpGetString(url, maxBytes = 393216, timeoutMs = 8000) ?: return null
        return try {
            val result = JSONObject(raw)
                .optJSONObject("chart")
                ?.optJSONArray("result")
                ?.optJSONObject(0) ?: return null

            val meta = result.optJSONObject("meta") ?: return null
            val regPrice = meta.optDouble("regularMarketPrice", Double.NaN).takeIf { it.isFinite() }
            val prevClose = (meta.optDouble("chartPreviousClose", Double.NaN).takeIf { it.isFinite() })
                ?: (meta.optDouble("previousClose", Double.NaN).takeIf { it.isFinite() })

            val chg = if (regPrice != null && prevClose != null) regPrice - prevClose else 0.0
            val pct = if (regPrice != null && prevClose != null && prevClose != 0.0) (chg / prevClose) * 100.0 else 0.0

            val pts = ArrayList<Double>()
            val closeArr = result.optJSONObject("indicators")
                ?.optJSONArray("quote")
                ?.optJSONObject(0)
                ?.optJSONArray("close")

            if (closeArr != null) {
                for (i in 0 until closeArr.length()) {
                    if (!closeArr.isNull(i)) {
                        val v = closeArr.optDouble(i, Double.NaN)
                        if (v.isFinite()) pts.add(roundSmartVal(v))
                    }
                }
            }

            if (pts.size < 2 && range == "1d") {
                val fb = fetchYahooGlobalChart(symbol, "5d", false)
                if (fb != null && fb.pts.size >= 2) {
                    pts.clear()
                    pts.addAll(fb.pts)
                }
            }

            val prePrice = meta.optDouble("preMarketPrice", Double.NaN).takeIf { it.isFinite() && it > 0.0 }
            val preChg = meta.optDouble("preMarketChange", Double.NaN).takeIf { it.isFinite() }
            val prePct = meta.optDouble("preMarketChangePercent", Double.NaN).takeIf { it.isFinite() }
            val preTime = meta.optLong("preMarketTime", 0L)

            val postPrice = meta.optDouble("postMarketPrice", Double.NaN).takeIf { it.isFinite() && it > 0.0 }
            val postChg = meta.optDouble("postMarketChange", Double.NaN).takeIf { it.isFinite() }
            val postPct = meta.optDouble("postMarketChangePercent", Double.NaN).takeIf { it.isFinite() }
            val postTime = meta.optLong("postMarketTime", 0L)
            val regTime = meta.optLong("regularMarketTime", 0L)

            ChartResult(
                name = meta.optString("shortName", "").ifEmpty { meta.optString("longName", symbol) },
                price = regPrice,
                prevClose = prevClose,
                chg = chg,
                pct = pct,
                cur = meta.optString("currency", ""),
                pts = pts,
                prePrice = prePrice,
                preChg = preChg,
                prePct = prePct,
                preTime = preTime,
                postPrice = postPrice,
                postChg = postChg,
                postPct = postPct,
                postTime = postTime,
                regTime = regTime
            )
        } catch (_: Exception) {
            null
        }
    }

    private fun httpGetString(urlStr: String, maxBytes: Int, timeoutMs: Int): String? {
        val conn = (URL(urlStr).openConnection() as HttpURLConnection).apply {
            instanceFollowRedirects = true
            requestMethod = "GET"
            connectTimeout = (timeoutMs / 2).coerceAtLeast(3500)
            readTimeout = timeoutMs
            useCaches = false
            setRequestProperty("Accept-Encoding", "gzip")
            setRequestProperty("Accept-Language", "ja-JP,ja;q=0.9,en-US;q=0.8")
            setRequestProperty("User-Agent", UA_BROWSER)
        }
        return try {
            if (conn.responseCode != 200) null else readConnString(conn, maxBytes)
        } catch (_: Exception) {
            null
        } finally {
            conn.disconnect()
        }
    }

    private fun readConnString(conn: HttpURLConnection, maxBytes: Int): String? {
        val rawStream: InputStream = conn.inputStream ?: return null
        val enc = conn.contentEncoding?.lowercase(Locale.US) ?: ""
        val decoded = if (enc.contains("gzip")) GZIPInputStream(rawStream) else rawStream
        val bytes = decoded.use { ins ->
            val bos = ByteArrayOutputStream(8192)
            val buf = ByteArray(4096)
            var total = 0
            while (total < maxBytes) {
                val n = ins.read(buf, 0, (maxBytes - total).coerceAtMost(buf.size))
                if (n < 0) break
                if (n > 0) {
                    bos.write(buf, 0, n)
                    total += n
                }
            }
            bos.toByteArray()
        }
        return bytes.toString(Charsets.UTF_8)
    }

    private fun parseJpNum(s: String?): Double? {
        if (s == null) return null
        val cleaned = s.replace(",", "")
            .replace("+", "")
            .replace("%", "")
            .replace("円", "")
            .replace(" ", "")
            .trim()
        if (cleaned.isEmpty() || cleaned == "---" || cleaned == "--" || cleaned == "-") return null
        return cleaned.toDoubleOrNull()
    }

    /**
     * Keeps ASCII names crisp on X4 Pro's stock fonts while allowing clean Japanese names if short.
     */
    private fun cleanAsciiSafeName(raw: String, fallback: String): String {
        val trimmed = raw.replace(Regex("\\s+"), " ")
            .replace("(株)", "")
            .replace("株式会社", "")
            .trim()
        if (trimmed.isEmpty()) return fallback
        return if (trimmed.length > 22) trimmed.substring(0, 22) else trimmed
    }

    private fun validateRange(r: String): String {
        return if (r == "5d" || r == "1mo" || r == "3mo") r else "1d"
    }

    private fun downsample(arr: List<Double>, maxPts: Int): List<Double> {
        if (arr.size <= maxPts) return arr
        val out = ArrayList<Double>(maxPts)
        val step = (arr.size - 1).toDouble() / (maxPts - 1).toDouble()
        for (i in 0 until maxPts) {
            out.add(arr[(i * step).roundToInt().coerceIn(0, arr.size - 1)])
        }
        return out
    }

    private fun roundSmartVal(v: Double): Double {
        val a = abs(v)
        return when {
            a >= 1000.0 -> (v * 10.0).roundToInt() / 10.0
            a >= 10.0 -> (v * 100.0).roundToInt() / 100.0
            else -> (v * 1000.0).roundToInt() / 1000.0
        }
    }

    private fun JSONObject.putRoundSmart(key: String, v: Double?) {
        if (v == null || !v.isFinite()) {
            put(key, JSONObject.NULL)
        } else {
            put(key, roundSmartVal(v))
        }
    }

    private fun JSONObject.putRoundFixed(key: String, v: Double?, digits: Int) {
        if (v == null || !v.isFinite()) {
            put(key, JSONObject.NULL)
        } else {
            val f = 10.0.pow(digits.toDouble())
            put(key, (v * f).roundToInt() / f)
        }
    }

    private fun wrapPayload(rawBytes: ByteArray, wantZlib: Boolean, hostSummary: String): HttpProxyEngine.ProxyResponse {
        if (wantZlib && rawBytes.size >= 140) {
            val compressed = HttpProxyEngine.compressZlib(rawBytes)
            if (compressed.size + 8 < rawBytes.size) {
                return HttpProxyEngine.ProxyResponse(
                    httpStatus = 200,
                    payload = compressed,
                    rawLength = rawBytes.size,
                    isZlib = true,
                    isError = false,
                    hostSummary = hostSummary
                )
            }
        }
        return HttpProxyEngine.ProxyResponse(
            httpStatus = 200,
            payload = rawBytes,
            rawLength = rawBytes.size,
            isZlib = false,
            isError = false,
            hostSummary = hostSummary
        )
    }

    private fun errorJson(msg: String): HttpProxyEngine.ProxyResponse {
        val bytes = JSONObject().apply {
            put("ok", false)
            put("ver", ENGINE_VER)
            put("error", msg)
        }.toString().toByteArray(Charsets.UTF_8)
        return HttpProxyEngine.ProxyResponse(
            httpStatus = 200,
            payload = bytes,
            rawLength = bytes.size,
            isZlib = false,
            isError = false,
            hostSummary = "rt-stock(err)"
        )
    }
}
