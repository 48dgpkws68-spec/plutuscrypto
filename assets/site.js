/* Plutus Crypto — QR encoder (byte mode, error correction level M, versions 1-10).
   Written from the spec so the demo shows a QR that actually scans, not a picture of one. */
(function (global) {
  "use strict";

  // ---- GF(256) with primitive polynomial 0x11d -------------------------------
  var EXP = new Uint8Array(512), LOG = new Uint8Array(256);
  (function () {
    for (var i = 0, x = 1; i < 255; i++) {
      EXP[i] = x; LOG[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= 0x11d;
    }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();

  function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function generatorPoly(degree) {
    var poly = [1];
    for (var d = 0; d < degree; d++) {
      var next = new Array(poly.length + 1).fill(0);
      for (var i = 0; i < poly.length; i++) {
        next[i] ^= poly[i];
        next[i + 1] ^= mul(poly[i], EXP[d]);
      }
      poly = next;
    }
    return poly;
  }

  function eccBytes(data, count) {
    var gen = generatorPoly(count);
    var rest = new Array(count).fill(0);
    for (var i = 0; i < data.length; i++) {
      var factor = data[i] ^ rest[0];
      rest.shift();
      rest.push(0);
      for (var j = 0; j < count; j++) rest[j] ^= mul(gen[j + 1], factor);
    }
    return rest;
  }

  // ---- version tables (error correction level M) -----------------------------
  // [byte capacity, ecc codewords per block, [ [blocks, data codewords], ... ] ]
  var VERSIONS = {
    1:  [14,  10, [[1, 16]]],
    2:  [26,  16, [[1, 28]]],
    3:  [42,  26, [[1, 44]]],
    4:  [62,  18, [[2, 32]]],
    5:  [84,  24, [[2, 43]]],
    6:  [106, 16, [[4, 27]]],
    7:  [122, 18, [[4, 31]]],
    8:  [152, 22, [[2, 38], [2, 39]]],
    9:  [180, 22, [[3, 36], [2, 37]]],
    10: [213, 26, [[4, 43], [1, 44]]]
  };

  var ALIGN = {
    1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30],
    6: [6, 34], 7: [6, 22, 38], 8: [6, 24, 42], 9: [6, 26, 46], 10: [6, 28, 50]
  };

  function utf8(text) {
    var out = [], enc = unescape(encodeURIComponent(text));
    for (var i = 0; i < enc.length; i++) out.push(enc.charCodeAt(i));
    return out;
  }

  function pickVersion(byteCount) {
    for (var v = 1; v <= 10; v++) if (byteCount <= VERSIONS[v][0]) return v;
    throw new Error("QR payload too long for this encoder");
  }

  // ---- bit stream ------------------------------------------------------------
  function BitBuffer() { this.bits = []; }
  BitBuffer.prototype.put = function (value, length) {
    for (var i = length - 1; i >= 0; i--) this.bits.push((value >>> i) & 1);
  };
  BitBuffer.prototype.bytes = function () {
    var out = [];
    for (var i = 0; i < this.bits.length; i += 8) {
      var b = 0;
      for (var j = 0; j < 8; j++) b = (b << 1) | (this.bits[i + j] || 0);
      out.push(b);
    }
    return out;
  };

  function buildCodewords(bytes, version) {
    var spec = VERSIONS[version];
    var totalData = spec[2].reduce(function (sum, g) { return sum + g[0] * g[1]; }, 0);
    var buf = new BitBuffer();
    buf.put(4, 4);                                   // byte mode
    buf.put(bytes.length, version < 10 ? 8 : 16);    // character count
    for (var i = 0; i < bytes.length; i++) buf.put(bytes[i], 8);
    var room = totalData * 8;
    for (var t = 0; t < 4 && buf.bits.length < room; t++) buf.bits.push(0);
    while (buf.bits.length % 8) buf.bits.push(0);
    var data = buf.bytes();
    var pad = [0xEC, 0x11], p = 0;
    while (data.length < totalData) data.push(pad[p++ % 2]);

    // split into blocks, compute ecc, then interleave
    var blocks = [], pos = 0;
    spec[2].forEach(function (group) {
      for (var b = 0; b < group[0]; b++) {
        var chunk = data.slice(pos, pos + group[1]);
        pos += group[1];
        blocks.push({ data: chunk, ecc: eccBytes(chunk, spec[1]) });
      }
    });
    var out = [], maxData = Math.max.apply(null, blocks.map(function (b) { return b.data.length; }));
    for (var c = 0; c < maxData; c++)
      blocks.forEach(function (b) { if (c < b.data.length) out.push(b.data[c]); });
    for (var e = 0; e < spec[1]; e++)
      blocks.forEach(function (b) { out.push(b.ecc[e]); });
    return out;
  }

  // ---- matrix ----------------------------------------------------------------
  function newMatrix(size) {
    var m = [];
    for (var i = 0; i < size; i++) m.push(new Array(size).fill(null));
    return m;
  }

  function placeFinder(m, row, col) {
    for (var r = -1; r <= 7; r++) {
      for (var c = -1; c <= 7; c++) {
        var rr = row + r, cc = col + c;
        if (rr < 0 || cc < 0 || rr >= m.length || cc >= m.length) continue;
        var edge = (r >= 0 && r <= 6 && (c === 0 || c === 6)) ||
                   (c >= 0 && c <= 6 && (r === 0 || r === 6));
        var core = r >= 2 && r <= 4 && c >= 2 && c <= 4;
        m[rr][cc] = edge || core ? 1 : 0;
      }
    }
  }

  // The three centres that would land on a finder pattern are omitted. Centres that
  // merely cross the timing line are placed normally: their modules agree with it.
  function skipAlignment(row, col, last) {
    return (row === 6 && col === 6) || (row === 6 && col === last) || (row === last && col === 6);
  }

  function placeAlignment(m, version) {
    var centers = ALIGN[version], last = m.length - 7;
    for (var a = 0; a < centers.length; a++) {
      for (var b = 0; b < centers.length; b++) {
        var row = centers[a], col = centers[b];
        if (skipAlignment(row, col, last)) continue;
        for (var r = -2; r <= 2; r++)
          for (var c = -2; c <= 2; c++)
            m[row + r][col + c] = (Math.max(Math.abs(r), Math.abs(c)) !== 1) ? 1 : 0;
      }
    }
  }

  function reserveFormat(m) {
    var size = m.length;
    for (var i = 0; i < 9; i++) {
      if (m[8][i] === null) m[8][i] = 0;
      if (m[i][8] === null) m[i][8] = 0;
    }
    for (var j = 0; j < 8; j++) {
      if (m[8][size - 1 - j] === null) m[8][size - 1 - j] = 0;
      if (m[size - 1 - j][8] === null) m[size - 1 - j][8] = 0;
    }
    m[size - 8][8] = 1; // dark module
  }

  function placeVersionInfo(m, version) {
    if (version < 7) return;
    // BCH(18,6) with generator 0x1F25
    var bits = version << 12, r = bits;
    for (var k = 0; k < 6; k++) if (r >>> (17 - k) & 1) r ^= 0x1F25 << (5 - k);
    var info = bits | (r & 0xFFF);
    var size = m.length;
    for (var b = 0; b < 18; b++) {
      var bit = (info >>> b) & 1;
      m[Math.floor(b / 3)][size - 11 + (b % 3)] = bit;
      m[size - 11 + (b % 3)][Math.floor(b / 3)] = bit;
    }
  }

  function placeData(m, codewords) {
    var size = m.length, dir = -1, row = size - 1, bitIndex = 0;
    for (var col = size - 1; col > 0; col -= 2) {
      if (col === 6) col--;                       // skip the vertical timing line
      for (;;) {
        for (var c = 0; c < 2; c++) {
          var cc = col - c;
          if (m[row][cc] === null) {
            var byte = codewords[bitIndex >>> 3];
            var bit = byte === undefined ? 0 : (byte >>> (7 - (bitIndex & 7))) & 1;
            m[row][cc] = bit;
            bitIndex++;
          }
        }
        row += dir;
        if (row < 0 || row >= size) { row -= dir; dir = -dir; break; }
      }
    }
  }

  var MASKS = [
    function (r, c) { return (r + c) % 2 === 0; },
    function (r) { return r % 2 === 0; },
    function (r, c) { return c % 3 === 0; },
    function (r, c) { return (r + c) % 3 === 0; },
    function (r, c) { return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0; },
    function (r, c) { return ((r * c) % 2) + ((r * c) % 3) === 0; },
    function (r, c) { return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0; },
    function (r, c) { return (((r + c) % 2) + ((r * c) % 3)) % 2 === 0; }
  ];

  function isFunction(version, size, r, c) {
    if (r <= 8 && c <= 8) return true;
    if (r <= 8 && c >= size - 8) return true;
    if (r >= size - 8 && c <= 8) return true;
    if (r === 6 || c === 6) return true;
    var centers = ALIGN[version], last = size - 7;
    for (var a = 0; a < centers.length; a++)
      for (var b = 0; b < centers.length; b++) {
        var ar = centers[a], ac = centers[b];
        if (skipAlignment(ar, ac, last)) continue;
        if (Math.abs(r - ar) <= 2 && Math.abs(c - ac) <= 2) return true;
      }
    if (version >= 7 && ((r < 6 && c >= size - 11) || (c < 6 && r >= size - 11))) return true;
    return false;
  }

  function formatBits(mask) {
    var data = (0x00 << 3) | mask;              // 00 = error correction level M
    var rem = data << 10;
    for (var i = 0; i < 5; i++) if (rem >>> (14 - i) & 1) rem ^= 0x537 << (4 - i);
    return ((data << 10) | (rem & 0x3FF)) ^ 0x5412;
  }

  function applyFormat(m, mask) {
    var bits = formatBits(mask), size = m.length;
    for (var i = 0; i < 15; i++) {
      var bit = (bits >>> i) & 1;
      if (i < 6) m[i][8] = bit;
      else if (i === 6) m[7][8] = bit;
      else if (i === 7) m[8][8] = bit;
      else if (i === 8) m[8][7] = bit;
      else m[8][14 - i] = bit;

      if (i < 8) m[8][size - 1 - i] = bit;
      else m[size - 15 + i][8] = bit;
    }
    m[size - 8][8] = 1;
  }

  function penalty(m) {
    var size = m.length, score = 0, i, j, run, dark = 0;
    for (i = 0; i < size; i++) {
      run = 1;
      for (j = 1; j < size; j++) {
        if (m[i][j] === m[i][j - 1]) { run++; }
        else { if (run >= 5) score += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) score += 3 + (run - 5);
      run = 1;
      for (j = 1; j < size; j++) {
        if (m[j][i] === m[j - 1][i]) { run++; }
        else { if (run >= 5) score += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) score += 3 + (run - 5);
    }
    for (i = 0; i < size - 1; i++)
      for (j = 0; j < size - 1; j++) {
        var v = m[i][j];
        if (v === m[i][j + 1] && v === m[i + 1][j] && v === m[i + 1][j + 1]) score += 3;
      }
    var pattern = [1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0];
    function matches(get) {
      var hits = 0;
      for (var s = 0; s + 11 <= size; s++) {
        var ok = true, okRev = true;
        for (var k = 0; k < 11; k++) {
          if (get(s + k) !== pattern[k]) ok = false;
          if (get(s + k) !== pattern[10 - k]) okRev = false;
        }
        if (ok) hits++;
        if (okRev) hits++;
      }
      return hits;
    }
    for (i = 0; i < size; i++) {
      (function (row) { score += 40 * matches(function (k) { return m[row][k]; }); })(i);
      (function (col) { score += 40 * matches(function (k) { return m[k][col]; }); })(i);
    }
    for (i = 0; i < size; i++) for (j = 0; j < size; j++) if (m[i][j]) dark++;
    var percent = (dark * 100) / (size * size);
    score += Math.floor(Math.abs(percent - 50) / 5) * 10;
    return score;
  }

  /** Returns a size x size array of 0/1 for the given text. */
  function encode(text, forcedMask) {
    var bytes = utf8(String(text));
    var version = pickVersion(bytes.length);
    var size = version * 4 + 17;
    var codewords = buildCodewords(bytes, version);

    var base = newMatrix(size);
    placeFinder(base, 0, 0);
    placeFinder(base, 0, size - 7);
    placeFinder(base, size - 7, 0);
    for (var i = 8; i < size - 8; i++) {
      base[6][i] = i % 2 === 0 ? 1 : 0;
      base[i][6] = i % 2 === 0 ? 1 : 0;
    }
    placeAlignment(base, version);
    placeVersionInfo(base, version);
    reserveFormat(base);
    placeData(base, codewords);

    var best = null, bestScore = Infinity;
    var from = forcedMask == null ? 0 : forcedMask;
    var to = forcedMask == null ? 7 : forcedMask;
    for (var mask = from; mask <= to; mask++) {
      var candidate = base.map(function (row) { return row.slice(); });
      for (var r = 0; r < size; r++)
        for (var c = 0; c < size; c++)
          if (!isFunction(version, size, r, c) && MASKS[mask](r, c)) candidate[r][c] ^= 1;
      applyFormat(candidate, mask);
      var s = penalty(candidate);
      if (s < bestScore) { bestScore = s; best = candidate; }
    }
    return best;
  }

  /** Draws the code into a canvas, styled for the Plutus palette. */
  function draw(canvas, text, options) {
    var opts = options || {};
    var matrix = encode(text);
    var size = matrix.length;
    var quiet = opts.quiet == null ? 3 : opts.quiet;
    var scale = Math.max(1, Math.floor((opts.pixels || 320) / (size + quiet * 2)));
    var edge = (size + quiet * 2) * scale;
    var ratio = global.devicePixelRatio || 1;
    canvas.width = edge * ratio;
    canvas.height = edge * ratio;
    canvas.style.width = edge + "px";
    canvas.style.height = edge + "px";
    var ctx = canvas.getContext("2d");
    ctx.scale(ratio, ratio);
    ctx.fillStyle = opts.background || "#F7F4FB";
    ctx.fillRect(0, 0, edge, edge);
    ctx.fillStyle = opts.foreground || "#14032B";
    for (var r = 0; r < size; r++)
      for (var c = 0; c < size; c++)
        if (matrix[r][c])
          ctx.fillRect((c + quiet) * scale, (r + quiet) * scale, scale, scale);
    return { modules: size, pixels: edge };
  }

  global.PlutusQR = { encode: encode, draw: draw };
})(window);

/* Content and demo data for the Plutus Crypto site.
   Rates are illustrative and drift on a seeded random walk so the demo behaves
   like a market without pretending to be a price feed. */

const ASSETS = [
  { sym: "BTC",  name: "Bitcoin",   network: "Bitcoin",        tint: "#F7931A", rate: 58420,  conf: 2,  dp: 8, prefix: "tb1q", addr: "bech32", len: 38 },
  { sym: "ETH",  name: "Ethereum",  network: "Ethereum",       tint: "#8FA2FF", rate: 2410,   conf: 12, dp: 6, prefix: "0x",   addr: "hex",    len: 40 },
  { sym: "USDT", name: "Tether",    network: "Tron TRC20",     tint: "#26A17B", rate: 0.92,   conf: 19, dp: 2, prefix: "T",    addr: "base58", len: 33 },
  { sym: "USDT", name: "Tether",    network: "Ethereum ERC20", tint: "#26A17B", rate: 0.92,   conf: 12, dp: 2, prefix: "0x",   addr: "hex",    len: 40 },
  { sym: "USDC", name: "USD Coin",  network: "Solana",         tint: "#5A9BEA", rate: 0.92,   conf: 32, dp: 2, prefix: "",     addr: "base58", len: 44 },
  { sym: "USDC", name: "USD Coin",  network: "Polygon",        tint: "#5A9BEA", rate: 0.92,   conf: 30, dp: 2, prefix: "0x",   addr: "hex",    len: 40 },
  { sym: "XRP",  name: "XRP",       network: "XRP Ledger",     tint: "#D6DEE6", rate: 0.54,   conf: 1,  dp: 4, prefix: "r",    addr: "base58", len: 32 },
  { sym: "SOL",  name: "Solana",    network: "Solana",         tint: "#14F195", rate: 132.40, conf: 32, dp: 5, prefix: "",     addr: "base58", len: 44 },
  { sym: "LTC",  name: "Litecoin",  network: "Litecoin",       tint: "#C8C8C8", rate: 68.90,  conf: 4,  dp: 6, prefix: "ltc1", addr: "bech32", len: 38 },
  { sym: "BCH",  name: "Bitcoin Cash", network: "Bitcoin Cash", tint: "#8DC351", rate: 342.10, conf: 3, dp: 6, prefix: "q",    addr: "bech32", len: 41 },
  { sym: "DASH", name: "Dash",      network: "Dash",           tint: "#3FA9F5", rate: 24.80,  conf: 3,  dp: 5, prefix: "X",    addr: "base58", len: 33 },
  { sym: "POL",  name: "Polygon",   network: "Polygon",        tint: "#A26BF0", rate: 0.41,   conf: 30, dp: 4, prefix: "0x",   addr: "hex",    len: 40 },
  { sym: "TRX",  name: "Tron",      network: "Tron",           tint: "#FF5A5E", rate: 0.11,   conf: 19, dp: 3, prefix: "T",    addr: "base58", len: 33 }
];

const FIAT = { EUR: { symbol: "€", rate: 1 }, USD: { symbol: "$", rate: 1.09 }, GBP: { symbol: "£", rate: 0.84 } };

const PRODUCTS = [
  { icon: "cart", title: "Hosted checkout",
    text: "Send the customer to a payment page carrying your name and your colours. Nothing to build, nothing to maintain." },
  { icon: "code", title: "Drop in widget",
    text: "One script tag inside your existing checkout. The customer never leaves your site." },
  { icon: "link", title: "Payment links and invoices",
    text: "Create a link in the dashboard and send it by email, chat or QR. Useful long before you have an integration." },
  { icon: "terminal", title: "In store terminal",
    text: "Take crypto at the counter from a phone, a tablet or a dedicated terminal. The customer scans, you see it land." },
  { icon: "send", title: "Payouts and refunds",
    text: "Send crypto or stablecoin back out to a customer, a supplier or a contractor, one at a time or in batches." },
  { icon: "swap", title: "On ramp and off ramp",
    text: "Convert between fiat and crypto in both directions, so you can hold a working balance in either." },
  { icon: "chart", title: "Merchant dashboard",
    text: "Payments, settlements, refunds and fees in one ledger, with exports your accountant will accept." },
  { icon: "label", title: "Recurring billing",
    text: "Bill the same customer every month against a saved reference, and chase the ones that go unpaid." }
];

const SOLUTIONS = [
  { title: "Ecommerce", text: "High ticket goods where card fees and fraud losses hurt most, and where buyers already hold crypto." },
  { title: "Gaming and iGaming", text: "Instant deposits from any country, with payouts back to the same wallet the player deposited from." },
  { title: "Travel", text: "Bookings across borders without card declines, currency conversion or a three day settlement wait." },
  { title: "Luxury retail", text: "Single transactions above card limits, cleared in minutes and impossible to charge back." },
  { title: "Trading and FX", text: "Fund and defund accounts on chain while keeping the ledger in the currency you report in." },
  { title: "Remittances", text: "Move value to markets where the correspondent banking route is slow, costly or simply closed." },
  { title: "B2B trade", text: "Invoices settled between countries without waiting for a wire to clear on a Friday afternoon." },
  { title: "Marketplaces", text: "Split incoming payments across sellers, and pay them out in the asset each one prefers." }
];

const SECURITY = [
  { title: "Screened on arrival", text: "Every incoming transaction is checked against sanctions and risk scoring before it is credited." },
  { title: "Travel Rule ready", text: "Originator and beneficiary information is exchanged where the threshold applies." },
  { title: "No card data", text: "Nothing that touches a card network touches us, so your PCI scope does not grow." },
  { title: "No chargebacks", text: "A confirmed blockchain payment is final. There is no reversal window to defend." },
  { title: "Signed webhooks", text: "Every callback carries a signature and a timestamp, with IP allow lists and scoped keys." },
  { title: "Roles and audit", text: "Per user permissions, two factor sign in, and an exportable record of every action." }
];

const PRICE_RATE = 3;   // percent per transaction, everything included

const PRICE_INCLUDED = [
  "Hosted checkout, payment links and the drop in widget",
  "In store terminal and the full API",
  "Every asset and network we support",
  "Conversion to euros, pounds or dollars",
  "All blockchain network fees",
  "Next business day settlement to your bank",
  "Dashboard, exports, webhooks and payouts",
  "No monthly fee, no setup fee, no chargeback fee"
];

const FAQ = [
  { q: "What does it cost?",
    a: "Three percent per transaction, and that is the whole bill. Conversion, blockchain network fees and settlement to your bank are inside it. There is no monthly fee, no setup fee and no chargeback fee, because a confirmed blockchain payment cannot be reversed." },
  { q: "Can I pass the cost on to my customer?",
    a: "Yes, and most merchants do. You set a surcharge for paying in crypto at checkout. If you add four percent, the three percent is covered and just under one percent stays with you on every crypto order. Add nothing and you simply absorb the three percent, the same way you absorb card fees today." },
  { q: "Do I have to hold any crypto?",
    a: "No. The default is to convert at the moment of payment and pay you in euros, pounds or dollars. Holding a crypto or stablecoin balance is optional, and most merchants only do it because they want to make payouts or refunds in kind." },
  { q: "What happens if the price moves while the customer is paying?",
    a: "The quote is locked for fifteen minutes. Inside that window the exchange risk is ours. If the customer pays after it expires, the payment is re quoted at the new rate and either party can walk away." },
  { q: "What if a customer sends too little or too much?",
    a: "You see the shortfall or the surplus in the dashboard and decide per case: accept it, ask for the difference, or refund the whole amount back to the sending address in one click." },
  { q: "How fast is settlement, really?",
    a: "Crypto confirmation takes seconds to minutes depending on the network. The fiat payout runs on the banking day, so a payment taken on Tuesday reaches your account on Wednesday." },
  { q: "Can my customers pay from an exchange account?",
    a: "Yes. Any wallet or exchange that can send to an address works, including hardware wallets. There is nothing for the customer to install and no account to create with us." },
  { q: "Which countries can you onboard?",
    a: "Most of the European Economic Area, the United Kingdom and a growing list beyond it. Regulated sectors such as gaming need a licence check first, so tell us your market when you get in touch." }
];

const CODE = {
  cURL: `curl https://api.plutuscrypto.com/v1/payments \\
  -u pk_live_9f2c:sk_live_•••• \\
  -d amount=189.00 \\
  -d currency=EUR \\
  -d reference=INV-2026-0841 \\
  -d callback_url=https://atlaswatches.com/hooks/plutus`,
  Node: `const plutus = require("@plutuscrypto/node")(process.env.PLUTUS_SECRET);

const payment = await plutus.payments.create({
  amount: 189.00,
  currency: "EUR",
  reference: "INV-2026-0841",
  callback_url: "https://atlaswatches.com/hooks/plutus"
});

res.redirect(payment.checkout_url);`,
  Python: `import plutus

plutus.api_key = os.environ["PLUTUS_SECRET"]

payment = plutus.Payment.create(
    amount="189.00",
    currency="EUR",
    reference="INV-2026-0841",
    callback_url="https://atlaswatches.com/hooks/plutus",
)

return redirect(payment.checkout_url)`,
  PHP: `<?php
$plutus = new \\Plutus\\Client(getenv('PLUTUS_SECRET'));

$payment = $plutus->payments->create([
  'amount'       => '189.00',
  'currency'     => 'EUR',
  'reference'    => 'INV-2026-0841',
  'callback_url' => 'https://atlaswatches.com/hooks/plutus',
]);

header('Location: ' . $payment->checkout_url);`
};

const WEBHOOK_SAMPLE = `{
  "event": "payment.confirmed",
  "payment_id": "pay_7F3K92QX",
  "reference": "INV-2026-0841",
  "status": "confirmed",
  "amount": { "value": "189.00", "currency": "EUR" },
  "received": { "value": "0.00184215", "asset": "BTC", "network": "bitcoin" },
  "rate": { "value": "102596.00", "locked_at": "2026-08-05T14:22:08Z" },
  "confirmations": 2,
  "tx_hash": "b7c1…9e42",
  "settlement": { "date": "2026-08-06", "method": "sepa" }
}`;

/* Seed data for the dashboard. Deterministic so the page always opens the same way. */
const SEED_TX = [
  { ref: "INV-2026-0840", sym: "USDT", net: "Tron TRC20", status: "settled",   crypto: "1,480.00", fiat: "1,361.60", when: "12 min ago" },
  { ref: "ORD-88213",     sym: "BTC",  net: "Bitcoin",    status: "confirmed", crypto: "0.00612900", fiat: "358.05", when: "37 min ago" },
  { ref: "INV-2026-0839", sym: "ETH",  net: "Ethereum",   status: "settled",   crypto: "0.412000",  fiat: "992.92",  when: "1 h ago" },
  { ref: "ORD-88207",     sym: "SOL",  net: "Solana",     status: "settled",   crypto: "3.11200",   fiat: "412.03",  when: "2 h ago" },
  { ref: "INV-2026-0837", sym: "USDC", net: "Polygon",    status: "refunded",  crypto: "240.00",    fiat: "220.80",  when: "3 h ago" },
  { ref: "ORD-88198",     sym: "XRP",  net: "XRP Ledger", status: "settled",   crypto: "1,850.0000", fiat: "999.00", when: "4 h ago" },
  { ref: "INV-2026-0836", sym: "BTC",  net: "Bitcoin",    status: "settled",   crypto: "0.01044100", fiat: "610.00", when: "6 h ago" }
];

const VOLUME_30D = [
  18420, 21100, 16850, 24300, 27650, 19980, 22140, 31200, 28760, 24500,
  33810, 29940, 26120, 35400, 41250, 38700, 32950, 30480, 44120, 47800,
  41360, 39250, 52400, 48900, 45720, 58100, 54300, 49850, 62400, 67150
];

const ASSET_SPLIT = [
  { sym: "USDT", pct: 34, tint: "#26A17B" },
  { sym: "BTC",  pct: 26, tint: "#F7931A" },
  { sym: "ETH",  pct: 17, tint: "#8FA2FF" },
  { sym: "USDC", pct: 12, tint: "#5A9BEA" },
  { sym: "SOL",  pct: 7,  tint: "#14F195" },
  { sym: "Other", pct: 4, tint: "#A294BC" }
];

const ICONS = {
  cart: '<path d="M2 3h3l2.4 11.2a2 2 0 0 0 2 1.6h7.2a2 2 0 0 0 2-1.6L21 7H6"/><circle cx="9" cy="20" r="1.4"/><circle cx="18" cy="20" r="1.4"/>',
  code: '<path d="M9 6 3 12l6 6M15 6l6 6-6 6"/>',
  link: '<path d="M10 14a4 4 0 0 0 5.7 0l3-3a4 4 0 1 0-5.7-5.7L11.5 6.8"/><path d="M14 10a4 4 0 0 0-5.7 0l-3 3a4 4 0 1 0 5.7 5.7l1.4-1.4"/>',
  terminal: '<rect x="4" y="2" width="16" height="20" rx="2"/><path d="M8 7h8M8 11h8M9 17h6"/>',
  send: '<path d="m21 3-9.5 9.5M21 3l-6.5 18-4-8-8-4L21 3Z"/>',
  swap: '<path d="M7 4v13m0 0-3-3m3 3 3-3M17 20V7m0 0-3 3m3-3 3 3"/>',
  chart: '<path d="M4 20V10M10 20V4M16 20v-7M22 20H2"/>',
  label: '<path d="M3 7a2 2 0 0 1 2-2h7l9 9-9 9-9-9V7Z"/><circle cx="8.5" cy="9.5" r="1.2"/>',
  check: '<path d="m4 12 5 5L20 6"/>'
};

/* ----------------------------------------------------------- developers --- */

const ENDPOINTS = [
  { verb: "POST",   path: "/v1/payments",                 text: "Create a payment. Returns a checkout URL, a payment id and the locked quote per asset." },
  { verb: "GET",    path: "/v1/payments/{id}",            text: "Fetch one payment with its current status, confirmations and settlement details." },
  { verb: "GET",    path: "/v1/payments",                 text: "List payments, filterable by status, reference, asset and date range. Paginated." },
  { verb: "POST",   path: "/v1/payments/{id}/cancel",     text: "Cancel a payment that has not been seen on chain yet. Expired quotes cancel themselves." },
  { verb: "POST",   path: "/v1/payments/{id}/refund",     text: "Refund all or part of a confirmed payment to the sending address, or to an address you supply." },
  { verb: "POST",   path: "/v1/links",                    text: "Create a reusable or single use payment link with an amount, a reference and an expiry." },
  { verb: "POST",   path: "/v1/payouts",                  text: "Send crypto or stablecoin to an external address, singly or as a batch of up to 500." },
  { verb: "GET",    path: "/v1/payouts/{id}",             text: "Fetch a payout with its on chain transaction hash once it has been broadcast." },
  { verb: "GET",    path: "/v1/balances",                 text: "Your fiat and stablecoin balances, what is pending settlement and what is reserved for payouts." },
  { verb: "GET",    path: "/v1/settlements",              text: "Every bank payout we have made, with the payments it contains and the fee it carried." },
  { verb: "GET",    path: "/v1/rates",                    text: "Indicative rates for every supported asset against EUR, USD and GBP. Quotes lock at payment creation." },
  { verb: "POST",   path: "/v1/webhooks",                 text: "Register a callback URL. Returns the signing secret you will use to verify every delivery." },
  { verb: "DELETE", path: "/v1/webhooks/{id}",            text: "Remove a webhook endpoint. Pending deliveries to it are dropped." },
  { verb: "GET",    path: "/v1/events",                   text: "Replay the event log for your account, useful after downtime on your side." }
];

const WEBHOOK_EVENTS = [
  { name: "payment.created",     text: "A payment was created and a quote locked. Nothing has been paid yet." },
  { name: "payment.detected",    text: "A transaction to the payment address was seen on the network, before any confirmation." },
  { name: "payment.confirming",  text: "The first confirmation arrived. Sent again as the count grows, up to the threshold." },
  { name: "payment.confirmed",   text: "The required confirmation depth was reached. Safe to release goods." },
  { name: "payment.underpaid",   text: "Less arrived than quoted. Includes the shortfall so you can decide what to do." },
  { name: "payment.overpaid",    text: "More arrived than quoted. The surplus is held for you to refund or keep." },
  { name: "payment.expired",     text: "The quote window closed with nothing received. The address is retired." },
  { name: "payment.refunded",    text: "A refund was broadcast, with its transaction hash." },
  { name: "payout.sent",         text: "A payout left your balance and was broadcast to the network." },
  { name: "payout.failed",       text: "A payout could not be broadcast. Includes the reason and whether funds were returned." },
  { name: "settlement.scheduled", text: "Confirmed payments were bundled into a bank payout for the next business day." },
  { name: "settlement.paid",     text: "The bank payout was executed, with the reference that will appear on your statement." }
];

const ERROR_CODES = [
  { status: 400, code: "invalid_request",     text: "A field is missing or malformed. The message names the field." },
  { status: 401, code: "unauthenticated",     text: "The API key is missing, revoked or belongs to the other environment." },
  { status: 403, code: "forbidden",           text: "The key is valid but not allowed to do this. Check its scopes." },
  { status: 404, code: "not_found",           text: "No resource with that id on this account." },
  { status: 409, code: "already_final",       text: "You tried to change a payment that is confirmed, expired or refunded." },
  { status: 422, code: "unsupported_asset",   text: "The asset or network is not enabled for your account." },
  { status: 422, code: "below_minimum",       text: "The amount is under the minimum for that asset after network fees." },
  { status: 429, code: "rate_limited",        text: "Too many requests. The Retry-After header says how long to wait." },
  { status: 500, code: "internal",            text: "Something failed on our side. Safe to retry with the same idempotency key." }
];

const SDKS = [
  { name: "Node.js",  pkg: "@plutuscrypto/node",   cmd: "npm install @plutuscrypto/node" },
  { name: "Python",   pkg: "plutuscrypto",         cmd: "pip install plutuscrypto" },
  { name: "PHP",      pkg: "plutuscrypto/sdk",     cmd: "composer require plutuscrypto/sdk" },
  { name: "Ruby",     pkg: "plutuscrypto",         cmd: "gem install plutuscrypto" },
  { name: "Go",       pkg: "github.com/plutuscrypto/go", cmd: "go get github.com/plutuscrypto/go" }
];

/* Plutus Crypto — page behaviour, checkout simulation and dashboard.
   The checkout below is a faithful simulation: it quotes, locks, watches and
   settles exactly like the real flow, but nothing leaves the browser. */
(function () {
  "use strict";

  var $ = function (sel, root) { return (root || document).querySelector(sel); };
  var $$ = function (sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); };
  var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  function el(tag, attrs, html) {
    var node = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function (k) {
      if (k === "class") node.className = attrs[k];
      else if (k === "style") node.setAttribute("style", attrs[k]);
      else node.setAttribute(k, attrs[k]);
    });
    if (html != null) node.innerHTML = html;
    return node;
  }

  function icon(name) {
    return '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" ' +
           'stroke-linecap="round" stroke-linejoin="round">' + (ICONS[name] || "") + "</svg>";
  }

  function money(value, currency) {
    var f = FIAT[currency] || FIAT.EUR;
    return f.symbol + value.toLocaleString("en-GB", { minimumFractionDigits: 2, maximumFractionDigits: 2 });
  }

  function crypto(value, dp) {
    return value.toLocaleString("en-GB", { minimumFractionDigits: dp, maximumFractionDigits: dp });
  }

  function clock() {
    return new Date().toLocaleTimeString("en-GB", { hour12: false });
  }

  /* --------------------------------------------------------------- chrome -- */

  function chrome() {
    var yr = $("#year");
    if (yr) yr.textContent = String(new Date().getFullYear());

    leadForm();
  }

  /* ------------------------------------------------------------- lead form -- */

  // Where the enquiries land. FormSubmit relays them to this inbox; swapping the
  // address is the only change needed to send them somewhere else. The mailbox has
  // to be able to receive mail, otherwise the confirmation FormSubmit sends bounces
  // and nothing is ever delivered.
  var LEAD_INBOX = "info@plutuscrypto.com";

  function leadForm() {
    var form = $("#leadForm");
    if (!form) return;
    var note = $("#formNote");

    function say(text, colour) {
      note.textContent = text;
      note.style.color = colour;
    }

    form.addEventListener("submit", function (e) {
      e.preventDefault();
      var data = {
        name: form.name.value.trim(),
        company: form.company.value.trim(),
        email: form.email.value.trim(),
        volume: form.volume.value,
        message: form.message.value.trim()
      };
      if (!data.name || !data.company || !/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(data.email)) {
        say("Fill in your name, company and a valid work email so we can reply", "var(--dead)");
        return;
      }

      var button = form.querySelector("button[type=submit]");
      button.disabled = true;
      say("Sending", "var(--muted)");

      fetch("https://formsubmit.co/ajax/" + LEAD_INBOX, {
        method: "POST",
        headers: { "Content-Type": "application/json", Accept: "application/json" },
        body: JSON.stringify({
          _subject: "Plutus Crypto enquiry from " + data.company,
          _template: "table",
          Name: data.name,
          Company: data.company,
          Email: data.email,
          "Monthly volume": data.volume || "not given",
          Message: data.message || "none",
          Source: location.href
        })
      }).then(function (r) {
        return r.json().catch(function () { return {}; });
      }).then(function (result) {
        // A 200 is not proof of delivery. An inbox that has not been confirmed yet
        // answers with success false, and treating that as sent would hand the
        // visitor a thank you for an enquiry nobody ever received.
        if (String(result && result.success) !== "true") throw new Error("not delivered");
        form.reset();
        say("Thank you. We will come back to you within one business day.", "var(--ok)");
      }).catch(function () {
        // Never leave a visitor at a dead end: open their own mail client with
        // everything filled in, so the enquiry still arrives.
        var body = encodeURIComponent(
          "Name: " + data.name + "\nCompany: " + data.company + "\nEmail: " + data.email +
          "\nMonthly volume: " + (data.volume || "not given") + "\n\n" + data.message);
        note.innerHTML = 'We could not send that from here. <a href="mailto:' + LEAD_INBOX +
          "?subject=" + encodeURIComponent("Plutus Crypto enquiry from " + data.company) +
          "&body=" + body +
          '" style="color:var(--gold);text-decoration:underline">Send it from your mail app instead</a>' +
          " and we will pick it up straight away.";
        note.style.color = "var(--muted)";
      }).then(function () { button.disabled = false; });
    });
  }

  /* --------------------------------------------------------------- ticker -- */

  function ticker() {
    var track = $("#ticker");
    if (!track) return;
    var seen = {};
    var rows = ASSETS.filter(function (a) { if (seen[a.sym]) return false; seen[a.sym] = 1; return true; });
    var html = rows.map(function (a) {
      var move = (Math.random() * 6 - 2.4);
      var cls = move >= 0 ? "up" : "down";
      var price = a.rate >= 100 ? a.rate.toLocaleString("en-GB", { maximumFractionDigits: 0 })
                                : a.rate.toFixed(a.rate >= 1 ? 2 : 4);
      return '<span class="tick"><span class="sym">' + a.sym + '</span>' +
             '<span class="px">€' + price + '</span>' +
             '<span class="mv ' + cls + '">' + (move >= 0 ? "+" : "") + move.toFixed(2) + "%</span></span>";
    }).join("");
    track.innerHTML = html + html;
  }

  /* ------------------------------------------------------------- sections -- */

  function sections() {
    var grid = $("#productGrid");
    if (grid) PRODUCTS.forEach(function (p) {
      grid.appendChild(el("article", { class: "struck card card-link" },
        '<div class="card-icon">' + icon(p.icon) + "</div><h3>" + p.title + "</h3><p>" + p.text + "</p>"));
    });

    var sol = $("#solutionGrid");
    if (sol) SOLUTIONS.forEach(function (s) {
      sol.appendChild(el("article", { class: "struck card" }, "<h3>" + s.title + "</h3><p>" + s.text + "</p>"));
    });

    var sec = $("#securityGrid");
    if (sec) SECURITY.forEach(function (s) {
      sec.appendChild(el("article", { class: "struck card", style: "padding:20px" },
        "<h3 style='font-size:.9375rem'>" + s.title + "</h3><p style='font-size:.875rem'>" + s.text + "</p>"));
    });

    var rate = $("#rateCard");
    if (rate) {
      rate.innerHTML =
        '<span class="chip chip-gold" style="width:max-content">Everything included</span>' +
        '<div class="price"><span class="n">' + PRICE_RATE + '</span><span class="u">% per transaction</span></div>' +
        '<p style="color:var(--faint);font-size:.8125rem;margin-top:-6px">No monthly fee, no setup fee</p>' +
        "<ul>" + PRICE_INCLUDED.map(function (f) {
          return "<li>" + icon("check") + "<span>" + f + "</span></li>";
        }).join("") + "</ul>" +
        '<a class="btn btn-gold" href="/contact/" style="margin-top:6px">Request access</a>';
    }

    marginCalculator();

    var faq = $("#faqList");
    if (faq) FAQ.forEach(function (f) {
      faq.appendChild(el("details", { class: "faq" }, "<summary>" + f.q + "</summary><p>" + f.a + "</p>"));
    });

    var tabs = $("#codeTabs"), body = $("#codeBody");
    if (tabs && body) {
      Object.keys(CODE).forEach(function (lang, i) {
        var b = el("button", { class: "tab", role: "tab", "aria-selected": i === 0 ? "true" : "false",
                               style: "padding:6px 12px;font-size:.75rem" }, lang);
        b.addEventListener("click", function () {
          $$(".tab", tabs).forEach(function (o) { o.setAttribute("aria-selected", "false"); });
          b.setAttribute("aria-selected", "true");
          body.querySelector("code").textContent = CODE[lang];
        });
        tabs.appendChild(b);
      });
      body.querySelector("code").textContent = CODE[Object.keys(CODE)[0]];
    }

    var hook = $("#webhookSample");
    if (hook) hook.textContent = WEBHOOK_SAMPLE;
  }

  /* ---------------------------------------------------- surcharge calculator */

  /** Shows what a merchant keeps once they add their own surcharge on top of our rate.
      The customer pays the marked up amount, so our percentage applies to that total. */
  function marginCalculator() {
    var host = $("#marginCalc");
    if (!host) return;

    host.innerHTML =
      '<h3 style="font-size:1.25rem">Add your own surcharge</h3>' +
      '<p style="color:var(--muted);font-size:.875rem">Charge a little more for paying in crypto and the' +
      " three percent stops being a cost. Move the sliders to see where you land.</p>" +
      '<div class="field"><label for="calcVol">Crypto volume per month</label>' +
      '<input id="calcVol" type="range" min="5000" max="500000" step="5000" value="50000"></div>' +
      '<div class="field"><label for="calcFee">Your surcharge at checkout</label>' +
      '<input id="calcFee" type="range" min="0" max="6" step="0.25" value="4"></div>' +
      '<div id="calcOut" style="display:grid;gap:9px"></div>';

    var vol = $("#calcVol"), fee = $("#calcFee"), out = $("#calcOut");

    function row(label, value, tone) {
      return '<div style="display:flex;justify-content:space-between;gap:14px;align-items:baseline">' +
        '<span style="font-size:.875rem;color:var(--muted)">' + label + "</span>" +
        '<b class="mono" style="font-size:.9375rem' + (tone ? ";color:" + tone : "") + '">' + value + "</b></div>";
    }

    function draw() {
      var v = Number(vol.value), s = Number(fee.value);
      var customerPays = v * (1 + s / 100);
      var ourFee = customerPays * (PRICE_RATE / 100);
      var youKeep = customerPays - ourFee;
      var versusList = youKeep - v;
      var perOrder = ((1 + s / 100) * (1 - PRICE_RATE / 100) - 1) * 100;
      var tone = versusList >= 0 ? "var(--ok)" : "var(--dead)";

      out.innerHTML =
        row("Volume at your list prices", money(v, "EUR")) +
        row("Surcharge", s.toFixed(2).replace(/\.00$/, "") + " %", "var(--gold-lit)") +
        row("Your customers pay", money(customerPays, "EUR")) +
        row("Plutus fee, " + PRICE_RATE + " %", "-" + money(ourFee, "EUR")) +
        '<div style="height:1px;background:var(--line-soft);margin:3px 0"></div>' +
        row("You receive", money(youKeep, "EUR")) +
        row(versusList >= 0 ? "Extra margin per month" : "Cost per month",
            (versusList >= 0 ? "+" : "") + money(versusList, "EUR"), tone) +
        '<p class="mono" style="font-size:.6875rem;color:var(--faint);margin-top:4px">' +
        (perOrder >= 0
          ? "At " + s + " percent you keep " + perOrder.toFixed(2) + " percent on every crypto order."
          : "At " + s + " percent you carry " + Math.abs(perOrder).toFixed(2) + " percent yourself.") +
        "</p>";
    }

    vol.addEventListener("input", draw);
    fee.addEventListener("input", draw);
    draw();
  }

  /* --------------------------------------------------------------- stages -- */

  var STAGES = [
    { key: "await",   label: "Awaiting payment",   sub: "Address is live" },
    { key: "seen",    label: "Seen on the network", sub: "In the mempool" },
    { key: "confirm", label: "Confirming",          sub: "" },
    { key: "done",    label: "Payment confirmed",   sub: "Final, no reversal" },
    { key: "settled", label: "Settled to your bank", sub: "SEPA, next business day" }
  ];

  function renderStepper(host, state) {
    host.innerHTML = "";
    STAGES.forEach(function (s, i) {
      var cls = "stage";
      if (state.failed && i >= state.index) cls += i === state.index ? " failed" : "";
      else if (i < state.index) cls += " done";
      else if (i === state.index) cls += " active";
      var sub = s.key === "confirm" && state.index >= 2
        ? state.confirmations + " of " + state.needed + " confirmations"
        : (state.failed && i === state.index ? state.failReason : s.sub);
      host.appendChild(el("div", { class: cls },
        '<span class="ring"></span>' +
        '<span><span class="label">' + (state.failed && i === state.index ? state.failLabel : s.label) + "</span>" +
        (sub ? '<span class="sub">' + sub + "</span>" : "") + "</span>" +
        '<span class="when">' + (state.stamps[i] || "") + "</span>"));
    });
  }

  /* ----------------------------------------------------------- hero card -- */

  function heroCard() {
    var host = $("#heroStepper");
    if (!host) return;
    var asset = ASSETS[0];
    var state = { index: 0, confirmations: 0, needed: asset.conf, stamps: [], failed: false };
    renderStepper(host, state);
    if (reduceMotion) {
      state.index = 4; state.confirmations = asset.conf;
      state.stamps = ["14:22:08", "14:22:31", "14:23:02", "14:24:19", "next day"];
      renderStepper(host, state);
      return;
    }
    var step = 0;
    setInterval(function () {
      step++;
      if (step > 7) {
        step = 0;
        state = { index: 0, confirmations: 0, needed: asset.conf, stamps: [], failed: false };
      } else if (step === 1) { state.index = 1; state.stamps[0] = clock(); }
      else if (step === 2) { state.index = 2; state.stamps[1] = clock(); state.confirmations = 1; }
      else if (step === 3) { state.confirmations = 2; }
      else if (step === 4) { state.index = 3; state.stamps[2] = clock(); }
      else if (step === 5) { state.index = 4; state.stamps[3] = clock(); }
      else if (step === 6) { state.stamps[4] = "tomorrow"; }
      renderStepper(host, state);
    }, 1700);
  }

  /* ------------------------------------------------------------- checkout -- */

  var demo = {
    mode: "online",
    fiat: "EUR",
    amount: 189.00,
    reference: "INV-2026-0841",
    asset: null,
    payment: null,
    timer: null,
    tickHandle: null
  };

  /* Each chain has its own alphabet. Getting this wrong is the first thing
     anyone who works with crypto would notice, so the generator follows them. */
  var ALPHABET = {
    base58: "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz",
    bech32: "qpzry9x8gf2tvdw0s3jn54khce6mua7l",
    hex: "0123456789abcdef"
  };

  function makeId() {
    var out = "";
    for (var i = 0; i < 8; i++) out += "0123456789ABCDEFGHJKLMNPQRSTUVWXYZ"[Math.floor(Math.random() * 34)];
    return out;
  }

  function makeAddress(asset, seed) {
    var kind = asset.addr || "base58", length = asset.len || 33;
    var chars = ALPHABET[kind] || ALPHABET.base58;
    var out = asset.prefix || "";
    var h = 2166136261;
    for (var i = 0; i < seed.length; i++) {
      h = (h ^ seed.charCodeAt(i)) >>> 0;
      h = (h * 16777619) >>> 0;
    }
    for (var j = 0; j < length; j++) {
      // xorshift32: the low bits of a plain congruential generator repeat on
      // alphabets sized to a power of two, which turns bech32 into rows of q
      h ^= h << 13; h >>>= 0;
      h ^= h >>> 17;
      h ^= h << 5;  h >>>= 0;
      out += chars[(h >>> 8) % chars.length];
    }
    return out;
  }

  function fiatToCrypto(amount, fiatCode, asset) {
    var eur = amount / (FIAT[fiatCode] || FIAT.EUR).rate;
    return eur / asset.rate;
  }

  function logEvent(name, fields) {
    var host = $("#console");
    if (!host) return;
    var body = Object.keys(fields || {}).map(function (k) {
      return '<span class="k">' + k + '</span>=<span class="v">' + fields[k] + "</span>";
    }).join(" ");
    var row = el("div", { class: "row" },
      '<span class="t">' + clock() + '</span><span><span class="ev">' + name + "</span> " + body + "</span>");
    host.appendChild(row);
    host.scrollTop = host.scrollHeight;
  }

  function merchantPanel() {
    var body = $("#merchantBody");
    if (!body) return;
    var titles = { online: "Create a payment", pos: "Terminal, take a payment", link: "Create a payment link" };
    $("#merchantTitle").textContent = titles[demo.mode];

    body.innerHTML = "";
    var amountField = el("div", { class: "field" },
      '<label for="amt">Amount to charge</label>' +
      '<div class="amount-field"><span class="cur" id="curSign">€</span>' +
      '<input class="input" id="amt" type="text" inputmode="decimal" value="' + demo.amount.toFixed(2) + '"></div>');
    body.appendChild(amountField);

    var cur = el("div", { class: "field" }, '<label>Settlement currency</label>');
    var seg = el("div", { class: "seg" });
    Object.keys(FIAT).forEach(function (code) {
      var b = el("button", { type: "button", "aria-pressed": code === demo.fiat ? "true" : "false" }, code);
      b.addEventListener("click", function () {
        demo.fiat = code;
        $("#curSign").textContent = FIAT[code].symbol;
        $$("button", seg).forEach(function (o) { o.setAttribute("aria-pressed", "false"); });
        b.setAttribute("aria-pressed", "true");
      });
      seg.appendChild(b);
    });
    cur.appendChild(seg);
    body.appendChild(cur);

    body.appendChild(el("div", { class: "field" },
      '<label for="ref">' + (demo.mode === "pos" ? "Till reference" : "Your reference") + "</label>" +
      '<input class="input mono" id="ref" type="text" value="' + demo.reference + '">'));

    if (demo.mode === "link") {
      body.appendChild(el("div", { class: "field" },
        '<label for="exp">Link expires</label>' +
        '<select class="select" id="exp"><option>After 24 hours</option><option>After 7 days</option>' +
        "<option>When paid once</option></select>"));
    }

    var go = el("button", { class: "btn btn-gold", type: "button", style: "width:100%" },
      demo.mode === "link" ? "Create link" : "Create payment");
    go.addEventListener("click", function () {
      var raw = parseFloat(($("#amt").value || "0").replace(",", "."));
      if (!(raw > 0)) { $("#amt").focus(); return; }
      demo.amount = raw;
      demo.reference = $("#ref").value || demo.reference;
      demo.asset = null;
      demo.payment = null;
      customerPanel();
      logEvent("payment.created", {
        id: '"pay_' + makeId() + '"',
        amount: '"' + demo.amount.toFixed(2) + '"',
        currency: '"' + demo.fiat + '"',
        reference: '"' + demo.reference + '"'
      });
    });
    body.appendChild(go);

    body.appendChild(el("p", { class: "mono", style: "font-size:.6875rem;color:var(--faint);margin-top:2px" },
      "Sandbox. Rates are indicative and addresses are test addresses."));
  }

  function customerPanel() {
    var host = $("#customerPanel");
    if (!host) return;
    host.innerHTML = "";

    var card = el("div", { class: "struck checkout" });
    var head = el("div", { class: "checkout-head" },
      '<span class="who"><img src="ASSET:coin-180.png" alt="" width="26" height="26"> Atlas Watches</span>' +
      '<span class="chip">' + (demo.mode === "pos" ? "Terminal 04" : demo.mode === "link" ? "Payment link" : "Checkout") + "</span>");
    card.appendChild(head);

    var body = el("div", { class: "panel-body" });
    card.appendChild(body);
    host.appendChild(card);

    if (!demo.asset) {
      if (demo.mode === "link") {
        var linkUrl = "https://pay.plutuscrypto.com/l/" + makeId().slice(0, 6).toLowerCase();
        var linkBox = el("div", { class: "addr" }, "<code>" + linkUrl + "</code>");
        var linkCopy = el("button", { class: "btn btn-quiet", type: "button" }, "Copy link");
        linkCopy.addEventListener("click", function () {
          if (navigator.clipboard) navigator.clipboard.writeText(linkUrl);
          linkCopy.textContent = "Copied";
          setTimeout(function () { linkCopy.textContent = "Copy link"; }, 1600);
        });
        linkBox.appendChild(linkCopy);
        body.appendChild(el("div", { class: "field" },
          "<label>Send this to your customer by mail, chat or QR</label>"));
        body.appendChild(linkBox);
      }
      if (demo.mode === "pos") {
        body.appendChild(el("div", { style: "text-align:center;padding:6px 0 2px" },
          '<div class="eyebrow">Customer display</div>' +
          '<div class="mono" style="font-size:2.5rem;font-weight:700;color:var(--gold-lit);margin-top:6px">' +
          money(demo.amount, demo.fiat) + "</div>"));
      }
      body.appendChild(el("div", {},
        '<p style="font-size:.9375rem;color:var(--muted)">Pay <b style="color:var(--gold-lit)">' +
        money(demo.amount, demo.fiat) + "</b> to Atlas Watches. Choose how you would like to pay.</p>"));
      var grid = el("div", { class: "asset-grid" });
      ASSETS.forEach(function (a) {
        var b = el("button", { class: "asset", type: "button" },
          '<span class="glyph" style="background:' + a.tint + '">' + a.sym + "</span>" +
          '<span class="meta"><span class="name">' + a.name + '</span><span class="net">' + a.network + "</span></span>");
        b.addEventListener("click", function () { demo.asset = a; customerPanel(); });
        grid.appendChild(b);
      });
      body.appendChild(grid);
      return;
    }

    /* ---- payment screen ---- */
    var asset = demo.asset;
    if (!demo.payment) {
      var id = makeId();
      var amount = fiatToCrypto(demo.amount, demo.fiat, asset);
      demo.payment = {
        id: id,
        address: makeAddress(asset, id + asset.sym),
        amount: amount,
        rate: asset.rate * (FIAT[demo.fiat] || FIAT.EUR).rate,
        expires: Date.now() + 15 * 60 * 1000,
        state: { index: 0, confirmations: 0, needed: asset.conf, stamps: [], failed: false }
      };
      logEvent("quote.locked", {
        asset: '"' + asset.sym + '"', network: '"' + asset.network + '"',
        amount: '"' + crypto(amount, asset.dp) + '"', valid_for: "900"
      });
    }
    var pay = demo.payment;

    var back = el("button", { class: "btn-quiet btn", type: "button", style: "width:max-content" }, "Change asset");
    back.addEventListener("click", function () { demo.asset = null; demo.payment = null; stopTimer(); customerPanel(); });
    body.appendChild(back);

    body.appendChild(el("div", { class: "pay-amount" },
      '<span class="crypto">' + crypto(pay.amount, asset.dp) + " " + asset.sym + "</span>" +
      '<span class="fiat">' + money(demo.amount, demo.fiat) + " at " +
      money(pay.rate, demo.fiat) + " per " + asset.sym + "</span>"));

    var qrWrap = el("div", { class: "qr-frame" });
    var canvas = el("canvas");
    qrWrap.appendChild(canvas);
    qrWrap.appendChild(el("span", { class: "hint" }, "Scan to open this payment on your phone"));
    body.appendChild(qrWrap);

    var payUrl = location.origin + location.pathname + "#pay/" + pay.id;
    try { PlutusQR.draw(canvas, payUrl, { pixels: 260, background: "#FBF8FF", foreground: "#14032B" }); }
    catch (e) { qrWrap.style.display = "none"; }

    var addr = el("div", { class: "addr" },
      "<code>" + pay.address + "</code>");
    var copy = el("button", { class: "btn btn-quiet", type: "button" }, "Copy");
    copy.addEventListener("click", function () {
      if (navigator.clipboard) navigator.clipboard.writeText(pay.address);
      copy.textContent = "Copied";
      setTimeout(function () { copy.textContent = "Copy"; }, 1600);
    });
    addr.appendChild(copy);
    body.appendChild(el("div", { class: "field" },
      '<label>Send exactly this amount to the ' + asset.network + " address</label>"));
    body.appendChild(addr);
    body.appendChild(el("span", { class: "chip chip-wait", style: "width:max-content" },
      '<span class="dot"></span>Test address, nothing can be sent to it'));

    var lock = el("div", { class: "lock" },
      '<div class="lock-row"><span>Rate locked</span><b id="lockClock">15:00</b></div>' +
      '<div class="lock-bar"><div class="lock-fill" id="lockFill"></div></div>');
    body.appendChild(lock);

    var stepper = el("div", { class: "stepper", id: "payStepper" });
    body.appendChild(stepper);
    renderStepper(stepper, pay.state);

    var actions = el("div", { style: "display:flex;gap:8px;flex-wrap:wrap" });
    var payBtn = el("button", { class: "btn btn-gold", type: "button", style: "flex:1 1 150px" }, "Simulate payment");
    payBtn.addEventListener("click", function () { runPayment(false); });
    var underBtn = el("button", { class: "btn btn-ghost", type: "button" }, "Underpay");
    underBtn.addEventListener("click", function () { runPayment(true); });
    var expireBtn = el("button", { class: "btn btn-ghost", type: "button" }, "Let it expire");
    expireBtn.addEventListener("click", function () { expire(); });
    actions.appendChild(payBtn); actions.appendChild(underBtn); actions.appendChild(expireBtn);
    body.appendChild(actions);
    demo.actions = { pay: payBtn, under: underBtn, expire: expireBtn };

    startTimer();
  }

  function stopTimer() {
    if (demo.tickHandle) { clearInterval(demo.tickHandle); demo.tickHandle = null; }
  }

  function startTimer() {
    stopTimer();
    var fill = $("#lockFill"), out = $("#lockClock");
    if (!fill || !out) return;
    demo.tickHandle = setInterval(function () {
      var left = Math.max(0, demo.payment.expires - Date.now());
      var pct = left / (15 * 60 * 1000);
      fill.style.transform = "scaleX(" + pct + ")";
      fill.classList.toggle("low", pct < 0.2);
      var m = Math.floor(left / 60000), s = Math.floor((left % 60000) / 1000);
      out.textContent = m + ":" + String(s).padStart(2, "0");
      if (left <= 0) expire();
    }, 1000);
  }

  function expire() {
    stopTimer();
    var pay = demo.payment;
    if (!pay || pay.state.index >= 3) return;
    pay.state.failed = true;
    pay.state.failLabel = "Quote expired";
    pay.state.failReason = "No funds seen inside the window";
    renderStepper($("#payStepper"), pay.state);
    logEvent("payment.expired", { id: '"pay_' + pay.id + '"', reason: '"quote_window_elapsed"' });
    if (demo.actions) { demo.actions.pay.disabled = true; demo.actions.under.disabled = true; demo.actions.expire.disabled = true; }
  }

  function runPayment(under) {
    var pay = demo.payment, asset = demo.asset, stepper = $("#payStepper");
    if (!pay || pay.state.failed || pay.state.index > 0) return;
    if (demo.actions) { demo.actions.pay.disabled = true; demo.actions.under.disabled = true; }

    var sent = under ? pay.amount * 0.82 : pay.amount;
    var tx = makeAddress({ prefix: "" }, pay.id + "tx").slice(0, 12).toLowerCase();

    var s = pay.state;
    s.index = 1; s.stamps[0] = clock();
    renderStepper(stepper, s);
    logEvent("payment.detected", {
      id: '"pay_' + pay.id + '"', amount: '"' + crypto(sent, asset.dp) + '"', confirmations: "0"
    });

    if (under) {
      setTimeout(function () {
        s.failed = true; s.index = 1;
        s.failLabel = "Underpaid";
        s.failReason = "Received " + crypto(sent, asset.dp) + " of " + crypto(pay.amount, asset.dp) + " " + asset.sym;
        renderStepper(stepper, s);
        logEvent("payment.underpaid", {
          shortfall: '"' + crypto(pay.amount - sent, asset.dp) + '"', action: '"await_merchant"'
        });
        var fix = el("div", { class: "chip chip-dead", style: "width:max-content" },
          '<span class="dot"></span>Waiting for you to accept, top up or refund');
        stepper.parentNode.insertBefore(fix, stepper.nextSibling);
        if (demo.actions) demo.actions.expire.disabled = true;
      }, 1200);
      return;
    }

    var step = 0;
    var beat = setInterval(function () {
      step++;
      if (step === 1) {
        s.index = 2; s.stamps[1] = clock(); s.confirmations = 1;
        logEvent("payment.confirming", { confirmations: "1", required: String(asset.conf) });
      } else if (step <= asset.conf && s.confirmations < asset.conf) {
        s.confirmations = Math.min(asset.conf, s.confirmations + Math.max(1, Math.ceil(asset.conf / 4)));
      } else if (s.index === 2) {
        s.index = 3; s.stamps[2] = clock();
        logEvent("payment.confirmed", { tx: '"' + tx + '…"', confirmations: String(asset.conf) });
      } else if (s.index === 3) {
        s.index = 4; s.stamps[3] = clock(); s.stamps[4] = "next business day";
        logEvent("settlement.scheduled", {
          amount: '"' + demo.amount.toFixed(2) + '"', currency: '"' + demo.fiat + '"', method: '"sepa"'
        });
        clearInterval(beat);
        stopTimer();
        settle(sent, tx);
      }
      renderStepper(stepper, s);
    }, reduceMotion ? 200 : 700);
  }

  function settle(sent, tx) {
    var asset = demo.asset;
    var fee = demo.amount * (PRICE_RATE / 100);
    var receipt = el("div", { class: "struck", style: "padding:16px;display:grid;gap:8px" },
      '<div style="display:flex;justify-content:space-between;gap:12px;font-size:.875rem">' +
        "<span>Received</span><b class='mono'>" + crypto(sent, asset.dp) + " " + asset.sym + "</b></div>" +
      '<div style="display:flex;justify-content:space-between;gap:12px;font-size:.875rem">' +
        "<span>Converted</span><b class='mono'>" + money(demo.amount, demo.fiat) + "</b></div>" +
      '<div style="display:flex;justify-content:space-between;gap:12px;font-size:.875rem;color:var(--muted)">' +
        "<span>Fee, " + PRICE_RATE + " percent</span><span class='mono'>-" + money(fee, demo.fiat) + "</span></div>" +
      '<div style="display:flex;justify-content:space-between;gap:12px;padding-top:8px;border-top:1px solid var(--line-soft)">' +
        "<span style='font-weight:700'>To your bank</span><b class='mono' style='color:var(--ok)'>" +
        money(demo.amount - fee, demo.fiat) + "</b></div>" +
      '<div class="mono" style="font-size:.6875rem;color:var(--faint)">tx ' + tx + "… · " + asset.network + "</div>");
    var host = $("#customerPanel .panel-body");
    if (host) host.appendChild(receipt);

    var jump = el("a", { class: "btn btn-ghost", href: "#dashboard", style: "width:max-content" },
      "See it in the dashboard");
    if (host) host.appendChild(jump);

    addToDashboard(sent, tx);
    if (demo.actions) demo.actions.expire.disabled = true;
  }

  function bindTabs() {
    $$("#demo .tab").forEach(function (tab) {
      tab.addEventListener("click", function () {
        $$("#demo .tab").forEach(function (o) { o.setAttribute("aria-selected", "false"); });
        tab.setAttribute("aria-selected", "true");
        demo.mode = tab.dataset.mode;
        demo.asset = null; demo.payment = null;
        stopTimer();
        merchantPanel();
        customerPanel();
      });
    });
  }

  /* ------------------------------------------------------------ dashboard -- */

  var dash = { volume: 0, count: 0, settled: 0 };

  function dashboard() {
    var total = VOLUME_30D.reduce(function (a, b) { return a + b; }, 0);
    dash.volume = total;
    dash.count = 1284;
    dash.settled = Math.round(total * 0.62);

    var compact = function (v) {
      return v >= 1e6 ? "€" + (v / 1e6).toFixed(2) + "M" : "€" + (v / 1000).toFixed(1) + "k";
    };

    var kpis = $("#kpis");
    if (kpis) {
      [
        { k: "Volume, 30 days", v: compact(total), d: "+18.4% vs previous", up: true },
        { k: "Payments", v: dash.count.toLocaleString("en-GB"), d: "+241 this week", up: true },
        { k: "Average ticket", v: "€" + Math.round(total / dash.count), d: "-3.1% vs previous", up: false },
        { k: "Next settlement", v: compact(67150), d: "Tomorrow, SEPA", up: true }
      ].forEach(function (t) {
        kpis.appendChild(el("div", { class: "struck kpi" },
          '<span class="k">' + t.k + '</span><span class="v">' + t.v + "</span>" +
          '<span class="d ' + (t.up ? "up" : "down") + '">' + t.d + "</span>"));
      });
    }

    var tag = $("#volumeTotal");
    if (tag) tag.textContent = "€" + total.toLocaleString("en-GB");

    drawVolume();
    drawSplit();

    var body = $("#txBody");
    if (body) SEED_TX.forEach(function (t) { body.appendChild(txRow(t)); });

    var ledger = $("#ledger");
    if (ledger) {
      [
        { label: "Confirmed, awaiting payout", value: "€67,150.00", tone: "" },
        { label: "In transit to bank", value: "€48,900.00", tone: "wait" },
        { label: "Paid out this month", value: "€412,380.00", tone: "ok" },
        { label: "Fees this month", value: "€4,123.80", tone: "" },
        { label: "Refunded this month", value: "€1,240.00", tone: "" }
      ].forEach(function (r) {
        ledger.appendChild(el("div", { style: "display:flex;justify-content:space-between;gap:12px;align-items:center;" +
            "padding:11px 0;border-bottom:1px solid rgba(162,148,188,.1)" },
          '<span style="font-size:.875rem;color:var(--muted)">' + r.label + "</span>" +
          '<b class="mono" style="font-size:.9375rem' + (r.tone === "ok" ? ";color:var(--ok)" : r.tone === "wait" ? ";color:var(--wait)" : "") + '">' +
          r.value + "</b>"));
      });
      ledger.appendChild(el("div", { class: "eyebrow", style: "margin-top:14px" }, "Webhook feed"));
      ledger.appendChild(el("div", { class: "console", id: "console" }, ""));
      logEvent("session.ready", { environment: '"sandbox"', merchant: '"atlas_watches"' });
    }
  }

  function txRow(t) {
    var tone = t.status === "settled" ? "chip-ok" : t.status === "confirmed" ? "chip-gold"
             : t.status === "refunded" ? "chip-dead" : "chip-wait";
    return el("tr", {},
      "<td><strong>" + t.ref + "</strong></td>" +
      "<td>" + t.sym + ' <span style="color:var(--faint)">' + t.net + "</span></td>" +
      '<td><span class="chip ' + tone + '"><span class="dot"></span>' + t.status + "</span></td>" +
      '<td class="num">' + t.crypto + "</td>" +
      '<td class="num">€' + t.fiat + "</td>" +
      "<td>" + t.when + "</td>");
  }

  function addToDashboard(sent, tx) {
    var body = $("#txBody");
    if (!body) return;
    var asset = demo.asset;
    var row = txRow({
      ref: demo.reference, sym: asset.sym, net: asset.network, status: "confirmed",
      crypto: crypto(sent, asset.dp), fiat: demo.amount.toFixed(2), when: "just now"
    });
    row.classList.add("fresh");
    body.insertBefore(row, body.firstChild);
    dash.count += 1;
    var kpiCount = $$("#kpis .v")[1];
    if (kpiCount) kpiCount.textContent = dash.count.toLocaleString("en-GB");
  }

  /* ---------------------------------------------------------------- plots -- */

  function fitCanvas(canvas) {
    var ratio = window.devicePixelRatio || 1;
    var w = canvas.clientWidth || 600, h = canvas.clientHeight || 220;
    canvas.width = w * ratio; canvas.height = h * ratio;
    var ctx = canvas.getContext("2d");
    ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
    return { ctx: ctx, w: w, h: h };
  }

  function drawVolume() {
    var canvas = $("#volumeChart");
    if (!canvas) return;
    var f = fitCanvas(canvas), ctx = f.ctx, w = f.w, h = f.h;
    var pad = { l: 8, r: 8, t: 12, b: 22 };
    var data = VOLUME_30D, max = Math.max.apply(null, data) * 1.12;
    var stepX = (w - pad.l - pad.r) / (data.length - 1);
    var y = function (v) { return pad.t + (1 - v / max) * (h - pad.t - pad.b); };

    ctx.clearRect(0, 0, w, h);
    ctx.strokeStyle = "rgba(162,148,188,.13)";
    ctx.lineWidth = 1;
    for (var g = 0; g <= 3; g++) {
      var gy = pad.t + g * (h - pad.t - pad.b) / 3;
      ctx.beginPath(); ctx.moveTo(pad.l, gy); ctx.lineTo(w - pad.r, gy); ctx.stroke();
    }

    var grad = ctx.createLinearGradient(0, pad.t, 0, h - pad.b);
    grad.addColorStop(0, "rgba(228,178,63,.34)");
    grad.addColorStop(1, "rgba(228,178,63,0)");

    ctx.beginPath();
    data.forEach(function (v, i) {
      var px = pad.l + i * stepX, py = y(v);
      if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    });
    ctx.lineTo(pad.l + (data.length - 1) * stepX, h - pad.b);
    ctx.lineTo(pad.l, h - pad.b);
    ctx.closePath();
    ctx.fillStyle = grad; ctx.fill();

    ctx.beginPath();
    data.forEach(function (v, i) {
      var px = pad.l + i * stepX, py = y(v);
      if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    });
    ctx.strokeStyle = "#E4B23F"; ctx.lineWidth = 2; ctx.lineJoin = "round"; ctx.stroke();

    var lastX = pad.l + (data.length - 1) * stepX, lastY = y(data[data.length - 1]);
    ctx.beginPath(); ctx.arc(lastX, lastY, 4.5, 0, Math.PI * 2);
    ctx.fillStyle = "#FBEBB6"; ctx.fill();
    ctx.strokeStyle = "rgba(228,178,63,.55)"; ctx.lineWidth = 6; ctx.stroke();

    ctx.fillStyle = "rgba(162,148,188,.75)";
    ctx.font = "11px " + getComputedStyle(document.body).getPropertyValue("--mono");
    ctx.fillText("30 days ago", pad.l, h - 6);
    ctx.textAlign = "right";
    ctx.fillText("today", w - pad.r, h - 6);
    ctx.textAlign = "left";
  }

  function drawSplit() {
    var canvas = $("#assetChart");
    if (!canvas) return;
    var f = fitCanvas(canvas), ctx = f.ctx, w = f.w, h = f.h;
    var cx = w / 2, cy = h / 2, radius = Math.min(w, h) / 2 - 8, inner = radius * 0.62;
    ctx.clearRect(0, 0, w, h);
    var start = -Math.PI / 2;
    ASSET_SPLIT.forEach(function (s) {
      var slice = (s.pct / 100) * Math.PI * 2;
      ctx.beginPath();
      ctx.arc(cx, cy, radius, start, start + slice);
      ctx.arc(cx, cy, inner, start + slice, start, true);
      ctx.closePath();
      ctx.fillStyle = s.tint;
      ctx.globalAlpha = 0.92;
      ctx.fill();
      ctx.globalAlpha = 1;
      start += slice;
    });
    ctx.fillStyle = "#F2EFF8";
    ctx.textAlign = "center";
    ctx.font = "700 15px " + getComputedStyle(document.body).getPropertyValue("--mono");
    ctx.fillText("13", cx, cy - 1);
    ctx.fillStyle = "rgba(162,148,188,.85)";
    ctx.font = "10px " + getComputedStyle(document.body).getPropertyValue("--sans");
    ctx.fillText("assets live", cx, cy + 13);
    ctx.textAlign = "left";

    var legend = $("#assetLegend");
    if (legend) legend.innerHTML = ASSET_SPLIT.map(function (s) {
      return '<span><i style="background:' + s.tint + '"></i>' + s.sym + " " + s.pct + "%</span>";
    }).join("");
  }

  /* ----------------------------------------------------------------- boot -- */

  function boot() {
    chrome();
    ticker();
    sections();
    heroCard();
    bindTabs();
    merchantPanel();
    customerPanel();
    dashboard();

    var redraw;
    window.addEventListener("resize", function () {
      clearTimeout(redraw);
      redraw = setTimeout(function () { drawVolume(); drawSplit(); }, 160);
    });
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();

/* Plutus Crypto — site chrome and the futuristic layer.
   Each module looks for its root element and steps aside when it is not on
   the page, so one script serves every page of the site. */
(function () {
  "use strict";

  var $ = function (sel, root) { return (root || document).querySelector(sel); };
  var $$ = function (sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); };
  var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  var finePointer = window.matchMedia("(hover: hover) and (pointer: fine)").matches;

  /* ------------------------------------------------------------- drawer -- */

  function drawer() {
    var toggle = $(".nav-toggle"), box = $("#drawer");
    if (!toggle || !box) return;
    var close = $(".drawer-close", box), scrim = $(".drawer-scrim", box);

    function open() {
      box.hidden = false;
      document.body.classList.add("drawer-open");
      toggle.setAttribute("aria-expanded", "true");
      var first = $(".drawer-link", box);
      if (first) first.focus();
    }
    function shut() {
      box.hidden = true;
      document.body.classList.remove("drawer-open");
      toggle.setAttribute("aria-expanded", "false");
      toggle.focus();
    }
    toggle.addEventListener("click", function () { box.hidden ? open() : shut(); });
    close.addEventListener("click", shut);
    scrim.addEventListener("click", shut);
    document.addEventListener("keydown", function (e) { if (e.key === "Escape" && !box.hidden) shut(); });
  }

  /* touch devices have no hover, so a tap on a menu parent opens it first */
  function menus() {
    $$(".has-menu").forEach(function (item) {
      var link = $("a", item);
      link.addEventListener("click", function (e) {
        if (finePointer) return;
        if (!item.classList.contains("open")) {
          e.preventDefault();
          $$(".has-menu.open").forEach(function (o) { o.classList.remove("open"); });
          item.classList.add("open");
        }
      });
    });
    document.addEventListener("click", function (e) {
      if (!e.target.closest(".has-menu")) $$(".has-menu.open").forEach(function (o) { o.classList.remove("open"); });
    });
  }

  function currentLinks() {
    var path = location.pathname.replace(/index\.html$/, "");
    $$('a[href^="/"]').forEach(function (a) {
      var href = a.getAttribute("href").split("#")[0];
      if (!href || href === "/") { if (path === "/" && a.classList.contains("drawer-link")) a.classList.add("current"); return; }
      if (path === href || (href.length > 1 && path.indexOf(href) === 0 && a.closest(".nav, .drawer-panel")))
        a.classList.add("current");
    });
  }

  /* --------------------------------------------------------------- dock -- */

  function dock() {
    var bar = $("#dock");
    if (!bar) return;
    var last = 0;
    function check() {
      var y = window.scrollY;
      var nearEnd = window.innerHeight + y > document.body.scrollHeight - 420;
      bar.classList.toggle("show", y > 560 && !nearEnd);
      bar.setAttribute("aria-hidden", bar.classList.contains("show") ? "false" : "true");
      last = y;
    }
    window.addEventListener("scroll", check, { passive: true });
    check();
  }

  /* -------------------------------------------------------- constellation -- */

  /** Slowly drifting nodes joined by faint lines, gold and purple. The pointer
      pulls nearby nodes a little, so the sky answers the reader without
      ever getting in the way of the words. */
  function sky() {
    var canvas = $("#sky");
    if (!canvas || reduceMotion) return;
    var ctx = canvas.getContext("2d");
    var nodes = [], w = 0, h = 0, ratio = 1, px = -1e4, py = -1e4;

    function size() {
      ratio = Math.min(window.devicePixelRatio || 1, 2);
      var r = canvas.parentElement.getBoundingClientRect();
      w = r.width; h = r.height;
      canvas.width = w * ratio; canvas.height = h * ratio;
      ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
      var count = Math.round(Math.min(110, (w * h) / 14000));
      nodes = [];
      for (var i = 0; i < count; i++) {
        nodes.push({
          x: Math.random() * w, y: Math.random() * h,
          vx: (Math.random() - 0.5) * 0.18, vy: (Math.random() - 0.5) * 0.18,
          r: Math.random() * 1.4 + 0.6,
          gold: Math.random() < 0.38
        });
      }
    }

    function frame() {
      ctx.clearRect(0, 0, w, h);
      for (var i = 0; i < nodes.length; i++) {
        var n = nodes[i];
        var dx = px - n.x, dy = py - n.y, d2 = dx * dx + dy * dy;
        if (d2 < 32000) { n.x -= dx * 0.0025; n.y -= dy * 0.0025; }
        n.x += n.vx; n.y += n.vy;
        if (n.x < -10) n.x = w + 10; if (n.x > w + 10) n.x = -10;
        if (n.y < -10) n.y = h + 10; if (n.y > h + 10) n.y = -10;
      }
      ctx.lineWidth = 1;
      for (var a = 0; a < nodes.length; a++) {
        for (var b = a + 1; b < nodes.length; b++) {
          var ax = nodes[a].x - nodes[b].x, ay = nodes[a].y - nodes[b].y;
          var dist = ax * ax + ay * ay;
          if (dist < 15000) {
            var alpha = (1 - dist / 15000) * 0.32;
            ctx.strokeStyle = (nodes[a].gold || nodes[b].gold)
              ? "rgba(228,178,63," + alpha + ")" : "rgba(180,70,255," + alpha * 0.9 + ")";
            ctx.beginPath(); ctx.moveTo(nodes[a].x, nodes[a].y); ctx.lineTo(nodes[b].x, nodes[b].y); ctx.stroke();
          }
        }
      }
      for (var k = 0; k < nodes.length; k++) {
        var m = nodes[k];
        ctx.beginPath(); ctx.arc(m.x, m.y, m.r, 0, Math.PI * 2);
        ctx.fillStyle = m.gold ? "rgba(251,235,182,0.9)" : "rgba(200,150,255,0.75)";
        ctx.fill();
      }
      requestAnimationFrame(frame);
    }

    size();
    window.addEventListener("resize", size);
    canvas.parentElement.addEventListener("pointermove", function (e) {
      var r = canvas.getBoundingClientRect();
      px = e.clientX - r.left; py = e.clientY - r.top;
    });
    canvas.parentElement.addEventListener("pointerleave", function () { px = py = -1e4; });
    frame();
  }

  /* ---------------------------------------------------------- spotlight --- */

  function spotlight() {
    if (!finePointer) return;
    $$(".spot").forEach(function (card) {
      card.addEventListener("pointermove", function (e) {
        var r = card.getBoundingClientRect();
        card.style.setProperty("--mx", (e.clientX - r.left) + "px");
        card.style.setProperty("--my", (e.clientY - r.top) + "px");
      });
    });
  }

  /* ---------------------------------------------------------------- feed --- */

  /** A sandbox feed: plausible payments arriving from cities around the world.
      Labelled as simulated in the page; the shapes and sizes are realistic. */
  function feed() {
    var host = $("#feed");
    if (!host) return;
    var cities = ["Amsterdam", "Lisbon", "Dubai", "Singapore", "Berlin", "Madrid", "Zurich", "Milan",
                  "Warsaw", "Istanbul", "Lagos", "São Paulo", "Toronto", "Sydney", "Bangkok", "Prague",
                  "Rotterdam", "Vienna", "Manila", "Nairobi", "Buenos Aires", "Seoul", "Tallinn", "Riga"];
    var shops = ["Atlas Watches", "Nordlys Travel", "Kite Hosting", "Marble & Co", "Volta Bikes",
                 "Reef Diving", "Orbit Gaming", "Cedar Furniture", "Mira Cosmetics", "Harbour Yachts",
                 "Pixel Forge", "Aurum Jewellers", "Stratus VPN", "Terra Coffee", "Lumen Optics"];
    var seen = {};
    var pool = ASSETS.filter(function (a) { if (seen[a.sym]) return false; seen[a.sym] = 1; return true; });

    function pick(list) { return list[Math.floor(Math.random() * list.length)]; }

    function row() {
      var asset = pick(pool);
      var eur = [24, 49, 89, 129, 189, 249, 420, 640, 990, 1450, 2100, 3800][Math.floor(Math.random() * 12)];
      eur = eur * (0.85 + Math.random() * 0.3);
      var qty = eur / asset.rate;
      var settled = Math.random() < 0.55;
      var node = document.createElement("div");
      node.className = "feed-row";
      node.innerHTML =
        '<span class="glyph" style="background:' + asset.tint + '">' + asset.sym + "</span>" +
        '<span class="what"><b>' + pick(shops) + " · " + pick(cities) + "</b>" +
        "<span>" + (settled ? "settled" : "confirmed") + " · " + asset.network + "</span></span>" +
        '<span class="amt"><b>€' + eur.toLocaleString("en-GB", { maximumFractionDigits: 0 }) + "</b>" +
        "<span>" + qty.toLocaleString("en-GB", { maximumFractionDigits: asset.dp > 4 ? 5 : asset.dp }) + " " + asset.sym + "</span></span>";
      return node;
    }

    for (var i = 0; i < 7; i++) host.appendChild(row());
    if (reduceMotion) return;
    setInterval(function () {
      host.insertBefore(row(), host.firstChild);
      while (host.children.length > 9) host.removeChild(host.lastChild);
    }, 2600 + Math.random() * 1400);
  }

  /* ---------------------------------------------------------------- rail --- */

  function rail() {
    var wrap = $(".rail");
    if (!wrap) return;
    var fill = $(".rail-fill", wrap), steps = $$(".rail-step", wrap);
    function update() {
      var r = wrap.getBoundingClientRect();
      var mid = window.innerHeight * 0.55;
      var progress = Math.max(0, Math.min(1, (mid - r.top) / r.height));
      if (fill) fill.style.transform = "scaleY(" + progress + ")";
      steps.forEach(function (s) {
        var sr = s.getBoundingClientRect();
        s.classList.toggle("lit", sr.top + 20 < mid);
      });
    }
    window.addEventListener("scroll", update, { passive: true });
    window.addEventListener("resize", update);
    update();
  }

  /* ------------------------------------------------------------ counters --- */

  function counters() {
    var items = $$("[data-count]");
    if (!items.length) return;
    function run(node) {
      var to = parseFloat(node.dataset.count), dp = (node.dataset.dp | 0), suffix = node.dataset.suffix || "";
      var start = performance.now(), dur = reduceMotion ? 1 : 1400;
      (function tick(now) {
        var t = Math.min(1, (now - start) / dur), e = 1 - Math.pow(1 - t, 3);
        node.textContent = (to * e).toLocaleString("en-GB", { minimumFractionDigits: dp, maximumFractionDigits: dp }) + suffix;
        if (t < 1) requestAnimationFrame(tick);
      })(start);
    }
    if (!("IntersectionObserver" in window)) { items.forEach(run); return; }
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (en) { if (en.isIntersecting) { run(en.target); io.unobserve(en.target); } });
    }, { threshold: 0.4 });
    items.forEach(function (n) { io.observe(n); });
  }

  /* ---------------------------------------------------------- currencies --- */

  function currencies() {
    var host = $("#curGrid");
    if (!host) return;
    ASSETS.forEach(function (a) {
      var minutes = a.conf === 1 ? "under a minute" : a.conf <= 4 ? "about " + (a.conf * 10) + " min"
                  : a.conf <= 12 ? "about 3 min" : a.conf <= 20 ? "about 1 min" : "under 30 s";
      var card = document.createElement("article");
      card.className = "struck cur-card spot";
      card.innerHTML =
        '<div class="top"><span class="glyph" style="background:' + a.tint + '">' + a.sym + "</span>" +
        "<div><b>" + a.name + "</b><span>" + a.network + "</span></div></div>" +
        "<dl><dt>Confirmations we wait for</dt><dd>" + a.conf + "</dd>" +
        "<dt>Typical time to final</dt><dd>" + minutes + "</dd>" +
        "<dt>Quote precision</dt><dd>" + a.dp + " decimals</dd>" +
        "<dt>Address format</dt><dd>" + (a.addr === "hex" ? "0x hex" : a.addr) + "</dd></dl>";
      host.appendChild(card);
    });
  }

  /* --------------------------------------------------------- developers --- */

  function developers() {
    var ep = $("#endpointTable");
    if (ep && typeof ENDPOINTS !== "undefined") {
      ep.innerHTML = ENDPOINTS.map(function (e) {
        return "<tr><td data-label='Method'><span class='verb verb-" + e.verb.toLowerCase().replace("delete", "del") + "'>" + e.verb + "</span></td>" +
               "<td data-label='Path'><code>" + e.path + "</code></td>" +
               "<td data-label='What it does'>" + e.text + "</td></tr>";
      }).join("");
    }
    var ev = $("#eventTable");
    if (ev && typeof WEBHOOK_EVENTS !== "undefined") {
      ev.innerHTML = WEBHOOK_EVENTS.map(function (e) {
        return "<tr><td data-label='Event'><code>" + e.name + "</code></td><td data-label='Fires when'>" + e.text + "</td></tr>";
      }).join("");
    }
    var er = $("#errorTable");
    if (er && typeof ERROR_CODES !== "undefined") {
      er.innerHTML = ERROR_CODES.map(function (e) {
        return "<tr><td data-label='Status'><code>" + e.status + "</code></td><td data-label='Code'><code>" + e.code + "</code></td><td data-label='Meaning'>" + e.text + "</td></tr>";
      }).join("");
    }
  }

  /* ------------------------------------------------------------- reveal ---- */

  function reveal() {
    var nodes = $$(".reveal");
    if (!nodes.length) return;
    if (!("IntersectionObserver" in window)) { nodes.forEach(function (n) { n.classList.add("seen"); }); return; }
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (en) { if (en.isIntersecting) { en.target.classList.add("seen"); io.unobserve(en.target); } });
    }, { rootMargin: "0px 0px -10% 0px" });
    nodes.forEach(function (n) { io.observe(n); });
  }

  function boot() {
    drawer(); menus(); currentLinks(); dock();
    sky(); spotlight(); feed(); rail(); counters(); currencies(); developers(); reveal();
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot); else boot();
})();
