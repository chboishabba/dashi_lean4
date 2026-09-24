/* The single page Wikidata-ontology report.
 *
 * Everything below runs on data embedded in the same file: the ontologies are
 * carried verbatim, in the JSON Lines format of `wikidata publish`, inside inert
 * <script type="application/x-wdkb-jsonl"> elements, and the diagnostics as the CSV
 * of `wikidata report`.  Nothing is fetched.
 *
 * The query evaluator, the relation closures and the chart renderer reimplement,
 * for the browser, definitions that are proved correct in Lean 4:
 *
 *   subclass of / instance of   Wikidata.KB.isSubclassOf, isInstanceOf   (Engine.lean)
 *   the query language          Wikidata.Query.eval, mem_eval_iff        (Queries.lean)
 *   the surface syntax          Wikidata.Cli.parseAtom?                  (Cli/Query.lean)
 *   the bar chart               Wikidata.Report.svgText                  (ReportFormat.lean)
 *   the digest                  Wikidata.Publish.fnv1a, hex16            (Publish.lean)
 *
 * On load the page re-evaluates the queries whose answers were computed by the
 * verified evaluator when the page was generated, and re-renders the charts whose
 * digests were computed by the verified renderer, and reports whether it agrees.
 */
(function () {
  "use strict";

  /* ----------------------------------------------------------------- helpers */

  var SEP = "\u0001";

  function htmlEscape(s) {
    var out = "", i, c;
    for (i = 0; i < s.length; i++) {
      c = s.charAt(i);
      if (c === "&") out += "&amp;";
      else if (c === "<") out += "&lt;";
      else if (c === ">") out += "&gt;";
      else if (c === '"') out += "&quot;";
      else out += c;
    }
    return out;
  }

  /* FNV-1a over code points, 64 bit, as sixteen hex digits: the digest the
     verified tool computes (Wikidata.Publish.fnv1a / hex16). */
  var MASK64 = (1n << 64n) - 1n;
  function fnv1aHex(s) {
    var h = 14695981039346656037n;
    var prime = 1099511628211n;
    for (var ch of s) {
      h = (h ^ BigInt(ch.codePointAt(0))) & MASK64;
      h = (h * prime) & MASK64;
    }
    var hex = h.toString(16);
    while (hex.length < 16) hex = "0" + hex;
    return hex;
  }

  function el(id) { return document.getElementById(id); }

  function download(name, mime, text) {
    var blob = new Blob([text], { type: mime });
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url;
    a.download = name;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
  }

  /* ------------------------------------------------------------ identifiers */

  /* Reads an identifier from the front of a token list, as Wikidata.Cli.parseQid?
     does; returns [key, text, next index] or null. */
  function readQid(toks, i) {
    var t = toks[i];
    if (t === "wd" && i + 1 < toks.length) {
      return [["wd", toks[i + 1]].join(SEP), toks[i + 1], i + 2];
    }
    if (t === "ont" && i + 1 < toks.length) {
      return [["ont", toks[i + 1]].join(SEP), "ontology:" + toks[i + 1], i + 2];
    }
    if (t === "lvl" && i + 1 < toks.length) {
      return [["lvl", toks[i + 1]].join(SEP), "level-" + toks[i + 1], i + 2];
    }
    if (t === "about") {
      var inner = readQid(toks, i + 1);
      if (!inner) return null;
      return ["about" + SEP + inner[0], "about(" + inner[1] + ")", inner[2]];
    }
    return null;
  }

  /* --------------------------------------------------- reading the payload */

  function parseKb(text) {
    var kb = {
      name: "ontology", items: [], itemSet: new Set(), text: new Map(),
      level: new Map(), sub: [], inst: [], disj: [],
      subKeys: new Set(), instKeys: new Set(),
      parents: new Map(), children: new Map(), classesOf: new Map(),
      supersMemo: new Map()
    };
    var lines = text.split("\n");
    for (var i = 0; i < lines.length; i++) {
      var line = lines[i].trim();
      if (line === "") continue;
      var fields;
      try { fields = JSON.parse(line); } catch (e) { continue; }
      if (!Array.isArray(fields) || fields.length === 0) continue;
      var tag = fields[0];
      var rest = fields.slice(1);
      if (tag === "name") { kb.name = rest[0] || "ontology"; continue; }
      if (tag === "level") {
        var lv = parseInt(rest[0], 10);
        var q = readQid(rest, 1);
        if (q) { remember(kb, q); kb.level.set(q[0], lv); }
        continue;
      }
      var a = readQid(rest, 0);
      if (!a) continue;
      remember(kb, a);
      if (tag === "item") { addItem(kb, a[0]); continue; }
      var b = readQid(rest, a[2]);
      if (!b) continue;
      remember(kb, b);
      if (tag === "sub") {
        kb.sub.push([a[0], b[0]]);
        kb.subKeys.add(a[0] + "|" + b[0]);
        push(kb.parents, a[0], b[0]);
        push(kb.children, b[0], a[0]);
      } else if (tag === "inst") {
        kb.inst.push([a[0], b[0]]);
        kb.instKeys.add(a[0] + "|" + b[0]);
        push(kb.classesOf, a[0], b[0]);
      } else if (tag === "disj") {
        kb.disj.push([a[0], b[0]]);
      }
    }
    return kb;
  }

  function remember(kb, q) { if (!kb.text.has(q[0])) kb.text.set(q[0], q[1]); }
  /* The item list is kept exactly as published, repetitions and all: it is the list
     the verified evaluator enumerates, and the list the counts are taken over. */
  function addItem(kb, key) { kb.itemSet.add(key); kb.items.push(key); }
  function push(m, k, v) {
    var l = m.get(k);
    if (l) l.push(v); else m.set(k, [v]);
  }

  function label(kb, key) { return kb.text.get(key) || key.split(SEP).join(":"); }

  /* ------------------------------------------------- the derived relations */

  /* All superclasses of an item: the reflexive-transitive closure of P279,
     as Wikidata.KB.superclasses computes it. */
  function supers(kb, key) {
    var memo = kb.supersMemo.get(key);
    if (memo) return memo;
    var seen = new Set([key]);
    var stack = [key];
    while (stack.length) {
      var x = stack.pop();
      var ps = kb.parents.get(x);
      if (!ps) continue;
      for (var i = 0; i < ps.length; i++) {
        if (!seen.has(ps[i])) { seen.add(ps[i]); stack.push(ps[i]); }
      }
    }
    kb.supersMemo.set(key, seen);
    return seen;
  }

  function isSubclassOf(kb, a, b) { return supers(kb, a).has(b); }

  function isInstanceOf(kb, a, c) {
    var ds = kb.classesOf.get(a);
    if (!ds) return false;
    for (var i = 0; i < ds.length; i++) if (supers(kb, ds[i]).has(c)) return true;
    return false;
  }

  function isClass(kb, a) { return (kb.level.get(a) || 0) > 0; }

  /* ------------------------------------------------------ the query language */

  var KEYWORDS = { sub: 2, inst: 2, dsub: 2, dinst: 2, ne: 2, "class": 1 };

  /* One atom, in the surface syntax of Wikidata.Cli.parseAtom?. */
  function parseAtom(line) {
    var toks = line.trim().split(/\s+/).filter(function (t) { return t !== ""; });
    if (toks.length === 0) return null;
    var kw = toks[0];
    if (!Object.prototype.hasOwnProperty.call(KEYWORDS, kw)) return null;
    if (toks.length !== KEYWORDS[kw] + 1) return null;
    var terms = toks.slice(1).map(parseTerm);
    return { kw: kw, terms: terms };
  }

  function parseTerm(s) {
    if (s.charAt(0) === "?") return { v: s.slice(1) };
    return { q: ["wd", s].join(SEP) };
  }

  function parseQuery(text) {
    var out = [];
    var lines = text.split("\n");
    for (var i = 0; i < lines.length; i++) {
      var line = lines[i].trim();
      if (line === "" || line.charAt(0) === "#") continue;
      var a = parseAtom(line);
      if (!a) return { error: "cannot read the atom: " + line };
      out.push(a);
    }
    return { atoms: out };
  }

  function atomVars(a) {
    var vs = [];
    for (var i = 0; i < a.terms.length; i++) if (a.terms[i].v) vs.push(a.terms[i].v);
    return vs;
  }

  function queryVars(atoms) {
    var seen = [], i, j, vs;
    for (i = 0; i < atoms.length; i++) {
      vs = atomVars(atoms[i]);
      for (j = 0; j < vs.length; j++) if (seen.indexOf(vs[j]) < 0) seen.push(vs[j]);
    }
    return seen;
  }

  function resolve(env, t) { return t.v ? env.get(t.v) : t.q; }

  function checkAtom(kb, a, env) {
    var x = resolve(env, a.terms[0]);
    if (x === undefined) return false;
    if (a.kw === "class") return isClass(kb, x);
    var y = resolve(env, a.terms[1]);
    if (y === undefined) return false;
    if (a.kw === "sub") return isSubclassOf(kb, x, y);
    if (a.kw === "inst") return isInstanceOf(kb, x, y);
    if (a.kw === "dsub") return kb.subKeys.has(x + "|" + y);
    if (a.kw === "dinst") return kb.instKeys.has(x + "|" + y);
    if (a.kw === "ne") return x !== y;
    return false;
  }

  /* Extends a binding over the variables of an atom, in every way, by the items
     of the base (Wikidata.Query.extendVars). */
  function extendVars(kb, vars, env, out, budget) {
    if (vars.length === 0) { out.push(env); return; }
    var v = vars[0];
    var rest = vars.slice(1);
    if (env.has(v)) { extendVars(kb, rest, env, out, budget); return; }
    for (var i = 0; i < kb.items.length; i++) {
      if (out.length > budget) return;
      var e2 = new Map(env);
      e2.set(v, kb.items[i]);
      extendVars(kb, rest, e2, out, budget);
    }
  }

  var BUDGET = 400000;

  /* The evaluator of Wikidata.Query.eval: every binding of the query's variables
     that satisfies every atom. */
  function evalQuery(kb, atoms) {
    var envs = [new Map()];
    var truncated = false;
    for (var i = 0; i < atoms.length; i++) {
      var next = [];
      var vars = atomVars(atoms[i]);
      for (var j = 0; j < envs.length; j++) {
        var cands = [];
        extendVars(kb, vars, envs[j], cands, BUDGET);
        if (cands.length > BUDGET) truncated = true;
        for (var k = 0; k < cands.length; k++) {
          if (checkAtom(kb, atoms[i], cands[k])) next.push(cands[k]);
        }
        if (next.length > BUDGET) { truncated = true; break; }
      }
      envs = next;
    }
    return { envs: envs, truncated: truncated };
  }

  /* The answers, projected on the output variables and de-duplicated
     (Wikidata.Query.answers). */
  function answers(kb, atoms, outs) {
    var r = evalQuery(kb, atoms);
    var seen = new Set();
    var rows = [];
    for (var i = 0; i < r.envs.length; i++) {
      var row = [];
      for (var j = 0; j < outs.length; j++) {
        var v = r.envs[i].get(outs[j]);
        if (v !== undefined) row.push(v);
      }
      var key = row.join(SEP);
      if (!seen.has(key)) { seen.add(key); rows.push(row); }
    }
    return { rows: rows, truncated: r.truncated };
  }

  /* -------------------------------------------------------------------- CSV */

  function parseCsv(text) {
    var rows = [], row = [], field = "", quoted = false, i = 0;
    while (i < text.length) {
      var c = text.charAt(i);
      if (quoted) {
        if (c === '"') {
          if (text.charAt(i + 1) === '"') { field += '"'; i += 2; continue; }
          quoted = false; i++; continue;
        }
        field += c; i++; continue;
      }
      if (c === '"') { quoted = true; i++; continue; }
      if (c === ",") { row.push(field); field = ""; i++; continue; }
      if (c === "\n") { row.push(field); rows.push(row); row = []; field = ""; i++; continue; }
      if (c === "\r") { i++; continue; }
      field += c; i++;
    }
    if (field !== "" || row.length) { row.push(field); rows.push(row); }
    return rows;
  }

  /* ----------------------------------------------------------------- charts */

  /* The bar chart of Wikidata.Report.svgText, character for character. */
  function svgBars(title, subtitle, bars) {
    var height = 130 + 26 * bars.length;
    var m = 0, i;
    for (i = 0; i < bars.length; i++) if (bars[i].count > m) m = bars[i].count;
    var lines = [
      '<svg xmlns="http://www.w3.org/2000/svg" width="860" height="' + height +
        '" viewBox="0 0 860 ' + height +
        '" font-family="-apple-system,Segoe UI,Helvetica,Arial,sans-serif">',
      '<rect width="860" height="' + height + '" fill="#ffffff"/>',
      '<style>.ttl{font-size:20px;font-weight:600;fill:#1b1b1f}' +
        '.sub{font-size:12px;fill:#5b5b66}.lbl{font-size:12px;fill:#1b1b1f}' +
        '.cnt{font-size:12px;fill:#5b5b66}</style>',
      '<text x="28" y="44" class="ttl">' + htmlEscape(title) + "</text>",
      '<text x="28" y="66" class="sub">' + htmlEscape(subtitle) + "</text>",
      '<line x1="261" y1="92" x2="261" y2="' + (96 + 26 * bars.length) +
        '" stroke="#d7d7de"/>'
    ];
    for (i = 0; i < bars.length; i++) {
      var b = bars[i];
      var y = 96 + 26 * i;
      var w = m === 0 ? 0 : Math.floor((520 * b.count) / m);
      lines.push('<g class="bar">' +
        '<text x="250" y="' + (y + 13) + '" text-anchor="end" class="lbl">' +
          htmlEscape(b.label) + "</text>" +
        '<rect x="262" y="' + (y + 3) + '" width="' + w +
          '" height="16" rx="3" fill="' + htmlEscape(b.colour) + '"/>' +
        '<text x="' + (270 + w) + '" y="' + (y + 16) + '" class="cnt">' + b.count +
          "</text>" +
        "</g>");
    }
    lines.push("</svg>");
    return lines.join("\n");
  }

  /* A drawing of the P279 neighbourhood of an item: its superclasses above it and
     its direct subclasses below. */
  function svgGraph(kb, focus, up, down) {
    var levels = [], seen = new Set([focus]);
    var frontier = [focus];
    var d;
    for (d = 0; d < up && frontier.length; d++) {
      var nextUp = [];
      for (var i = 0; i < frontier.length; i++) {
        var ps = kb.parents.get(frontier[i]) || [];
        for (var j = 0; j < ps.length; j++) {
          if (!seen.has(ps[j])) { seen.add(ps[j]); nextUp.push(ps[j]); }
        }
      }
      if (nextUp.length) levels.unshift(nextUp);
      frontier = nextUp;
    }
    levels.push([focus]);
    frontier = [focus];
    for (d = 0; d < down && frontier.length; d++) {
      var nextDown = [];
      for (var a = 0; a < frontier.length; a++) {
        var cs = kb.children.get(frontier[a]) || [];
        for (var b = 0; b < cs.length; b++) {
          if (!seen.has(cs[b])) { seen.add(cs[b]); nextDown.push(cs[b]); }
        }
      }
      if (nextDown.length) levels.push(nextDown);
      frontier = nextDown;
    }
    var maxRow = 1;
    for (d = 0; d < levels.length; d++) {
      if (levels[d].length > 8) levels[d] = levels[d].slice(0, 8);
      if (levels[d].length > maxRow) maxRow = levels[d].length;
    }
    var boxW = 150, boxH = 34, gapX = 24, gapY = 56;
    var width = Math.max(860, maxRow * (boxW + gapX) + gapX);
    var height = 80 + levels.length * (boxH + gapY);
    var pos = new Map();
    var out = ['<svg xmlns="http://www.w3.org/2000/svg" width="' + width + '" height="' +
      height + '" viewBox="0 0 ' + width + " " + height +
      '" font-family="-apple-system,Segoe UI,Helvetica,Arial,sans-serif">',
      '<rect width="' + width + '" height="' + height + '" fill="#ffffff"/>',
      '<style>.nd{font-size:12px;fill:#1b1b1f}.ttl{font-size:16px;font-weight:600;fill:#1b1b1f}' +
        "</style>",
      '<text x="24" y="34" class="ttl">subclass of (P279) around ' +
        htmlEscape(label(kb, focus)) + "</text>"];
    for (d = 0; d < levels.length; d++) {
      var rowY = 60 + d * (boxH + gapY);
      var rowW = levels[d].length * (boxW + gapX) - gapX;
      var x0 = Math.round((width - rowW) / 2);
      for (var n = 0; n < levels[d].length; n++) {
        var key = levels[d][n];
        var x = x0 + n * (boxW + gapX);
        pos.set(key, { x: x, y: rowY, w: boxW, h: boxH });
      }
    }
    var edges = [];
    pos.forEach(function (p, key) {
      var ps = kb.parents.get(key) || [];
      for (var i2 = 0; i2 < ps.length; i2++) {
        var q = pos.get(ps[i2]);
        if (q) edges.push([p, q]);
      }
    });
    out.push('<defs><marker id="ar" markerWidth="8" markerHeight="8" refX="7" refY="3" ' +
      'orient="auto"><path d="M0,0 L7,3 L0,6 z" fill="#8a8a94"/></marker></defs>');
    for (var e = 0; e < edges.length; e++) {
      var p1 = edges[e][0], p2 = edges[e][1];
      out.push('<line x1="' + (p1.x + p1.w / 2) + '" y1="' + p1.y + '" x2="' +
        (p2.x + p2.w / 2) + '" y2="' + (p2.y + p2.h) +
        '" stroke="#8a8a94" marker-end="url(#ar)"/>');
    }
    pos.forEach(function (p, key) {
      var fill = key === focus ? "#dce6f7" : "#f7f7fa";
      var stroke = key === focus ? "#2b5797" : "#d7d7de";
      var text = label(kb, key);
      if (text.length > 20) text = text.slice(0, 19) + "\u2026";
      out.push('<g><rect x="' + p.x + '" y="' + p.y + '" width="' + p.w + '" height="' + p.h +
        '" rx="5" fill="' + fill + '" stroke="' + stroke + '"/>' +
        '<text x="' + (p.x + p.w / 2) + '" y="' + (p.y + 22) +
        '" text-anchor="middle" class="nd">' + htmlEscape(text) + "</text></g>");
    });
    out.push("</svg>");
    return out.join("\n");
  }

  /* ----------------------------------------------------------- SVG and PNG */

  function currentSvgText() {
    var box = el("chart");
    var svg = box.querySelector("svg");
    return svg ? new XMLSerializer().serializeToString(svg) : null;
  }

  function exportSvg() {
    var text = currentSvgText();
    if (!text) return;
    download(chartFileName() + ".svg", "image/svg+xml;charset=utf-8", text);
  }

  /* A data URL for an SVG document, UTF-8 safe. */
  function svgDataUrl(text) {
    var bytes = new TextEncoder().encode(text);
    var bin = "";
    for (var i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
    return "data:image/svg+xml;base64," + btoa(bin);
  }

  function exportPng(scale) {
    var text = currentSvgText();
    if (!text) return;
    var svg = el("chart").querySelector("svg");
    var w = parseInt(svg.getAttribute("width"), 10) || 860;
    var h = parseInt(svg.getAttribute("height"), 10) || 400;
    var img = new Image();
    var url = svgDataUrl(text);
    img.onload = function () {
      var canvas = document.createElement("canvas");
      canvas.width = w * scale;
      canvas.height = h * scale;
      var ctx = canvas.getContext("2d");
      ctx.fillStyle = "#ffffff";
      ctx.fillRect(0, 0, canvas.width, canvas.height);
      ctx.setTransform(scale, 0, 0, scale, 0, 0);
      ctx.drawImage(img, 0, 0);
      var save = function (href, revoke) {
        var a = document.createElement("a");
        a.href = href;
        a.download = chartFileName() + ".png";
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        if (revoke) setTimeout(function () { URL.revokeObjectURL(href); }, 1000);
      };
      if (canvas.toBlob) {
        canvas.toBlob(function (blob) {
          if (blob) save(URL.createObjectURL(blob), true);
          else save(canvas.toDataURL("image/png"), false);
        }, "image/png");
      } else {
        save(canvas.toDataURL("image/png"), false);
      }
      setStatus("exported " + chartFileName() + ".png at " + canvas.width + "\u00d7" +
        canvas.height);
    };
    img.onerror = function () { setStatus("could not rasterise the chart"); };
    img.src = url;
  }

  function chartFileName() {
    var base = "wikidata-" + state.view;
    if (state.dataset) base += "-" + state.dataset.replace(/[^A-Za-z0-9-]+/g, "-");
    return base.toLowerCase();
  }

  /* ------------------------------------------------------------------ state */

  var META = {};
  var KBS = [];
  var BY_NAME = new Map();
  var DEFECTS = { header: [], rows: [] };
  var state = { dataset: null, view: "corpus", result: null, focus: null };

  function setStatus(msg) { el("status").textContent = msg; }

  /* -------------------------------------------------------------- rendering */

  function renderTable(node, header, rows, cls) {
    if (!rows.length) {
      node.innerHTML = '<p class="hint">no rows</p>';
      return;
    }
    var h = "<table><thead><tr>";
    for (var i = 0; i < header.length; i++) h += "<th>" + htmlEscape(header[i]) + "</th>";
    h += "</tr></thead><tbody>";
    for (var r = 0; r < rows.length; r++) {
      h += "<tr>";
      for (var c = 0; c < rows[r].length; c++) {
        var cell = String(rows[r][c] === undefined ? "" : rows[r][c]);
        var klass = cls ? cls(rows[r], c) : "";
        h += "<td" + (klass ? ' class="' + klass + '"' : "") + ">" + htmlEscape(cell) + "</td>";
      }
      h += "</tr>";
    }
    h += "</tbody></table>";
    node.innerHTML = h;
  }

  function currentKb() { return BY_NAME.get(state.dataset) || KBS[0]; }

  function corpusBars() {
    return KBS.map(function (kb) {
      return { label: kb.name, count: kb.items.length, colour: "#2b5797" };
    });
  }

  function datasetBars(kb) {
    return [
      { label: "items", count: kb.items.length, colour: "#2b5797" },
      { label: "subclass of (P279)", count: kb.sub.length, colour: "#2b5797" },
      { label: "instance of (P31)", count: kb.inst.length, colour: "#2b5797" },
      { label: "disjoint", count: kb.disj.length, colour: "#2b5797" }
    ];
  }

  function defectBars(source) {
    var codeIdx = DEFECTS.header.indexOf("code");
    var sevIdx = DEFECTS.header.indexOf("severity");
    var srcIdx = DEFECTS.header.indexOf("source");
    var counts = new Map(), sev = new Map();
    for (var i = 0; i < DEFECTS.rows.length; i++) {
      var row = DEFECTS.rows[i];
      if (source && srcIdx >= 0 && row[srcIdx] !== source) continue;
      var code = row[codeIdx];
      counts.set(code, (counts.get(code) || 0) + 1);
      if (row[sevIdx] === "error") sev.set(code, "error");
      else if (!sev.has(code)) sev.set(code, "warning");
    }
    var bars = [];
    counts.forEach(function (n, code) {
      bars.push({
        label: code, count: n,
        colour: sev.get(code) === "error" ? "#a4262c" : "#c9930a"
      });
    });
    bars.sort(function (a, b) { return b.count - a.count; });
    return bars;
  }

  function answerBars() {
    if (!state.result || !state.result.rows.length) return [];
    var counts = new Map();
    var kb = currentKb();
    var col = state.result.chartColumn || 0;
    for (var i = 0; i < state.result.rows.length; i++) {
      var v = state.result.rows[i][col];
      if (v === undefined) continue;
      counts.set(v, (counts.get(v) || 0) + 1);
    }
    var bars = [];
    counts.forEach(function (n, v) {
      bars.push({ label: label(kb, v), count: n, colour: "#2b5797" });
    });
    bars.sort(function (a, b) { return b.count - a.count || (a.label < b.label ? -1 : 1); });
    return bars.slice(0, 30);
  }

  function renderChart() {
    var kb = currentKb();
    var svg = "";
    if (state.view === "corpus") {
      var total = KBS.reduce(function (n, k) { return n + k.items.length; }, 0);
      svg = svgBars("Ontologies in this report", KBS.length + " ontologies, " + total +
        " items in all", corpusBars());
    } else if (state.view === "dataset") {
      svg = svgBars(kb.name, kb.items.length + " items, " +
        (kb.sub.length + kb.inst.length) + " P279/P31 statements", datasetBars(kb));
    } else if (state.view === "defects") {
      var bars = defectBars(null);
      var n = bars.reduce(function (m, b) { return m + b.count; }, 0);
      svg = svgBars("Diagnostics by error type", n + " issue(s) over the whole corpus", bars);
    } else if (state.view === "answers") {
      var abars = answerBars();
      svg = svgBars("Query answers",
        state.result ? state.result.rows.length + " answer(s) in " + kb.name
                     : "run a query first", abars);
    } else if (state.view === "graph") {
      var focus = state.focus || (kb.items.length ? kb.items[0] : null);
      svg = focus ? svgGraph(kb, focus, 3, 1) : "";
    }
    el("chart").innerHTML = svg;
    el("chart-digest").textContent = svg ? fnv1aHex(svg) : "";
  }

  function renderSummary() {
    var rows = META.datasets.map(function (d) {
      return [d.name, d.items, d.subclass_of, d.instance_of, d.disjoint,
        d.valid ? "valid" : d.errors + " error(s)", d.cid];
    });
    renderTable(el("summary"),
      ["ontology", "items", "P279", "P31", "disjoint", "validator", "content address"],
      rows);
  }

  function renderDefects() {
    var keep = ["source", "layer", "code", "severity", "status", "subject", "subject label",
      "object", "message", "fix"];
    var idx = keep.map(function (k) { return DEFECTS.header.indexOf(k); })
      .filter(function (i) { return i >= 0; });
    var filter = el("defect-filter").value.toLowerCase();
    var rows = [];
    for (var i = 0; i < DEFECTS.rows.length; i++) {
      var row = DEFECTS.rows[i];
      var text = row.join(" ").toLowerCase();
      if (filter && text.indexOf(filter) < 0) continue;
      rows.push(idx.map(function (j) { return row[j]; }));
      if (rows.length >= 500) break;
    }
    var sevCol = keep.indexOf("severity");
    renderTable(el("defects"), keep, rows, function (r, c) {
      return c === sevCol ? "sev-" + r[sevCol] : "";
    });
    el("defect-count").textContent = DEFECTS.rows.length + " issue(s) in the report" +
      (rows.length < DEFECTS.rows.length ? ", showing " + rows.length : "");
  }

  /* ------------------------------------------------- sharing through the URL */

  /* The view, the ontology and the query, in the fragment of the address, so that
     a copy of this file plus a link reproduces exactly what is on the screen. */
  function writeHash() {
    var parts = ["v=" + encodeURIComponent(state.view)];
    if (state.dataset) parts.push("d=" + encodeURIComponent(state.dataset));
    var q = el("query").value.trim();
    if (q) parts.push("q=" + encodeURIComponent(q));
    var s = el("select").value.trim();
    if (s) parts.push("s=" + encodeURIComponent(s));
    if (state.focus) parts.push("f=" + encodeURIComponent(label(currentKb(), state.focus)));
    try {
      history.replaceState(null, "", "#" + parts.join("&"));
    } catch (e) { /* a file:// page may refuse; the page works all the same */ }
  }

  function readHash() {
    var h = (location.hash || "").replace(/^#/, "");
    if (!h) return null;
    var out = {};
    h.split("&").forEach(function (kv) {
      var i = kv.indexOf("=");
      if (i > 0) out[kv.slice(0, i)] = decodeURIComponent(kv.slice(i + 1));
    });
    return out;
  }

  /* ------------------------------------------------------------- the query */

  function runQuery() {
    var kb = currentKb();
    var parsed = parseQuery(el("query").value);
    if (parsed.error) { setStatus(parsed.error); return; }
    if (!parsed.atoms.length) { setStatus("the query is empty"); return; }
    var outsRaw = el("select").value.trim();
    var outs = outsRaw === ""
      ? queryVars(parsed.atoms)
      : outsRaw.split(/[,\s]+/).map(function (s) {
          return s.charAt(0) === "?" ? s.slice(1) : s;
        }).filter(function (s) { return s !== ""; });
    var t0 = performance.now();
    var res = answers(kb, parsed.atoms, outs);
    var ms = Math.round(performance.now() - t0);
    state.result = { outs: outs, rows: res.rows, chartColumn: 0 };
    var rows = res.rows.slice(0, 1000).map(function (r) {
      return r.map(function (k) { return label(kb, k); });
    });
    renderTable(el("answers"), outs, rows);
    writeHash();
    setStatus(res.rows.length + " answer(s) in " + kb.name + ", " + ms + " ms" +
      (res.truncated ? " (search truncated: too many candidate bindings)" : "") +
      (res.rows.length > 1000 ? ", showing the first 1000" : ""));
    var sel = el("chart-column");
    sel.innerHTML = outs.map(function (v, i) {
      return '<option value="' + i + '">?' + htmlEscape(v) + "</option>";
    }).join("");
    if (state.view === "answers") renderChart();
  }

  function answersCsv() {
    if (!state.result) return "";
    var kb = currentKb();
    var q = function (s) { return '"' + String(s).split('"').join('""') + '"'; };
    var lines = [state.result.outs.map(q).join(",")];
    for (var i = 0; i < state.result.rows.length; i++) {
      lines.push(state.result.rows[i].map(function (k) { return q(label(kb, k)); }).join(","));
    }
    return lines.join("\n");
  }

  function answersJson() {
    if (!state.result) return "[]";
    var kb = currentKb();
    var out = state.result.rows.map(function (row) {
      var o = {};
      for (var i = 0; i < state.result.outs.length; i++) {
        o[state.result.outs[i]] = label(kb, row[i]);
      }
      return o;
    });
    return JSON.stringify(out, null, 1);
  }

  /* --------------------------------------------------------- the self check */

  function selfCheck() {
    var lines = [];
    var ok = true;
    var probes = META.probes || [];
    for (var i = 0; i < probes.length; i++) {
      var p = probes[i];
      var kb = BY_NAME.get(p.dataset);
      if (!kb) continue;
      var parsed = parseQuery(p.query.join("\n"));
      if (parsed.error) { ok = false; lines.push([p.label, p.dataset, "unreadable"]); continue; }
      var got = answers(kb, parsed.atoms, p.outs);
      var mine = got.rows.map(function (r) { return r.join(SEP); }).sort();
      var theirs = p.answers.map(function (r) {
        return r.map(function (t) { return ["wd", t].join(SEP); }).join(SEP);
      }).sort();
      var same = mine.length === theirs.length &&
        mine.every(function (x, j) { return x === theirs[j]; });
      if (!same) ok = false;
      lines.push([p.label, p.dataset, theirs.length + " expected", mine.length + " here",
        same ? "agree" : "DIFFER"]);
    }
    var charts = META.chartDigests || [];
    for (var c = 0; c < charts.length; c++) {
      var ch = charts[c];
      var kb2 = BY_NAME.get(ch.dataset);
      var svg;
      if (ch.kind === "corpus") {
        var total = KBS.reduce(function (n, k) { return n + k.items.length; }, 0);
        svg = svgBars("Ontologies in this report", KBS.length + " ontologies, " + total +
          " items in all", corpusBars());
      } else if (kb2) {
        svg = svgBars(kb2.name, kb2.items.length + " items, " +
          (kb2.sub.length + kb2.inst.length) + " P279/P31 statements", datasetBars(kb2));
      } else continue;
      var digest = fnv1aHex(svg);
      var same2 = digest === ch.digest;
      if (!same2) ok = false;
      lines.push(["chart " + ch.kind, ch.dataset || "\u2014", ch.digest, digest,
        same2 ? "agree" : "DIFFER"]);
    }
    renderTable(el("selfcheck"),
      ["check", "ontology", "verified", "in this browser", "verdict"], lines);
    var badge = el("selfcheck-badge");
    if (!lines.length) {
      badge.className = "badge wait";
      badge.textContent = "no checks shipped with this page";
    } else if (ok) {
      badge.className = "badge ok";
      badge.textContent = "this browser agrees with the verified engine on all " +
        lines.length + " checks";
    } else {
      badge.className = "badge bad";
      badge.textContent = "this browser disagrees with the verified engine";
    }
  }

  /* ------------------------------------------------------------------ setup */

  function boot() {
    META = JSON.parse(el("wd-meta").textContent);
    var blocks = document.querySelectorAll('script[type="application/x-wdkb-jsonl"]');
    for (var i = 0; i < blocks.length; i++) {
      var kb = parseKb(blocks[i].textContent);
      KBS.push(kb);
      BY_NAME.set(kb.name, kb);
    }
    var csv = el("wd-defects");
    if (csv) {
      var rows = parseCsv(csv.textContent.replace(/^\n/, ""));
      if (rows.length) { DEFECTS.header = rows[0]; DEFECTS.rows = rows.slice(1); }
    }
    state.dataset = KBS.length ? KBS[0].name : null;

    el("dataset").innerHTML = KBS.map(function (kb) {
      return '<option value="' + htmlEscape(kb.name) + '">' + htmlEscape(kb.name) +
        " (" + kb.items.length + " items)</option>";
    }).join("");
    el("dataset").addEventListener("change", function () {
      state.dataset = this.value;
      state.focus = null;
      el("focus").value = "";
      renderChart();
      writeHash();
    });
    el("run").addEventListener("click", runQuery);
    el("query").addEventListener("keydown", function (ev) {
      if ((ev.metaKey || ev.ctrlKey) && ev.key === "Enter") runQuery();
    });
    el("export-svg").addEventListener("click", exportSvg);
    var copy = el("copy-link");
    if (copy) {
      copy.addEventListener("click", function () {
        writeHash();
        var url = location.href;
        if (navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(url).then(function () {
            setStatus("link to this view copied");
          }, function () { setStatus(url); });
        } else {
          setStatus(url);
        }
      });
    }
    el("export-png").addEventListener("click", function () { exportPng(2); });
    el("export-png4").addEventListener("click", function () { exportPng(4); });
    el("export-csv").addEventListener("click", function () {
      download("wikidata-answers.csv", "text/csv;charset=utf-8", answersCsv());
    });
    el("export-json").addEventListener("click", function () {
      download("wikidata-answers.json", "application/json;charset=utf-8", answersJson());
    });
    el("chart-column").addEventListener("change", function () {
      if (state.result) state.result.chartColumn = parseInt(this.value, 10) || 0;
      if (state.view === "answers") renderChart();
    });
    el("defect-filter").addEventListener("input", renderDefects);
    el("focus").addEventListener("change", function () {
      var kb = currentKb();
      var wanted = this.value.trim();
      var key = ["wd", wanted].join(SEP);
      state.focus = kb.itemSet.has(key) ? key : null;
      if (!state.focus && wanted !== "") setStatus("no such item in " + kb.name + ": " + wanted);
      state.view = "graph";
      syncTabs();
      renderChart();
      writeHash();
    });
    var tabs = document.querySelectorAll("#views button");
    for (var t = 0; t < tabs.length; t++) {
      tabs[t].addEventListener("click", function () {
        state.view = this.getAttribute("data-view");
        syncTabs();
        renderChart();
        writeHash();
      });
    }
    document.querySelectorAll("[data-example]").forEach(function (b) {
      b.addEventListener("click", function () {
        el("query").value = this.getAttribute("data-example");
        el("select").value = this.getAttribute("data-select") || "";
        runQuery();
      });
    });

    renderSummary();
    renderDefects();

    var hash = readHash();
    if (hash) {
      if (hash.d && BY_NAME.has(hash.d)) { state.dataset = hash.d; el("dataset").value = hash.d; }
      if (hash.q) el("query").value = hash.q;
      if (hash.s !== undefined) el("select").value = hash.s;
      if (hash.v) state.view = hash.v;
      if (hash.f) {
        var fkey = ["wd", hash.f].join(SEP);
        el("focus").value = hash.f;
        if (currentKb().itemSet.has(fkey)) state.focus = fkey;
      }
    }

    syncTabs();
    renderChart();
    setStatus("ready — " + KBS.length + " ontologies loaded from this file");
    if (hash && hash.q) runQuery();
    setTimeout(selfCheck, 0);
  }

  function syncTabs() {
    var tabs = document.querySelectorAll("#views button");
    for (var t = 0; t < tabs.length; t++) {
      tabs[t].setAttribute("aria-selected",
        tabs[t].getAttribute("data-view") === state.view ? "true" : "false");
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", boot);
  } else {
    boot();
  }
})();
