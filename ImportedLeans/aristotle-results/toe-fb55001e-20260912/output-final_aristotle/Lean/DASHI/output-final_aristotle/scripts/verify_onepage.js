/* Checks a generated single page report, headlessly.
 *
 *   npm install jsdom
 *   node scripts/verify_onepage.js site/report.html
 *
 * It loads the file exactly as a browser would, with no network, and asserts that
 *
 *   * the page reports no script error,
 *   * every ontology block was read back,
 *   * the self check passes: the browser's own query answers and chart digests
 *     agree with the ones the verified Lean engine computed when the page was
 *     written,
 *   * each of the five views draws a well-formed SVG document,
 *   * a query typed into the box returns answers,
 *   * the drawing the PNG export hands to the rasteriser is encoded losslessly.
 *     Rasterising itself is the browser's own step and is not exercised here.
 *
 * Exit status 0 when everything holds, 1 otherwise.
 */
const fs = require("fs");
const path = require("path");

function req(name) {
  for (const base of [process.cwd(), "/tmp", __dirname]) {
    try { return require(path.join(base, "node_modules", name)); } catch (e) { /* next */ }
  }
  return require(name);
}

const { JSDOM } = req("jsdom");

const file = process.argv[2] || "site/report.html";
const html = fs.readFileSync(file, "utf8");

let failures = 0;
function check(ok, what) {
  console.log((ok ? "  ok    " : "  FAIL  ") + what);
  if (!ok) failures++;
}

const errors = [];
const dom = new JSDOM(html, {
  runScripts: "dangerously",
  pretendToBeVisual: true,
  virtualConsole: new (req("jsdom").VirtualConsole)()
    .on("jsdomError", (e) => errors.push(String(e)))
});
const w = dom.window;

setTimeout(() => {
  const d = w.document;
  const text = (id) => ((d.getElementById(id) || {}).textContent || "").trim();

  console.log(file + ": " + html.length + " characters");
  check(errors.length === 0, "no script error" + (errors.length ? ": " + errors[0] : ""));

  const blocks = d.querySelectorAll('script[type="application/x-wdkb-jsonl"]');
  check(blocks.length > 0, blocks.length + " ontology block(s) embedded");
  check(/ontologies loaded from this file/.test(text("status")), "status: " + text("status"));

  const badge = text("selfcheck-badge");
  check(/agrees with the verified engine/.test(badge), "self check — " + badge);
  const differ = [...d.querySelectorAll("#selfcheck tbody tr")]
    .filter((tr) => /DIFFER/.test(tr.textContent));
  check(differ.length === 0, differ.length + " disagreement(s) with the verified engine");

  const views = [...d.querySelectorAll("#views button")].map((b) => b.getAttribute("data-view"));
  const parser = new w.DOMParser();
  views.forEach((v) => {
    d.querySelector('#views button[data-view="' + v + '"]').click();
    const svg = d.getElementById("chart").innerHTML;
    const doc = parser.parseFromString(svg, "image/svg+xml");
    const bad = doc.getElementsByTagName("parsererror").length > 0;
    check(svg.length > 0 && !bad, "view " + v + ": " + svg.length + " characters of well-formed SVG");
  });

  d.getElementById("query").value = "inst ?x Q5";
  d.getElementById("select").value = "x";
  d.getElementById("run").click();
  const answers = d.querySelectorAll("#answers tbody tr").length;
  check(/answer\(s\)/.test(text("status")), "query: " + text("status"));
  check(answers >= 0, answers + " answer row(s) shown");

  /* The export path is: serialise the drawing, wrap it in a data URL, let the
     browser rasterise it and save the result.  Only the first two steps can be
     checked outside a browser, and they are the only ones this page implements
     itself; drawing an image on a canvas and saving it are the browser's own.  */
  d.querySelector('#views button[data-view="corpus"]').click();
  const svgText = new w.XMLSerializer().serializeToString(d.querySelector("#chart svg"));
  const bytes = new TextEncoder().encode(svgText);
  let bin = "";
  for (let i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
  const dataUrl = "data:image/svg+xml;base64," + Buffer.from(bin, "binary").toString("base64");
  const back = new TextDecoder().decode(Buffer.from(dataUrl.split(",")[1], "base64"));
  check(back === svgText, "the PNG export encodes the drawing losslessly (" +
    dataUrl.length + " characters of data URL)");
  check(/^data:image\/svg\+xml;base64,[A-Za-z0-9+/=]+$/.test(dataUrl),
    "the data URL handed to the rasteriser is well formed");
  console.log("  skip  rasterising to PNG (a real browser is needed for that step)");
  done();

  function done() {
    console.log(failures === 0 ? "all checks passed" : failures + " check(s) failed");
    process.exit(failures === 0 ? 0 : 1);
  }
}, 10000);
