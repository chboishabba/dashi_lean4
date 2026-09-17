/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.OnePage
import RequestProject.Cli.Publish
import RequestProject.Cli.ReportCmd
import RequestProject.Cli.EnrichCmd

/-!
# `wikidata onepage` — the whole report as one HTML file

This command writes **one** file.  It carries the ontologies, the diagnostics, a
query engine, a chart renderer and the export buttons inside itself, so it can be
opened from a local disk or dropped on any static host with no server, no build
step and no network access.

What it embeds, and what is proved about the embedding:

| in the page | guarantee |
|---|---|
| each ontology, as JSON Lines in an inert `<script>` | `Wikidata.OnePage.parseJsonl?_blockPayload_dataBlock` — reading the block back returns exactly that ontology |
| the whole corpus | `Wikidata.OnePage.parseDocs?_sanitize_docs` |
| the payload cannot break out of its element | `Wikidata.OnePage.scriptSafeB_sanitize`, and `Wikidata.OnePage.sanitize_eq_self`: on published data the precaution changes nothing |
| the diagnostics, as the CSV of `wikidata report` | `Wikidata.Report.parseCsvText_csvText` |
| the charts | `Wikidata.OnePage.corpusBars_length`, `corpusBars_count_sum`, `kbBars_count_sum`, `Wikidata.Report.svgBarLines_length` |
| the golden answers the browser re-checks | `Wikidata.OnePage.mem_probe_iff`, `Wikidata.Query.mem_eval_iff` |

The browser's own query evaluator and chart renderer are ordinary JavaScript, so
they are *checked*, not proved: the page ships answers computed here by the
certified evaluator and digests of charts drawn here by the certified renderer, and
re-computes both on load, showing whether they agree.
-/

namespace Wikidata
namespace Cli

open Wikidata.Publish Wikidata.OnePage

/-! ### The queries whose answers are shipped for checking -/

/-- A probe: a named query, run when the page is generated so that the browser can
re-run it and compare. -/
structure Probe where
  /-- What the query is about, for the reader. -/
  label : String
  /-- The query, as atoms of the surface syntax. -/
  query : Query.BGP
  /-- The variables to report. -/
  outs : List String

/-- The probes shipped with every page: one-variable queries, so that
`Wikidata.OnePage.mem_probe_iff` says exactly what their answers mean. -/
def probes : List Probe :=
  [{ label := "classes (metaclass level at least 1)", query := [.isClass (.var "x")],
     outs := ["x"] },
   { label := "instances of human (Q5)",
     query := [.inst (.var "x") (.item (.wd "Q5"))], outs := ["x"] },
   { label := "subclasses of entity (Q35120)",
     query := [.sub (.var "x") (.item (.wd "Q35120"))], outs := ["x"] },
   { label := "subclasses of human (Q5)",
     query := [.sub (.var "x") (.item (.wd "Q5"))], outs := ["x"] }]

/-- A plain Wikidata identifier, when that is what the item is. -/
def qidWd? : Qid → Option String
  | .wd id => some id
  | _ => none

/-- The answers of a probe, as plain identifiers — `none` if some answer is not a
plain Wikidata item, or if there are too many to ship. -/
def probeRows? (limit : ℕ) (kb : KB) (p : Probe) : Option (List (List String)) :=
  let rows := OnePage.probeAnswers kb p.query p.outs
  if rows.length > limit then none else rows.mapM (fun r => r.mapM qidWd?)

/-! ### JSON -/

/-- A JSON array. -/
def jsonArr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

/-- A JSON array of strings. -/
def jsonStrs (xs : List String) : String := jsonArr (xs.map js)

/-- The JSON record describing one probe on one ontology. -/
def probeJson (name : String) (p : Probe) (rows : List (List String)) : String :=
  "{" ++ js "label" ++ ":" ++ js p.label ++ "," ++
  js "dataset" ++ ":" ++ js name ++ "," ++
  js "query" ++ ":" ++ jsonStrs (showQuery p.query) ++ "," ++
  js "outs" ++ ":" ++ jsonStrs p.outs ++ "," ++
  js "answers" ++ ":" ++ jsonArr (rows.map jsonStrs) ++ "}"

/-! ### The charts drawn here, for the browser to reproduce -/

/-- The subtitle of the corpus chart. -/
def corpusSubtitle (kbs : List KB) : String :=
  let total := kbs.foldl (fun n kb => n + kb.items.length) 0
  toString kbs.length ++ " ontologies, " ++ toString total ++ " items in all"

/-- The corpus chart: one bar per ontology. -/
def corpusChart (kbs : List KB) : String :=
  Report.svgText "Ontologies in this report" (corpusSubtitle kbs) (OnePage.corpusBars kbs)

/-- The subtitle of the chart of one ontology. -/
def datasetSubtitle (kb : KB) : String :=
  toString kb.items.length ++ " items, " ++
    toString (kb.sub.length + kb.inst.length) ++ " P279/P31 statements"

/-- The chart of one ontology: its items and its three kinds of statement. -/
def datasetChart (kb : KB) : String :=
  Report.svgText kb.name (datasetSubtitle kb) (OnePage.kbBars kb)

/-- The digest of a chart, in the form the page compares against. -/
def chartDigestJson (kind : String) (name : String) (svg : String) : String :=
  "{" ++ js "kind" ++ ":" ++ js kind ++ "," ++
  js "dataset" ++ ":" ++ js name ++ "," ++
  js "digest" ++ ":" ++ js (hex16 (fnv1a svg)) ++ "}"

/-! ### The page -/

/-- The metadata block: the summaries, the golden answers and the chart digests. -/
def metaJson (stamp : String) (ps : List Published) : String :=
  let kbs := ps.map Published.kb
  let probeEntries : List String :=
    kbs.flatMap fun kb =>
      probes.filterMap fun p =>
        (probeRows? 1500 kb p).map fun rows => probeJson kb.name p rows
  let digests : List String :=
    chartDigestJson "corpus" "" (corpusChart kbs) ::
      kbs.map fun kb => chartDigestJson "dataset" kb.name (datasetChart kb)
  "{" ++ js "generated" ++ ":" ++ js stamp ++ "," ++
  js "tool" ++ ":" ++ js "wikidata onepage" ++ "," ++
  js "datasets" ++ ":" ++ jsonArr (ps.map publishedJson) ++ "," ++
  js "probes" ++ ":" ++ jsonArr probeEntries ++ "," ++
  js "chartDigests" ++ ":" ++ jsonArr digests ++ "}"

/-- An inert element carrying one ontology, verbatim, as JSON Lines. -/
def kbBlock (kb : KB) : String := OnePage.dataBlock kb.name (jsonlOfKB kb)

/-- The example queries offered by the page. -/
def exampleButtons : String :=
  let ex := fun (labelText : String) (q : String) (sel : String) =>
    "<button data-example=\"" ++ Report.htmlEscape q ++ "\" data-select=\"" ++
      Report.htmlEscape sel ++ "\">" ++ Report.htmlEscape labelText ++ "</button>"
  String.join
    [ex "instances of Q5" "inst ?x Q5" "x",
     ex "subclasses of Q5" "sub ?x Q5" "x",
     ex "classes" "class ?x" "x",
     ex "humans that are classes" "inst ?x Q5\nclass ?x" "x",
     ex "direct P31 of Q42" "dinst Q42 ?c" "c"]

/-- The body of the page: the controls, the tables and the chart. -/
def pageBody : String :=
  "<main>\n" ++
  "<div class=\"row\">\n" ++
  "<div class=\"col panel\">\n" ++
  "<h2 style=\"margin-top:0\">Query</h2>\n" ++
  "<label for=\"dataset\">ontology</label><select id=\"dataset\"></select>\n" ++
  "<label for=\"query\">query — one atom per line</label>\n" ++
  "<textarea id=\"query\" spellcheck=\"false\">inst ?x Q5</textarea>\n" ++
  "<label for=\"select\">report these variables (blank: all)</label>\n" ++
  "<input id=\"select\" value=\"x\" spellcheck=\"false\">\n" ++
  "<div class=\"buttons\"><button id=\"run\" class=\"primary\">Run</button>" ++
  "<button id=\"export-csv\">Answers as CSV</button>" ++
  "<button id=\"export-json\">Answers as JSON</button></div>\n" ++
  "<p class=\"hint\">Atoms: <code>sub</code>, <code>inst</code> (the derived, " ++
  "transitive relations), <code>dsub</code>, <code>dinst</code> (only what is " ++
  "directly asserted), <code>class T</code>, <code>ne A B</code>. A term is " ++
  "<code>?name</code> or an item identifier. Ctrl/⌘+Enter runs the query.</p>\n" ++
  "<div class=\"buttons\">" ++ exampleButtons ++ "</div>\n" ++
  "<p class=\"hint\" id=\"status\">loading…</p>\n" ++
  "</div>\n" ++
  "<div class=\"col panel\">\n" ++
  "<h2 style=\"margin-top:0\">Chart</h2>\n" ++
  "<div class=\"tabs\" id=\"views\">" ++
  "<button data-view=\"corpus\">corpus</button>" ++
  "<button data-view=\"dataset\">ontology</button>" ++
  "<button data-view=\"defects\">diagnostics</button>" ++
  "<button data-view=\"answers\">answers</button>" ++
  "<button data-view=\"graph\">P279 graph</button></div>\n" ++
  "<label for=\"chart-column\">chart the answers by</label>" ++
  "<select id=\"chart-column\"></select>\n" ++
  "<label for=\"focus\">centre the graph on an item (e.g. Q5)</label>" ++
  "<input id=\"focus\" spellcheck=\"false\">\n" ++
  "<div class=\"buttons\">" ++
  "<button id=\"export-png\" class=\"primary\">Export PNG (2×)</button>" ++
  "<button id=\"export-png4\">PNG (4×)</button>" ++
  "<button id=\"export-svg\">Download SVG</button>" ++
  "<button id=\"copy-link\">Copy link to this view</button></div>\n" ++
  "<p class=\"hint\">digest of the drawing: <span class=\"mono\" id=\"chart-digest\">" ++
  "</span></p>\n" ++
  "</div>\n" ++
  "</div>\n" ++
  "<div class=\"chartbox\" id=\"chart\"></div>\n" ++
  "<h2>Answers</h2>\n<div class=\"scroll\" id=\"answers\"></div>\n" ++
  "<h2>The ontologies in this file</h2>\n<div class=\"scroll\" id=\"summary\"></div>\n" ++
  "<h2>Diagnostics</h2>\n" ++
  "<label for=\"defect-filter\">filter</label><input id=\"defect-filter\" " ++
  "placeholder=\"code, item, message…\" spellcheck=\"false\">\n" ++
  "<p class=\"hint\" id=\"defect-count\"></p>\n" ++
  "<div class=\"scroll\" id=\"defects\"></div>\n" ++
  "<h2>Does this browser agree with the verified engine? " ++
  "<span class=\"badge wait\" id=\"selfcheck-badge\">checking…</span></h2>\n" ++
  "<p class=\"hint\">The answers and the chart digests below were computed by the " ++
  "Lean 4 engine when this file was written; the page recomputes them in your " ++
  "browser and compares.</p>\n" ++
  "<div class=\"scroll\" id=\"selfcheck\"></div>\n" ++
  "</main>\n"

/-- What the page says about itself. -/
def pageFooterText : String :=
  "<footer>\n<p>Every number here is computed from data carried inside this file. " ++
  "Reading a data block back returns exactly the ontology that was published " ++
  "(<code>Wikidata.OnePage.parseJsonl?_blockPayload_dataBlock</code>); the corpus as " ++
  "a whole round-trips (<code>Wikidata.OnePage.parseDocs?_sanitize_docs</code>); the " ++
  "payload cannot escape its element " ++
  "(<code>Wikidata.OnePage.scriptSafeB_sanitize</code>) and the precaution changes " ++
  "nothing (<code>Wikidata.OnePage.sanitize_eq_self</code>); the diagnostics table " ++
  "reads back as written (<code>Wikidata.Report.parseCsvText_csvText</code>); the " ++
  "charts draw one bar per entry and their bars add up " ++
  "(<code>Wikidata.OnePage.corpusBars_count_sum</code>, " ++
  "<code>Wikidata.Report.svgBarLines_length</code>); and a one-variable query " ++
  "answers with exactly the items that satisfy it " ++
  "(<code>Wikidata.OnePage.mem_probe_iff</code>, " ++
  "<code>Wikidata.Query.mem_eval_iff</code>).</p>\n" ++
  "<p>The query engine and the chart renderer running in your browser are " ++
  "JavaScript, and are checked rather than proved: the page ships answers and " ++
  "chart digests computed by the verified engine and compares them with its own.</p>\n" ++
  "</footer>\n"

/-- Whether a text can be inlined in an element of the given raw-text kind: what
ends such an element is its own closing tag, and nothing else. -/
def endTagFree (tag : String) (s : String) : Bool :=
  (s.toLower.splitOn ("</" ++ tag)).length == 1

/-- The complete single page report.  The stylesheet and the script are inlined
verbatim — the command checks first that neither carries a closing tag of its own
kind (`Wikidata.Cli.endTagFree`) — while the data, the diagnostics and the metadata
are sanitised, which by `Wikidata.OnePage.sanitize_eq_self` changes nothing in
them. -/
def onepageHtml (title : String) (stamp : String) (css : String) (jsSrc : String)
    (ps : List Published) (defectsCsv : String) : String :=
  let kbs := ps.map Published.kb
  let totalItems := kbs.foldl (fun n kb => n + kb.items.length) 0
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  "<title>" ++ Report.htmlEscape title ++ "</title>\n<style>\n" ++
  css ++ "\n</style>\n</head>\n<body>\n" ++
  "<header>\n<h1>" ++ Report.htmlEscape title ++ "</h1>\n<p>" ++
  toString ps.length ++ " ontologies · " ++ toString totalItems ++ " items · " ++
  "generated " ++ Report.htmlEscape stamp ++ " by <code>wikidata onepage</code>. " ++
  "This file is self-contained: no network, no server, no other file.</p>\n</header>\n" ++
  pageBody ++ pageFooterText ++
  String.join (kbs.map kbBlock) ++
  "<script type=\"text/csv\" id=\"wd-defects\">\n" ++ OnePage.sanitize defectsCsv ++
  "\n</script>\n" ++
  "<script type=\"application/json\" id=\"wd-meta\">\n" ++
  OnePage.sanitize (metaJson stamp ps) ++ "\n</script>\n" ++
  "<script>\n" ++ jsSrc ++ "\n</script>\n</body>\n</html>\n"

/-! ### Sanity checks the command runs before writing -/

/-- Whether every ontology can be embedded verbatim. -/
def allWebSafe (kbs : List KB) : Bool := kbs.all OnePage.webSafeKB

/-- **What the command writes is what it read**: for a web safe ontology, the block
the page carries parses back to that ontology. -/
theorem kbBlock_roundTrip {kb : KB} (h : OnePage.webSafeKB kb = true) :
    parseJsonl? (OnePage.blockPayload kb.name (kbBlock kb)) = some kb :=
  OnePage.parseJsonl?_blockPayload_dataBlock h kb.name

/-! ### The command -/

/-- Fills in the source file and the English labels of a report row.  Labels come
from the downloaded glossary and appear only in the label columns. -/
def decorateReportRow (src : String) (r : Report.Row) : Report.Row :=
  { r with source := src, subjectLabel := glossLabel r.subject,
           objectLabel := glossLabel r.object }

/-- Reads one of the two inlined assets, falling back on an empty string with a
warning when it is missing. -/
def readAsset (path : System.FilePath) : IO String := do
  if ← path.pathExists then
    IO.FS.readFile path
  else
    IO.eprintln s!"warning: {path} not found, the page will be written without it"
    return ""

/-- `onepage`: write the whole report as one self-contained HTML file.

Every ontology is embedded verbatim as the JSON Lines of `wikidata publish`, and
the command checks, base by base, that reading the block back out of the page
returns the base it started from (`Wikidata.Cli.kbBlock_roundTrip`). -/
def cmdOnePage (files : List String) (out : Option String) (assets : String)
    (title? : Option String) (warn : Option Bool) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln
      "usage: wikidata onepage FILE.wdkb [FILE.wdkb …] [--out F.html] [--assets DIR]"
    return 1
  let outPath : System.FilePath := out.getD "site/report.html"
  let assetDir : System.FilePath := assets
  let stamp := (← IO.getEnv "SOURCE_DATE").getD ""
  let mut ps : List Published := []
  let mut rows : List Report.Row := []
  for f in files do
    let kb ← baseOfPath f
    if !OnePage.webSafeKB kb then
      IO.eprintln s!"{f}: refusing to embed, an identifier is not safe to inline"
      return 1
    let p := summarise (ps.map Published.slug) kb
    let block := kbBlock kb
    let backAgain := parseJsonl? (OnePage.blockPayload kb.name block) == some kb
    if !backAgain then
      IO.eprintln s!"{f}: refusing to embed, the block does not read back"
      return 1
    let (_, rs) ← rowsOfPath f warn
    rows := rows ++ rs.map (decorateReportRow f)
    ps := ps ++ [p]
    IO.println s!"  {kb.name}: {p.rows} rows, {p.cid}, read back from the page: {backAgain}"
  let css ← readAsset (assetDir / "onepage.css")
  let jsSrc ← readAsset (assetDir / "onepage.js")
  if !endTagFree "style" css then
    IO.eprintln "refusing to inline the stylesheet: it carries a </style tag"
    return 1
  if !endTagFree "script" jsSrc then
    IO.eprintln "refusing to inline the script: it carries a </script tag"
    return 1
  let title := title?.getD "The Wikidata ontology — report"
  let csv := Report.csvOfRows rows
  let html := onepageHtml title stamp css jsSrc ps csv
  writeOut outPath html
  let errs := countSeverity rows .error
  IO.println s!"wrote {outPath}: {ps.length} ontologies, {rows.length} issue(s) \
({errs} error(s)), {html.length} characters, self-contained"
  return 0

end Cli
end Wikidata
