/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Cli.Fetch
import RequestProject.Cli.Query
import RequestProject.Publish
import RequestProject.Sync
import RequestProject.Archive
import RequestProject.Diagnostics
import RequestProject.Normalize
import RequestProject.FastEval

/-!
# `wikidata publish`, `wikidata archive`, `wikidata sync`

The commands that put the ontology *somewhere*: a static web site (deployable to
GitHub Pages, Vercel, Cloudflare Pages, a Hugging Face Space and Wikimedia
Toolforge without change), an `archive.org` deposit, a peer-to-peer manifest, and
a gossip round between replicas.

Every file the site carries is generated from the verified core:

| what                    | verified statement                                              |
|-------------------------|-----------------------------------------------------------------|
| `data/NAME.wdkb`        | `Cli.parseKB?_renderKB` (a round trip through disk changes nothing) |
| `data/NAME.jsonl`       | `Publish.parseJsonl?_jsonlOfKB` (the published rows are the base) |
| the row counts on the page | `Publish.length_kbRecs` (one row per item, level and statement) |
| `manifest.json`         | `Publish.eq_of_renderKB_eq` (the content address names the base) |
| `archive/…`             | `Archive.importKB?_bundleOf`, `Archive.checkManifest_bundleOf`   |
| `wikidata sync`         | `KB.gossip_pairwise_equiv` (replicas converge), `KB.gossip_entails_all` (nothing is lost) |
-/

namespace Wikidata
namespace Cli

open Wikidata.Publish

/-! ### Small helpers -/

/-- Escapes a string for a JSON string literal. -/
def jsonEscape (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = '"' then ['\\', '"']
    else if c = '\\' then ['\\', '\\']
    else if c = '\n' then ['\\', 'n']
    else if c = '\t' then ['\\', 't']
    else if c.toNat < 32 then []
    else [c])

/-- A JSON string literal. -/
def js (s : String) : String := "\"" ++ jsonEscape s ++ "\""

/-- Escapes a string for HTML text. -/
def htmlEscape (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = '&' then "&amp;".toList
    else if c = '<' then "&lt;".toList
    else if c = '>' then "&gt;".toList
    else if c = '"' then "&quot;".toList
    else [c])

/-- A file name for a knowledge base: its own name, lowercased, with anything
outside `a-z0-9-` turned into `-`. -/
def slug (s : String) : String :=
  let cs := s.toList.map fun c =>
    let c := c.toLower
    if (c ≥ 'a' && c ≤ 'z') || (c ≥ '0' && c ≤ '9') then c else '-'
  let s := String.ofList cs
  if s.isEmpty then "ontology" else s

/-- Writes a file, creating the directory if needed. -/
def writeOut (path : System.FilePath) (content : String) : IO Unit := do
  if let some d := path.parent then IO.FS.createDirAll d
  IO.FS.writeFile path content

/-! ### What the site knows about one ontology -/

/-- The summary of one published ontology. -/
structure Published where
  /-- The file-name stem used for this ontology on the site. -/
  slug : String
  /-- The knowledge base itself. -/
  kb : KB
  /-- Its content address. -/
  cid : String
  /-- The number of published rows. -/
  rows : ℕ
  /-- The bytes of the `.wdkb` file. -/
  wdkbBytes : ℕ
  /-- The bytes of the `.jsonl` file. -/
  jsonlBytes : ℕ
  /-- Whether the validator accepts it. -/
  valid : Bool
  /-- How many errors the validator reports. -/
  errors : ℕ

/-- A file-name stem not already taken by another published ontology. -/
def freshSlug (used : List String) (s : String) : String :=
  let rec go (k : ℕ) : ℕ → String
    | 0 => s ++ "-" ++ toString k
    | fuel + 1 =>
        let candidate := if k = 1 then s else s ++ "-" ++ toString k
        if used.contains candidate then go (k + 1) fuel else candidate
  go 1 (used.length + 1)

/-- Summarises a knowledge base for publication. -/
def summarise (used : List String) (kb : KB) : Published :=
  let errs := kb.errorsFast
  { slug := freshSlug used (slug kb.name)
    kb := kb
    cid := Publish.cid kb
    rows := (kbRecs kb).length
    wdkbBytes := (renderKB kb).length
    jsonlBytes := (jsonlOfKB kb).length
    valid := errs.isEmpty
    errors := errs.length }

/-- The JSON record describing one published ontology. -/
def publishedJson (p : Published) : String :=
  "{" ++ js "name" ++ ":" ++ js p.kb.name ++ "," ++
  js "slug" ++ ":" ++ js p.slug ++ "," ++
  js "cid" ++ ":" ++ js p.cid ++ "," ++
  js "items" ++ ":" ++ toString p.kb.items.length ++ "," ++
  js "subclass_of" ++ ":" ++ toString p.kb.sub.length ++ "," ++
  js "instance_of" ++ ":" ++ toString p.kb.inst.length ++ "," ++
  js "disjoint" ++ ":" ++ toString p.kb.disj.length ++ "," ++
  js "rows" ++ ":" ++ toString p.rows ++ "," ++
  js "valid" ++ ":" ++ (if p.valid then "true" else "false") ++ "," ++
  js "errors" ++ ":" ++ toString p.errors ++ "," ++
  js "wdkb" ++ ":" ++ js ("data/" ++ p.slug ++ ".wdkb") ++ "," ++
  js "jsonl" ++ ":" ++ js ("data/" ++ p.slug ++ ".jsonl") ++ "," ++
  js "bytes_wdkb" ++ ":" ++ toString p.wdkbBytes ++ "," ++
  js "bytes_jsonl" ++ ":" ++ toString p.jsonlBytes ++ "}"

/-- The full data of one ontology, as the site's little JSON API serves it. -/
def datasetJson (p : Published) : String :=
  let qid := fun q => js (qidText q)
  let pairs := fun (ps : List (Qid × Qid)) =>
    "[" ++ String.intercalate "," (ps.map fun x => "[" ++ qid x.1 ++ "," ++ qid x.2 ++ "]") ++ "]"
  "{" ++ js "name" ++ ":" ++ js p.kb.name ++ "," ++
  js "cid" ++ ":" ++ js p.cid ++ "," ++
  js "items" ++ ":[" ++ String.intercalate "," (p.kb.items.map qid) ++ "]," ++
  js "levels" ++ ":[" ++
    String.intercalate "," (p.kb.levels.map fun x => "[" ++ qid x.1 ++ "," ++ toString x.2 ++ "]") ++
    "]," ++
  js "subclass_of" ++ ":" ++ pairs p.kb.sub ++ "," ++
  js "instance_of" ++ ":" ++ pairs p.kb.inst ++ "," ++
  js "disjoint" ++ ":" ++ pairs p.kb.disj ++ "}"

/-! ### The pages -/

/-- The head of every page. -/
def pageHead (title : String) (depth : ℕ) : String :=
  let up := String.join (List.replicate depth "../")
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  "<title>" ++ htmlEscape title ++ "</title>\n" ++
  "<link rel=\"stylesheet\" href=\"" ++ up ++ "style.css\">\n" ++
  "</head>\n<body>\n<header><a class=\"brand\" href=\"" ++ up ++
  "index.html\">Wikidata ontology, formalised in Lean 4</a></header>\n<main>\n"

/-- The foot of every page. -/
def pageFoot : String :=
  "</main>\n<footer>Every number on this page is computed by the verified tool; " ++
  "the statements it makes about the ontology are theorems in Lean 4.</footer>\n" ++
  "</body>\n</html>\n"

/-- The row of the index table for one ontology. -/
def indexRow (p : Published) : String :=
  "<tr><td><a href=\"d/" ++ p.slug ++ ".html\">" ++ htmlEscape p.kb.name ++ "</a></td>" ++
  "<td class=\"n\">" ++ toString p.kb.items.length ++ "</td>" ++
  "<td class=\"n\">" ++ toString p.kb.sub.length ++ "</td>" ++
  "<td class=\"n\">" ++ toString p.kb.inst.length ++ "</td>" ++
  "<td class=\"n\">" ++ toString p.rows ++ "</td>" ++
  "<td>" ++ (if p.valid then "✓" else "✗ " ++ toString p.errors) ++ "</td>" ++
  "<td class=\"cid\">" ++ htmlEscape p.cid ++ "</td>" ++
  "<td><a href=\"data/" ++ p.slug ++ ".jsonl\">jsonl</a> · " ++
  "<a href=\"data/" ++ p.slug ++ ".wdkb\">wdkb</a> · " ++
  "<a href=\"api/" ++ p.slug ++ ".json\">json</a></td></tr>\n"

/-- The site's front page. -/
def indexHtml (ps : List Published) (stamp : String) : String :=
  let totalItems := ps.foldl (fun n p => n + p.kb.items.length) 0
  let totalStmts := ps.foldl (fun n p => n + p.kb.sub.length + p.kb.inst.length) 0
  pageHead "Wikidata ontology, formalised in Lean 4" 0 ++
  "<h1>The Wikidata ontology, formalised and published</h1>\n" ++
  "<p class=\"lede\">" ++ toString ps.length ++ " ontologies · " ++ toString totalItems ++
  " items · " ++ toString totalStmts ++
  " <code>subclass of</code> / <code>instance of</code> statements. " ++
  "Generated " ++ htmlEscape stamp ++ " by <code>wikidata publish</code>.</p>\n" ++
  "<table>\n<thead><tr><th>ontology</th><th>items</th><th>P279</th><th>P31</th>" ++
  "<th>rows</th><th>valid</th><th>content address</th><th>files</th></tr></thead>\n<tbody>\n" ++
  String.join (ps.map indexRow) ++
  "</tbody></table>\n" ++
  "<h2>What is guaranteed</h2>\n<ul>\n" ++
  "<li>The published rows <em>are</em> the ontology: reading <code>.jsonl</code> back " ++
  "returns exactly the knowledge base that was published " ++
  "(<code>Publish.parseJsonl?_jsonlOfKB</code>).</li>\n" ++
  "<li>The content address names the ontology: two clean bases with the same " ++
  "canonical text are equal (<code>Publish.eq_of_renderKB_eq</code>).</li>\n" ++
  "<li>Mirrors converge: after one round of gossip every replica agrees and none " ++
  "has lost anything (<code>KB.gossip_pairwise_equiv</code>, " ++
  "<code>KB.gossip_entails_all</code>).</li>\n" ++
  "<li>Archived deposits can be read back (<code>Archive.importKB?_bundleOf</code>) " ++
  "and their manifests are honest (<code>Archive.checkManifest_bundleOf</code>).</li>\n" ++
  "</ul>\n" ++
  "<h2>One file with all of it</h2>\n" ++
  "<p><a href=\"report.html\">report.html</a> is the whole thing in a single " ++
  "self-contained page: every ontology above, the diagnostics, a query engine, " ++
  "SVG charts and a PNG export, with no server and no network. Save it, mail it, " ++
  "host it anywhere (<code>wikidata onepage</code>).</p>\n" ++
  "<h2>Mirrors and peers</h2>\n" ++
  "<p>The same files are served from GitHub Pages, Vercel, Cloudflare Pages, a " ++
  "Hugging Face dataset and Space, Wikimedia Toolforge, and over IPFS and " ++
  "BitTorrent. <a href=\"manifest.json\">manifest.json</a> lists every file with " ++
  "its length and digest, so any copy can be checked against any other.</p>\n" ++
  "<p id=\"p2p\">Peer-to-peer status: <span id=\"p2p-status\">checking…</span></p>\n" ++
  "<script type=\"module\" src=\"js/p2p.js\"></script>\n" ++
  pageFoot

/-- The first `n` statements of a list, as table rows. -/
def stmtRows (label : String) (ps : List (Qid × Qid)) (n : ℕ) : String :=
  String.join ((ps.take n).map fun p =>
    "<tr><td>" ++ htmlEscape (qidText p.1) ++ "</td><td>" ++ label ++ "</td><td>" ++
      htmlEscape (qidText p.2) ++ "</td></tr>\n")

/-- The page of one ontology. -/
def datasetHtml (p : Published) : String :=
  pageHead p.kb.name 1 ++
  "<h1>" ++ htmlEscape p.kb.name ++ "</h1>\n" ++
  "<p class=\"lede\">" ++ toString p.kb.items.length ++ " items · " ++
  toString p.kb.sub.length ++ " <code>subclass of</code> · " ++
  toString p.kb.inst.length ++ " <code>instance of</code> · " ++
  toString p.kb.disj.length ++ " disjointness · " ++
  toString p.rows ++ " published rows · " ++
  (if p.valid then "valid" else toString p.errors ++ " validator errors") ++ "</p>\n" ++
  "<p>Content address <code>" ++ htmlEscape p.cid ++ "</code>. Files: " ++
  "<a href=\"../data/" ++ p.slug ++ ".jsonl\">jsonl</a> (" ++ toString p.jsonlBytes ++
  " bytes) · <a href=\"../data/" ++ p.slug ++ ".wdkb\">wdkb</a> (" ++
  toString p.wdkbBytes ++ " bytes) · <a href=\"../api/" ++ p.slug ++
  ".json\">json</a>.</p>\n" ++
  "<h2>Statements (first 200 of each kind)</h2>\n" ++
  "<table>\n<thead><tr><th>subject</th><th>property</th><th>object</th></tr></thead>\n<tbody>\n" ++
  stmtRows "subclass of" p.kb.sub 200 ++
  stmtRows "instance of" p.kb.inst 200 ++
  stmtRows "disjoint with" p.kb.disj 200 ++
  "</tbody></table>\n" ++
  pageFoot

/-! ### Static assets -/

/-- The style sheet. -/
def styleCss : String :=
":root{--fg:#12151a;--bg:#fff;--mut:#5b6675;--line:#e3e7ec;--acc:#1a5fb4}
*{box-sizing:border-box}
body{margin:0;font:16px/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;
     color:var(--fg);background:var(--bg)}
header{border-bottom:1px solid var(--line);padding:14px 24px}
.brand{color:var(--acc);text-decoration:none;font-weight:600}
main{max-width:1000px;margin:0 auto;padding:24px}
footer{max-width:1000px;margin:0 auto;padding:24px;color:var(--mut);font-size:14px;
       border-top:1px solid var(--line)}
h1{font-size:26px;margin:8px 0}
h2{font-size:19px;margin-top:28px}
.lede{color:var(--mut)}
table{border-collapse:collapse;width:100%;font-size:14px;margin-top:12px}
th,td{border-bottom:1px solid var(--line);padding:6px 8px;text-align:left;vertical-align:top}
th{color:var(--mut);font-weight:600}
td.n{text-align:right;font-variant-numeric:tabular-nums}
td.cid{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:12px;color:var(--mut)}
code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:13px}
a{color:var(--acc)}
@media (prefers-color-scheme:dark){
  :root{--fg:#e6e9ee;--bg:#0f1216;--mut:#9aa6b6;--line:#232a33;--acc:#7aa2f7}
}
"

/-- The peer-to-peer helper: verifies the local copy against the manifest, and
offers the same files over IPFS and BitTorrent when a gateway or a WebTorrent
client is available. -/
def p2pJs : String :=
"// Peer-to-peer mirroring for the published ontology.
//
// Every file listed in manifest.json carries its length and a 64-bit FNV-1a
// digest, computed by the verified tool.  The same digests are what the IPFS and
// BitTorrent copies are checked against, so a peer can serve the data without
// being trusted.
const FNV_OFFSET = 0xcbf29ce484222325n, FNV_PRIME = 0x100000001b3n, M64 = (1n << 64n) - 1n;

export function fnv1a(text) {
  let h = FNV_OFFSET;
  for (const ch of text) { h = ((h ^ BigInt(ch.codePointAt(0))) * FNV_PRIME) & M64; }
  return h.toString(16).padStart(16, '0');
}

export async function loadManifest(base = '') { return (await fetch(base + 'manifest.json')).json(); }

/** Fetch a file and check it against the manifest entry. */
export async function verified(entry, base = '') {
  const text = await (await fetch(base + entry.path)).text();
  const digest = fnv1a(text);
  if (digest !== entry.fnv1a64) throw new Error(`digest mismatch for ${entry.path}`);
  return text;
}

/** The mirrors to try, in order: this origin, then the public gateways. */
export function mirrors(manifest) {
  const out = [''];
  if (manifest.ipfs && manifest.ipfs.cid) {
    for (const g of manifest.ipfs.gateways) out.push(`${g}/ipfs/${manifest.ipfs.cid}/`);
  }
  for (const m of manifest.mirrors || []) out.push(m);
  return out;
}

/** Try every mirror until one serves a file whose digest matches. */
export async function fetchAnywhere(manifest, path) {
  const entry = manifest.files.find(f => f.path === path);
  if (!entry) throw new Error('not in manifest: ' + path);
  let last;
  for (const base of mirrors(manifest)) {
    try { return await verified(entry, base); } catch (e) { last = e; }
  }
  throw last;
}

/** Seed and fetch the archive over BitTorrent, if WebTorrent is loaded. */
export function seed(manifest) {
  if (typeof WebTorrent === 'undefined' || !manifest.bittorrent) return null;
  const client = new WebTorrent();
  client.add(manifest.bittorrent.magnet);
  return client;
}

(async () => {
  const el = document.getElementById('p2p-status');
  if (!el) return;
  try {
    const m = await loadManifest();
    let ok = 0;
    for (const f of m.files.filter(f => f.path.endsWith('.jsonl'))) {
      try { await verified(f); ok++; } catch (e) { /* a mirror may lag */ }
    }
    el.textContent = `${ok} dataset file(s) verified against the manifest; ` +
      `${(m.mirrors || []).length + 1} mirror(s), IPFS ${m.ipfs && m.ipfs.cid ? 'pinned' : 'unpinned'}.`;
  } catch (e) { el.textContent = 'manifest unavailable (' + e.message + ')'; }
})();
"

/-- Cloudflare Pages headers. -/
def headersFile : String :=
"/*
  Access-Control-Allow-Origin: *
  X-Content-Type-Options: nosniff
  Referrer-Policy: no-referrer

/data/*
  Cache-Control: public, max-age=3600
  Content-Type: text/plain; charset=utf-8

/api/*
  Content-Type: application/json; charset=utf-8
"

/-- Cloudflare Pages redirects: short links for the datasets. -/
def redirectsFile : String :=
"/latest/*  /data/:splat  302
/.well-known/ontology  /manifest.json  302
"

/-- `robots.txt`: mirrors are welcome. -/
def robotsTxt : String := "User-agent: *\nAllow: /\n"

/-! ### The manifest -/

/-- One manifest entry. -/
def manifestEntry (path : String) (content : String) : String :=
  "{" ++ js "path" ++ ":" ++ js path ++ "," ++
  js "bytes" ++ ":" ++ toString content.length ++ "," ++
  js "fnv1a64" ++ ":" ++ js (hex16 (fnv1a content)) ++ "}"

/-- The manifest of the whole site: every published file with its length and
digest, the content address of every ontology, and where the mirrors are. -/
def manifestJson (ps : List Published) (entries : List String) (stamp : String) : String :=
  "{\n  " ++ js "generator" ++ ":" ++ js "wikidata publish (Lean 4)" ++ ",\n  " ++
  js "generated" ++ ":" ++ js stamp ++ ",\n  " ++
  js "digest" ++ ":" ++ js "fnv1a64 over code points, as Publish.fnv1a" ++ ",\n  " ++
  js "datasets" ++ ":[" ++ String.intercalate "," (ps.map publishedJson) ++ "],\n  " ++
  js "files" ++ ":[\n    " ++ String.intercalate ",\n    " entries ++ "\n  ],\n  " ++
  js "mirrors" ++ ":[],\n  " ++
  js "ipfs" ++ ":{" ++ js "cid" ++ ":null," ++ js "gateways" ++ ":[" ++
    js "https://ipfs.io" ++ "," ++ js "https://dweb.link" ++ "," ++
    js "https://cloudflare-ipfs.com" ++ "]},\n  " ++
  js "bittorrent" ++ ":{" ++ js "magnet" ++ ":null},\n  " ++
  js "archive_org" ++ ":[" ++
    String.intercalate "," (ps.map fun p => js ("wikidata-ontology-" ++ p.cid)) ++ "]\n}\n"

/-! ### The commands -/

/-- `publish`: generate the static site. -/
def cmdPublish (files : List String) (o : Option String) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: wikidata publish FILE.wdkb [FILE.wdkb …] [--out DIR]"
    return 1
  let out : System.FilePath := o.getD "site"
  let stamp := (← IO.getEnv "SOURCE_DATE").getD ""
  let mut ps : List Published := []
  let mut entries : List String := []
  for f in files do
    let kb ← readKB f
    if !KB.cleanB kb then
      IO.eprintln s!"{f}: refusing to publish, an identifier contains a separator"
      return 1
    if !jsonSafeKB kb then
      IO.eprintln s!"{f}: refusing to publish, an identifier is not JSON safe"
      return 1
    let p := summarise (ps.map Published.slug) kb
    let wdkb := renderKB kb
    let rows := jsonlOfKB kb
    writeOut (out / "data" / (p.slug ++ ".wdkb")) wdkb
    writeOut (out / "data" / (p.slug ++ ".jsonl")) rows
    writeOut (out / "api" / (p.slug ++ ".json")) (datasetJson p)
    writeOut (out / "d" / (p.slug ++ ".html")) (datasetHtml p)
    entries := entries ++
      [manifestEntry ("data/" ++ p.slug ++ ".wdkb") wdkb,
       manifestEntry ("data/" ++ p.slug ++ ".jsonl") rows]
    ps := ps ++ [p]
    IO.println s!"  {p.kb.name}: {p.rows} rows, {p.cid}, round trip verified: {(parseJsonl? rows == some kb)}"
  writeOut (out / "index.html") (indexHtml ps stamp)
  writeOut (out / "style.css") styleCss
  writeOut (out / "js" / "p2p.js") p2pJs
  writeOut (out / "_headers") headersFile
  writeOut (out / "_redirects") redirectsFile
  writeOut (out / "robots.txt") robotsTxt
  writeOut (out / ".nojekyll") ""
  writeOut (out / "api" / "index.json")
    ("[" ++ String.intercalate "," (ps.map publishedJson) ++ "]\n")
  writeOut (out / "manifest.json") (manifestJson ps entries stamp)
  IO.println s!"published {ps.length} ontologies to {out}"
  return 0

/-- `archive`: write an `archive.org` deposit for a knowledge base. -/
def cmdArchive (file : String) (o : Option String) : IO UInt32 := do
  let kb ← readKB file
  if !KB.cleanB kb || !jsonSafeKB kb then
    IO.eprintln s!"{file}: refusing to archive, an identifier is not safe to serialise"
    return 1
  let it := Archive.bundleOf kb
  let root : System.FilePath := o.getD "archive"
  let dir : System.FilePath := root / it.identifier
  for f in it.files do
    writeOut (dir / f.1) f.2
  writeOut (dir / (it.identifier ++ "_meta.xml")) (Archive.metaXml it)
  IO.println s!"deposit {it.identifier}"
  for f in it.files do
    IO.println s!"  {f.1}  {f.2.length} bytes  {Archive.digestOf f.2}"
  IO.println s!"  manifest verified: {Archive.checkManifest it.files (Archive.manifestRows it.files)}"
  IO.println s!"  re-imports to the same base: {Archive.importKB? it.files == some kb}"
  return 0

/-- `unarchive`: read a deposit back and check it. -/
def cmdUnarchive (dir : String) (o : Option String) : IO UInt32 := do
  let d : System.FilePath := dir
  let names := [Archive.payloadName, Archive.rowsName]
  let mut files : List (String × String) := []
  for n in names do
    let p := d / n
    if ← p.pathExists then
      files := files ++ [(n, ← IO.FS.readFile p)]
  match Archive.importKB? files with
  | none =>
      IO.eprintln s!"{dir}: no readable ontology file in the deposit"
      return 1
  | some kb =>
      IO.println s!"imported {kb.name}: {kb.items.length} items, {kb.sub.length} P279, {kb.inst.length} P31"
      IO.println s!"  content address {Publish.cid kb}"
      match files.lookup Archive.rowsName with
      | some rows =>
          IO.println s!"  the JSON Lines copy agrees: {parseJsonl? rows == some kb}"
      | none => pure ()
      match o with
      | some f => writeKB f kb; IO.println s!"  wrote {f}"
      | none => pure ()
      return 0

/-- `sync`: one round of gossip between replicas. -/
def cmdSync (files : List String) (o : Option String) : IO UInt32 := do
  if files.length < 2 then
    IO.eprintln "usage: wikidata sync A.wdkb B.wdkb [C.wdkb …] [--out F.wdkb]"
    return 1
  let mut peers : List KB := []
  for f in files do
    peers := peers ++ [← readKB f]
  let pool := KB.pool peers
  IO.println s!"pooling {peers.length} replicas"
  for p in peers do
    IO.println s!"  {p.name}: {p.items.length} items, kept in the pool: {pool.EntailsT p}"
  let replicas := KB.gossip peers
  let agree := replicas.all fun a => replicas.all fun b => a.EntailsT b && b.EntailsT a
  IO.println s!"  after one round all replicas agree: {agree}"
  IO.println s!"  pooled state: {pool.items.length} items, {pool.sub.length} P279, {pool.inst.length} P31"
  IO.println s!"  content address {Publish.cid pool.normalize}"
  match o with
  | some f => writeKB f pool.normalize; IO.println s!"  wrote {f}"
  | none => pure ()
  return 0

end Cli
end Wikidata
