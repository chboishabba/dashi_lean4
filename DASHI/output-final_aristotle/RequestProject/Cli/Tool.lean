import RequestProject.Cli.Fetch
import RequestProject.Cli.Derive
import RequestProject.Cli.Codegen
import RequestProject.Cli.Query
import RequestProject.Cli.EnrichCmd
import RequestProject.Cli.SeriesFormat
import RequestProject.Cli.ReportCmd
import RequestProject.Cli.WorklistCmd
import RequestProject.Cli.RepairCmd
import RequestProject.Cli.WikiCmd
import RequestProject.Cli.Publish
import RequestProject.Cli.OnePage
import RequestProject.Generated.Glossary
import RequestProject.Normalize
import RequestProject.Modules
import RequestProject.Diagnostics
import RequestProject.SeriesDiagnostics

/-!
# `wikidata` — the command line tool

A small program for working with the Wikidata ontology from the shell:

```
wikidata fetch Q42 --depth 3 --out douglas.wdkb   # download from the API
wikidata check douglas.wdkb                       # validate
wikidata derive douglas.wdkb --out closed.wdkb    # construct the new facts
wikidata ask douglas.wdkb subclass Q5 Q35120      # query
wikidata why douglas.wdkb Q5 Q35120               # a checked explanation
```

Each command is a thin shell around the verified core:

| command   | verified statement                                                    |
|-----------|-----------------------------------------------------------------------|
| `fetch`, `import` | `Cli.sub_kbOfEntities_iff`, `Cli.inst_kbOfEntities_iff` (no invented facts), `Cli.kbOfEntities_wellFormed` |
| `check`   | `KB.errors_eq_nil_iff_valid` (empty report ⟺ valid)                    |
| `derive`  | `KB.newSubL_sound`, `KB.saturate_isSubclassOf`, `KB.saturate_valid`, `KB.newSubL_saturate` |
| `ask`     | `KB.isSubclassOf_iff`, `KB.isInstanceOf_iff` (the answers are the derived facts) |
| `query`   | `Query.mem_eval_iff` (the answers are exactly the satisfying assignments), `Query.evalT_eq_eval`, `Cli.parseAtom?_showAtom` |
| `why`     | `KB.checkSubChain_sound` (the printed chain really is a derivation)    |
| `merge`   | `KB.merge_entails_left`, `KB.merge_entails_right` (nothing is lost)    |
| `module`  | `KB.moduleOf_isSubclassOf`, `KB.moduleOf_isInstanceOf` (the extracted module answers as the whole base), `KB.moduleOf_valid` |
| `series`  | `SKB.mem_chainFrom_iff` (the chain printed is exactly the items that come after), `SKB.exists_unique_origin` |
| `gloss`   | `Grounded.lookup_unique` (each identifier gets the one entry that carries it), `Grounded.corpus_covered` |
| `scheck`  | `SKB.report_eq_nil_iff_sValid` (empty report ⟺ the series layer is valid) |
| load/save | `Cli.parseKB?_renderKB`, `Cli.parseSKB?_renderSKB` (a round trip through disk changes nothing) |
| `publish` | `Publish.parseJsonl?_jsonlOfKB` (the published rows are the ontology), `Publish.length_kbRecs` (one row per item, level and statement), `Publish.eq_of_renderKB_eq` (the content address names the base) |
| `archive` / `unarchive` | `Archive.importKB?_bundleOf` (a deposit re-imports to what was deposited), `Archive.importKB?_rows_only`, `Archive.checkManifest_bundleOf` (the manifest is honest) |
| `sync`    | `KB.gossip_pairwise_equiv` (replicas converge), `KB.gossip_entails_all` (nothing is lost), `KB.sync_least` (nothing is invented) |
-/

namespace Wikidata
namespace Cli

/-! ### Display -/

/-- An item identifier, for humans. -/
def showQid : Qid → String := qidText

/-- A diagnostic, for humans.  The issues themselves come from
`RequestProject.Diagnostics`, whose report is proved to be empty exactly when the
knowledge base is valid. -/
def showIssue (kb : KB) : Issue → String
  | .danglingSub a b =>
      s!"undeclared item in `subclass of` statement {showQid a} ⊑ {showQid b}"
  | .danglingInst a c =>
      s!"undeclared item in `instance of` statement {showQid a} : {showQid c}"
  | .danglingDisj c d =>
      s!"undeclared item in disjointness declaration {showQid c} ⊥ {showQid d}"
  | .levelMismatchInst a c =>
      s!"level violation: {showQid a} (level {kb.levelOf a}) is an instance of {showQid c} (level {kb.levelOf c}); expected level {kb.levelOf a + 1}"
  | .levelMismatchSub a b =>
      s!"level violation: {showQid a} (level {kb.levelOf a}) ⊑ {showQid b} (level {kb.levelOf b}); a subclass must be a class of the same positive level"
  | .subclassCycle a b =>
      s!"subclass cycle: {showQid a} and {showQid b} are subclasses of each other"
  | .disjointViolation c d a =>
      s!"{showQid a} is an instance of the disjoint classes {showQid c} and {showQid d}"
  | .redundantSubclass a b =>
      s!"redundant statement: {showQid a} ⊑ {showQid b} already follows from the others"

/-- A series-layer diagnostic, for humans.  The issues come from
`RequestProject.SeriesDiagnostics`, whose report is proved to be empty exactly when the
series layer is valid. -/
def showSeriesIssue : SeriesIssue → String
  | .danglingSeries a t =>
      s!"undeclared item in `part of the series` statement {showQid a} ∈ {showQid t}"
  | .danglingFollows a b =>
      s!"undeclared item in `follows` statement {showQid a} after {showQid b}"
  | .danglingOrdinal a => s!"`series ordinal` given for the undeclared item {showQid a}"
  | .selfFollows a => s!"{showQid a} is declared to follow itself"
  | .seriesCycle a b =>
      s!"series cycle: {showQid a} and {showQid b} each come after the other"
  | .forkedSeries a b c =>
      s!"forking series: {showQid a} is declared to follow both {showQid b} and {showQid c}"
  | .seriesMismatch a b =>
      s!"{showQid a} follows {showQid b}, but the two are in different series"
  | .taxonomicFollows a b =>
      s!"{showQid a} follows {showQid b}, but the two are already related by `subclass of` or `instance of`"
  | .ordinalConflict a b =>
      s!"{showQid a} follows {showQid b}, but their `series ordinal` values do not increase"

/-- A `subclass of` chain, for humans. -/
def showChain (a : Qid) (cs : List Qid) : String :=
  String.intercalate " ⊑ " (showQid a :: cs.map showQid)

/-! ### Options -/

/-- The command line options. -/
structure Opts where
  /-- `--out FILE`: where to write the resulting knowledge base. -/
  out : Option String := none
  /-- `--cache DIR`: the directory of downloaded JSON. -/
  cache : String := ".wikidata-cache"
  /-- `--offline`: never touch the network. -/
  offline : Bool := false
  /-- `--depth N`: how far to follow `instance of` / `subclass of` links. -/
  depth : ℕ := 0
  /-- `--name NAME`: the name of the resulting knowledge base. -/
  name : Option String := none
  /-- `--quiet`: less chatter. -/
  quiet : Bool := false
  /-- `--warn` / `--no-warn`: force the (quadratic) redundancy scan on or off.  By
  default it runs on bases with at most 200 `subclass of` statements. -/
  warn : Option Bool := none
  /-- `--module NAME`: the module name of the Lean file written by `lean`. -/
  module : Option String := none
  /-- `--kernel`: have the generated module checked by the kernel (`decide`)
  rather than by compiled evaluation (`native_decide`). -/
  kernel : Bool := false
  /-- `--highlights N`: how many individually named fact theorems to generate. -/
  highlights : ℕ := 8
  /-- `--dedup`: normalise the result, dropping repeated items and statements. -/
  dedup : Bool := false
  /-- `--infer-levels`: recompute the metaclass levels from the statements. -/
  inferLevels : Bool := false
  /-- `--out-base`: also write the candidate base a patch review leads to.  The
  input file is never touched. -/
  outBase : Bool := false
  /-- `--select x,y`: which query variables to report, and in which order. -/
  select : Option String := none
  /-- `--langs en,de`: which Wikipedia languages the enrichment tool scans. -/
  langs : Option String := none
  /-- `--base FILE`: the knowledge base the enrichment commands work against. -/
  base : Option String := none
  /-- `--top N`: how many entries of a ranking to act on. -/
  top : ℕ := 20
  /-- `--max-links N`: how many links of an article to keep when scanning. -/
  maxLinks : ℕ := 150
  /-- `--max-cites N`: how many cited sources of an article to keep when scanning. -/
  maxCites : ℕ := 40
  /-- `--gaps`: have `worklist` include what is *missing* — parentless items,
  isolated items and childless classes — as well as what is wrong. -/
  gaps : Bool := false
  /-- `--assets DIR`: where `onepage` reads the stylesheet and the script it
  inlines into the single page report. -/
  assets : String := "web"
deriving Inhabited

/-- Splits the arguments into positional arguments and options. -/
def parseOpts : List String → List String × Opts
  | [] => ([], {})
  | "--out" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with out := some v })
  | "--cache" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with cache := v })
  | "--name" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with name := some v })
  | "--depth" :: v :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with depth := (parseNat? v).getD 0 })
  | "--module" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with module := some v })
  | "--highlights" :: v :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with highlights := (parseNat? v).getD 0 })
  | "--kernel" :: rest => let (ps, o) := parseOpts rest; (ps, { o with kernel := true })
  | "--dedup" :: rest => let (ps, o) := parseOpts rest; (ps, { o with dedup := true })
  | "--infer-levels" :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with inferLevels := true })
  | "--out-base" :: rest => let (ps, o) := parseOpts rest; (ps, { o with outBase := true })
  | "--select" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with select := some v })
  | "--langs" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with langs := some v })
  | "--base" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with base := some v })
  | "--top" :: v :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with top := (parseNat? v).getD 20 })
  | "--max-links" :: v :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with maxLinks := (parseNat? v).getD 150 })
  | "--max-cites" :: v :: rest =>
      let (ps, o) := parseOpts rest; (ps, { o with maxCites := (parseNat? v).getD 40 })
  | "--offline" :: rest => let (ps, o) := parseOpts rest; (ps, { o with offline := true })
  | "--quiet" :: rest => let (ps, o) := parseOpts rest; (ps, { o with quiet := true })
  | "--warn" :: rest => let (ps, o) := parseOpts rest; (ps, { o with warn := some true })
  | "--no-warn" :: rest => let (ps, o) := parseOpts rest; (ps, { o with warn := some false })
  | "--gaps" :: rest => let (ps, o) := parseOpts rest; (ps, { o with gaps := true })
  | "--assets" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with assets := v })
  | a :: rest => let (ps, o) := parseOpts rest; (a :: ps, o)

/-! ### Shared reporting -/

/-- Prints the diagnostic report; returns `true` when the base is valid. -/
def reportOn (o : Opts) (kb : KB) : IO Bool := do
  let errs := kb.errorsFast
  for i in errs do
    IO.println s!"  ✗ {showIssue kb i}"
  if o.warn.getD (kb.sub.length ≤ 200) then
    for i in kb.warnings do
      IO.println s!"  ! {showIssue kb i}"
  if errs.isEmpty then
    IO.println s!"  ✓ {kb.name}: valid ({kb.items.length} items, {kb.sub.length} P279, {kb.inst.length} P31)"
    return true
  else
    IO.println s!"  {errs.length} error(s) found"
    return false

/-- Writes the knowledge base if `--out` was given. -/
def maybeWrite (o : Opts) (kb : KB) : IO Unit := do
  match o.out with
  | none => pure ()
  | some f =>
      writeKB f kb
      IO.println s!"  wrote {kb.items.length} items and {kb.sub.length + kb.inst.length} statements to {f}"

/-- The English labels of the given items, from the label cache and, unless
`--offline` was given, from the Wikidata API.  Labels appear only in comments of
the generated module, never in what is proved. -/
def readLabels (dir : System.FilePath) (offline : Bool) (items : List Qid) :
    IO (List (Qid × String)) := do
  let ids := items.filterMap fun q => match q with | .wd id => some id | _ => none
  let rows ← fetchLabels dir offline ids
  return items.filterMap fun q =>
    match q with
    | .wd id => (rows.lookup id).map fun l => (q, l)
    | _ => none

/-- Re-runs the level inference of `Cli.inferLevels` on a knowledge base. -/
def withInferredLevels (kb : KB) : KB :=
  { kb with levels := inferLevels kb.items kb.sub kb.inst }

/-! ### The commands -/

/-- Printed when an imported base fails the validator. -/
def levelNote : String :=
"  (saved anyway: metaclass levels are inferred, and real Wikidata data does not always
   fit a strict level discipline — this is exactly the kind of thing the WikiProject
   Ontology pages discuss)"

/-- `fetch`: download entities from the Wikidata API. -/
def cmdFetch (ids : List String) (o : Opts) : IO UInt32 := do
  if ids.isEmpty then
    IO.eprintln "usage: wikidata fetch Q42 [Q5 ...] [--depth N] [--out FILE] [--cache DIR] [--offline]"
    return 1
  IO.println s!"fetching {ids.length} entity/entities (depth {o.depth}) …"
  let es ← crawl o.cache o.offline (!o.quiet) ids o.depth
  IO.println s!"  {es.length} entities"
  let kb := kbOfEntities (o.name.getD "wikidata") es
  let ok ← reportOn o kb
  if !ok then IO.println levelNote
  maybeWrite o kb
  return 0

/-- `import`: build a knowledge base from local Wikidata JSON files. -/
def cmdImport (files : List String) (o : Opts) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: wikidata import FILE.json [FILE.json ...] [--out FILE]"
    return 1
  let mut es : List Entity := []
  for f in files do
    let txt ← IO.FS.readFile f
    match Lean.Json.parse txt with
    | .ok j => es := es ++ entitiesOfJson j
    | .error e =>
        IO.eprintln s!"{f}: malformed JSON ({e})"
        return 1
  IO.println s!"read {es.length} entities from {files.length} file(s)"
  let kb := kbOfEntities (o.name.getD "wikidata") es
  let ok ← reportOn o kb
  if !ok then IO.println levelNote
  maybeWrite o kb
  return 0

/-- `check`: validate a stored knowledge base. -/
def cmdCheck (file : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  IO.println s!"checking {file} …"
  let ok ← reportOn o kb
  return (if ok then 0 else 1)

/-- `derive`: construct the facts the base implies but does not state. -/
def cmdDerive (file : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  let newSub := kb.newSubLFast
  let newInst := kb.newInstLFast
  IO.println s!"{file}: {newSub.length} new `subclass of` and {newInst.length} new `instance of` fact(s)"
  for p in newSub do
    IO.println s!"  P279  {showQid p.1} ⊑ {showQid p.2}"
  for p in newInst do
    IO.println s!"  P31   {showQid p.1} : {showQid p.2}"
  let sat := kb.saturateFast
  IO.println "  (every fact above is derivable in the input; adding them changes nothing that is derivable)"
  let _ok ← reportOn o sat
  maybeWrite o sat
  return 0

/-- `ask`: is a statement derivable? -/
def cmdAsk (file kind a b : String) : IO UInt32 := do
  let kb ← readKB file
  let qa : Qid := .wd a
  let qb : Qid := .wd b
  match kind with
  | "subclass" =>
      let yes := kb.isSubclassOf qa qb
      IO.println s!"{a} ⊑ {b} : {if yes then "yes" else "no"}"
      return (if yes then 0 else 1)
  | "instance" =>
      let yes := kb.isInstanceOf qa qb
      IO.println s!"{a} : {b} : {if yes then "yes" else "no"}"
      return (if yes then 0 else 1)
  | _ =>
      IO.eprintln "usage: wikidata ask FILE.wdkb (subclass|instance) A B"
      return 1

/-- A variable name, with the leading `?` of the surface syntax removed. -/
def stripVar (n : String) : String :=
  match n.toList with
  | '?' :: cs => String.ofList cs
  | _ => n

/-- `query`: evaluate a conjunctive query with variables.

Each positional argument after the file is one atom of the query.  The answers are
`Query.evalT`, which by `Query.evalT_eq_eval` is `Query.eval`, which by
`Query.mem_eval_iff` returns exactly the assignments of items to variables that make
every atom true in the ontology the base determines. -/
def cmdQuery (file : String) (pats : List String) (o : Opts) : IO UInt32 := do
  if pats.isEmpty then
    IO.eprintln "usage: wikidata query FILE.wdkb 'inst ?x Q5' ['sub ?x Q35120' …] [--select x,y]"
    IO.eprintln "  atoms: sub|inst|dsub|dinst|ne TERM TERM, class TERM; a term is ?name or an item id"
    return 1
  let kb ← readKB file
  match parseQuery? pats with
  | none =>
      IO.eprintln "malformed query"
      IO.eprintln "  atoms: sub|inst|dsub|dinst|ne TERM TERM, class TERM; a term is ?name or an item id"
      return 1
  | some q =>
      let outs :=
        match o.select with
        | some sel => ((splitChar ',' sel).map stripVar).filter (· ≠ "")
        | none => (Query.bgpVars q).dedup
      let rows := Query.answersT kb q outs
      IO.println s!"{file}: {rows.length} answer(s)"
      if !outs.isEmpty then
        IO.println ("  " ++ String.intercalate "\t" (outs.map fun n => "?" ++ n))
      for r in rows do
        IO.println ("  " ++ String.intercalate "\t" (r.map showQid))
      return (if rows.isEmpty then 1 else 0)

/-- `why`: print a checked explanation of a `subclass of` fact. -/
def cmdWhy (file a b : String) : IO UInt32 := do
  let kb ← readKB file
  let qa : Qid := .wd a
  let qb : Qid := .wd b
  match kb.explainSubclass qa qb with
  | some cs =>
      if cs.isEmpty then
        IO.println s!"{a} ⊑ {b} holds trivially: they are the same item"
      else
        IO.println (showChain qa cs)
      IO.println s!"  chain of {cs.length} asserted P279 statement(s)"
      IO.println s!"  re-checked: {if kb.checkSubChain qa cs qb then "valid derivation" else "INVALID"}"
      return 0
  | none =>
      IO.println s!"no chain of `subclass of` statements from {a} to {b}"
      return 1

/-- `classes` / `instances`: the derived neighbourhood of an item. -/
def cmdClasses (file q : String) : IO UInt32 := do
  let kb ← readKB file
  let qq : Qid := .wd q
  let table := kb.closureTable
  IO.println s!"{q} is an instance of:"
  for c in kb.classesOfT table qq do IO.println s!"  {showQid c}"
  IO.println s!"{q} is a subclass of:"
  for c in kb.superclassesOfLT table qq do
    if c ≠ qq then IO.println s!"  {showQid c}"
  return 0

/-! ### The glossary: what Wikidata says about an identifier -/

/-- One glossary entry, printed. -/
def showGloss (g : Gloss) : String :=
  let redirect := if g.isRedirect then s!"\n  redirects to {g.canonical}" else ""
  let article :=
    match g.articleUrl with
    | some u => s!"\n  article   {u}"
    | none => ""
  s!"{g.id}  {g.label}\n  {g.description}\n  wikidata  {g.conceptUrl}{article}{redirect}"

/-- `gloss`: what Wikidata says about the given identifiers, or about every item
of a stored knowledge base.

The answers come from `Wikidata.Generated.glossary`, the table downloaded by
`scripts/fetch_glossary.py`; `Wikidata.Grounded.lookup_unique` says each
identifier gets the one entry that carries it. -/
def cmdGloss (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: wikidata gloss (Q64 | P279 | FILE.wdkb) […]"
      return 1
  | [f] =>
      if f.endsWith ".wdkb" || f.endsWith ".skb" then
        let kb ← readKB f
        let ids := Glossary.wdIds kb.items
        let mut missing := 0
        for s in ids do
          match Generated.glossary.lookup s with
          | some g => IO.println (showGloss g)
          | none =>
              missing := missing + 1
              IO.println s!"{s}  (not in the glossary)"
        IO.println s!"{ids.length} item(s), {missing} not grounded in Wikidata"
        return (if missing == 0 then 0 else 1)
      else glossIds [f]
  | ids => glossIds ids
where
  /-- Print the entry of each identifier; exit status 1 if one is unknown. -/
  glossIds (ids : List String) : IO UInt32 := do
    let mut missing := 0
    for s in ids do
      match Generated.glossary.lookup s with
      | some g => IO.println (showGloss g)
      | none =>
          missing := missing + 1
          IO.println s!"{s}  (not in the glossary)"
    return (if missing == 0 then 0 else 1)

/-! ### The series layer -/

/-- Reads a series layer in the verified text format.  An ordinary `.wdkb` file reads as a
layer with no series statements. -/
def readSKB (path : System.FilePath) : IO SKB := do
  let raw ← IO.FS.readFile path
  -- a file written by an editor may end in a newline; the codec writes none
  let txt := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
  match parseSKB? txt with
  | some s => return s
  | none => throw (IO.userError s!"{path}: not a well-formed series file")

/-- Writes a series layer.  Fails if some identifier contains a separator, which is exactly
the condition under which reading the file back returns the same layer
(`Cli.parseSKB?_renderSKB`). -/
def writeSKB (path : System.FilePath) (s : SKB) : IO Unit := do
  if !SKB.cleanB s then
    throw (IO.userError "refusing to write: an identifier contains a tab or newline")
  IO.FS.writeFile path (renderSKB s)

/-- `series`: print the series an item belongs to, in order.

On a valid layer the printed chain is exactly the items that come after the origin
(`SKB.mem_chainFrom_iff`), each listed once (`SKB.chainFrom_nodup`), and the origin itself
is unique (`SKB.exists_unique_origin`). -/
def cmdSeries (file q : String) : IO UInt32 := do
  let s ← readSKB file
  let a : Qid := .wd q
  match s.originsOfL a with
  | [b] =>
      IO.println s!"{showQid a} belongs to the series beginning at {showQid b}:"
      for x in s.chainFrom b do
        let ordinal := match s.ordinalOf? x with | some n => s!"  ({n})" | none => ""
        let mark := if x == a then "  ←" else ""
        IO.println s!"  {showQid x}{ordinal}{mark}"
      return 0
  | [] =>
      IO.println s!"{showQid a} has no recorded origin; from it the series runs:"
      for x in s.chainFrom a do IO.println s!"  {showQid x}"
      return 0
  | bs =>
      IO.println s!"{showQid a} comes after {bs.length} distinct origins, so the series is not a chain:"
      for b in bs do IO.println s!"  {showQid b}"
      return 1

/-- `scheck`: validate the series layer of a file.

The two reports are empty exactly when the layer is valid
(`SKB.report_eq_nil_iff_sValid`); ordinal conflicts are reported as warnings, since they
do not make the ontology unsound. -/
def cmdSeriesCheck (file : String) : IO UInt32 := do
  let s ← readSKB file
  IO.println s!"checking the series layer of {file} …"
  IO.println s!"  P179 / P155 / P1545  {s.series.length} / {s.follows.length} / {s.ordinals.length}"
  let baseErrs := s.base.errors
  let errs := s.sErrors
  for e in baseErrs do IO.println s!"  error: {showIssue s.base e}"
  for e in errs do IO.println s!"  error: {showSeriesIssue e}"
  for w in s.sWarnings do IO.println s!"  warning: {showSeriesIssue w}"
  if baseErrs.isEmpty && errs.isEmpty then
    IO.println "  valid: the series layer passes every check"
    return 0
  else
    return 1

/-- Fills in the source and the labels of a row.  Labels come from the downloaded
glossary (`Wikidata.Cli.glossLabel`); they appear only in the label columns of a
report, never in what is proved. -/
def decorateRow (src : String) (r : Report.Row) : Report.Row :=
  { r with source := src, subjectLabel := glossLabel r.subject, objectLabel := glossLabel r.object }

/-- Pads a column to the given width. -/
def padTo (s : String) (n : ℕ) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- `report`: write the diagnostics as CSV, HTML and SVG files.

The rows are `Wikidata.Report.SKB.rows` (`Wikidata.Cli.reportRows_eq`): one per
witnessed issue, with its error type, severity, remediation status and the
identifiers it is about.  An empty table means every base reported on is valid
(`Wikidata.Report.errorRows_eq_nil_iff_valid`); the chart's bars add up to the
number of issues (`Wikidata.Report.bars_count_sum`); and the CSV file reads back
exactly as written (`Wikidata.Report.parseCsvText_csvText`). -/
def cmdReport (files : List String) (o : Opts) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: wikidata report FILE.wdkb [FILE.wdkb …] [--out PREFIX] [--warn|--no-warn]"
    return 1
  let mut rows : List Report.Row := []
  let mut names : List String := []
  for f in files do
    let (name, rs) ← rowsOfPath f o.warn
    let rs := rs.map (decorateRow f)
    names := names ++ [name]
    IO.println s!"{f} ({name}): {rs.length} issue(s), {countSeverity rs .error} error(s)"
    rows := rows ++ rs
  let prefixPath := o.out.getD (stripExt (files.headD "report"))
  let errs := countSeverity rows .error
  let warns := countSeverity rows .warning
  IO.println "  error type                severity  status           count"
  for fs in Report.summaryFields rows do
    match fs with
    | [code, sev, st, n] =>
        IO.println s!"  {padTo code 25} {padTo sev 9} {padTo st 16} {n}"
    | _ => IO.println ("  " ++ String.intercalate "  " fs)
  if rows.isEmpty then
    IO.println "  no issues: every base reported on is valid and carries no redundant statement"
  else
    IO.println s!"  {rows.length} issue(s): {errs} error(s), {warns} warning(s)"
  let title :=
    match names with
    | [n] => s!"Wikidata report — {n}"
    | _ => s!"Wikidata report — {files.length} bases"
  let source := String.intercalate ", " files
  writeReports prefixPath title source rows
  IO.println s!"  wrote {prefixPath}.csv, {prefixPath}.html and {prefixPath}.svg"
  return (if errs == 0 then 0 else 1)

/-- `worklist`: write the diagnostics grouped into things to work on.

The same issues as `report`, seen four ways — by error type, by file, by layer
and by kind of work — as a CSV table, an HTML page and an SVG chart each, one
CSV per task, and a markdown index.  Each grouping is a proved partition of the
report (`Wikidata.Report.tasks_flatMap_perm`), so its task sizes add up to the
number of issues (`Wikidata.Report.worklist_size_sum`) and so does its chart
(`Wikidata.Report.taskBars_count_sum`); the tasks come biggest first
(`Wikidata.Report.worklist_sorted`). -/
def cmdWorklist (files : List String) (o : Opts) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: wikidata worklist FILE.wdkb [FILE.wdkb …] [--out DIR] [--warn|--no-warn]"
    return 1
  let mut rows : List Report.Row := []
  for f in files do
    let (_, rs) ← rowsOfPath f o.warn
    rows := rows ++ rs.map (decorateRow f)
    if o.gaps then
      let kb ← baseOfPath f
      rows := rows ++ (Report.KB.gapRows kb).map (decorateRow f)
  let dir := o.out.getD "worklist"
  let source := String.intercalate ", " files
  let tasks := Report.worklist Report.byCode rows
  IO.println s!"{rows.length} item(s) of work in {files.length} file(s): {tasks.length} task(s) by type"
  IO.println "  task                      items   errors  what it takes"
  for t in tasks do
    IO.println s!"  {padTo t.key 25} {padTo (Report.num t.size) 7} {padTo (Report.num t.errors) 7} {t.advice}"
  if rows.isEmpty then
    IO.println "  nothing to work on: every base reported on is valid and carries no redundant statement"
  writeWorklist dir source rows
  IO.println s!"  wrote {dir}/by-code.*, by-source.*, by-layer.*, by-status.*, tasks/*.csv and README.md"
  return (if countSeverity rows .error == 0 then 0 else 1)

/-- `repairs`: write the patch review — a candidate repair for every flagged
issue, with its rationale and the verdict of the check — and change nothing.

Both layers are reviewed.  The ontology candidates are `Wikidata.KB.plan`, which
has one for every issue the base flags (`Wikidata.KB.plan_covers`), with the
verdicts of `Wikidata.KB.verdictOf`; the series candidates are
`Wikidata.SKB.sPlan` (`Wikidata.SKB.sPlan_covers`, `SKB.sVerdictOf`).  A line
marked `proven` is one whose change removes the issue it was raised for and
introduces no error and no warning the base did not carry
(`Wikidata.KB.proven_no_regression`, `Wikidata.SKB.sProven_no_regression`), while
lowering the repair debt (`Wikidata.KB.proven_scoreAfter_lt`,
`Wikidata.SKB.sProven_scoreAfter_lt`).  With `--out-base` the candidate base
`Wikidata.SKB.repairedCandidate` is written out as well; it carries no ontology
error the base did not already carry
(`Wikidata.SKB.repairedCandidate_base_errors_subset`). -/
def cmdRepairs (files : List String) (o : Opts) : IO UInt32 := do
  if files.isEmpty then
    IO.eprintln "usage: wikidata repairs FILE.wdkb [FILE.wdkb …] [--out DIR] [--out-base]"
    return 1
  let dir := o.out.getD "repairs"
  IO.FS.createDirAll dir
  let mut worst : UInt32 := 0
  for f in files do
    -- `.tkb` files carry no series layer; everything else reads as one (a `.wdkb`
    -- file reads as a layer with no series statements)
    let s ← if f.endsWith ".tkb" then (do let kb ← baseOfPath f; pure ({ base := kb } : SKB))
             else readSKB f
    let kb := s.base
    let debtNow := s.totalScoreFast
    let cand := s.repairedCandidateFast
    let debtAfter := cand.totalScoreFast
    let errsNow := kb.errorsFast.length + s.sErrors.length
    let errsAfter := cand.base.errorsFast.length + cand.sErrors.length
    let stem := (stripExt f).splitOn "/" |>.getLast!
    let prefixPath := dir ++ "/" ++ stem
    IO.println s!"{f} ({kb.name}): {kb.flaggedFast.length + s.sFlagged.length} flagged issue(s), {kb.flaggedFast.length} in the ontology and {s.sFlagged.length} in the series layer"
    IO.println s!"  {s.reviewCount} candidate repair(s): {s.reviewVerdictCount .proven} recommended, {s.reviewVerdictCount .rejected} for review"
    IO.println s!"  repair debt {debtNow} → {debtAfter} if the recommended changes are made"
    IO.println s!"  errors      {errsNow} → {errsAfter}"
    IO.println "  nothing applied: read the review and decide"
    writeRepairReviewSKB prefixPath s!"Proposed repairs — {kb.name}" f s debtNow debtAfter
    IO.println s!"  wrote {prefixPath}.csv, {prefixPath}.html and {prefixPath}.txt"
    if o.outBase then
      if f.endsWith ".skb" then
        writeSKB (prefixPath ++ "-repaired.skb") cand
        IO.println s!"  wrote the candidate base to {prefixPath}-repaired.skb (not applied to {f})"
      else
        writeKB (prefixPath ++ "-repaired.wdkb") cand.base
        IO.println s!"  wrote the candidate base to {prefixPath}-repaired.wdkb (not applied to {f})"
    if errsAfter != 0 then worst := 1
  return worst

/-- `fix`: suggest a repair for every issue, apply the ones that are checked to be
safe, and offer the candidate base.

The actions come from `Wikidata.KB.suggestedFixes` and are applied by
`Wikidata.KB.applyFixSafe`, which accepts one only if the result answers every
question about the declared items exactly as the base did
(`Wikidata.KB.applyFixes_isSubclassOf`, `applyFixes_isInstanceOf`), carries no
new error (`Wikidata.KB.applyFixes_errors_le`) and is strictly smaller or has
strictly fewer errors.  The base written out is `Wikidata.KB.repair`
(`Wikidata.Cli.fixTrace_snd`). -/
def cmdFix (file : String) (o : Opts) : IO UInt32 := do
  let kb ← baseOfPath file
  -- the scan for redundant statements is quadratic, so on a large base it is left
  -- out unless `--warn` asks for it
  let warn := o.warn.getD (kb.sub.length ≤ 200)
  let fixes := kb.suggestedFixesFast warn
  let (trace, cand) := fixTrace kb fixes
  let errs := kb.errorsFast.length
  IO.println s!"{file}: {kb.name}"
  IO.println s!"  {errs} error(s), {fixes.length} suggested action(s)"
  if !warn then
    IO.println "  (redundant statements not scanned for; --warn asks for them)"
  for (f, applied) in trace do
    IO.println s!"  {if applied then "applied " else "declined"}  {f.text}"
  let applied := (trace.filter (fun p => p.2)).length
  IO.println s!"  applied {applied} of {fixes.length} action(s)"
  IO.println s!"  errors     {errs} → {cand.errorsFast.length}"
  IO.println s!"  statements {kb.statementCount} → {cand.statementCount}"
  IO.println "  every applied action is checked: no new error, and no derived fact changed"
  maybeWrite o cand
  return (if cand.errorsFast.isEmpty then 0 else 1)

/-- `instances`: the derived instances of a class. -/
def cmdInstances (file q : String) : IO UInt32 := do
  let kb ← readKB file
  IO.println s!"instances of {q}:"
  for a in kb.instancesOfT kb.closureTable (.wd q) do IO.println s!"  {showQid a}"
  return 0

/-- `stats`: a summary of a stored knowledge base. -/
def cmdStats (file : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  let maxLevel := kb.items.foldl (fun m q => max m (kb.levelOf q)) 0
  let roots := kb.items.filter fun q => (kb.supersL q).isEmpty && !(kb.sub.filter (·.2 == q)).isEmpty
  let table := kb.closureTable
  let metaclasses := kb.items.filter fun q => kb.isMetaclassBT table q
  IO.println s!"{file}: {kb.name}"
  IO.println s!"  items                {kb.items.length}"
  IO.println s!"  P279 statements      {kb.sub.length}"
  IO.println s!"  P31 statements       {kb.inst.length}"
  IO.println s!"  disjointness         {kb.disj.length}"
  IO.println s!"  maximal level        {maxLevel}"
  IO.println s!"  top classes          {roots.length}"
  IO.println s!"  metaclasses          {metaclasses.length}"
  IO.println s!"  derivable new facts  {kb.newSubLFast.length + kb.newInstLFast.length}"
  let _ok ← reportOn o kb
  return 0

/-- `add`: assert a new statement and see whether the ontology still holds up. -/
def cmdAdd (file kind a b : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  let qa : Qid := .wd a
  let qb : Qid := .wd b
  let items := (kb.items ++ [qa, qb]).dedup
  let kb' : Option KB :=
    match kind with
    | "sub" => some { kb with items := items, sub := kb.sub ++ [(qa, qb)] }
    | "inst" => some { kb with items := items, inst := kb.inst ++ [(qa, qb)] }
    | "disj" => some { kb with items := items, disj := kb.disj ++ [(qa, qb)] }
    | _ => none
  match kb' with
  | none =>
      IO.eprintln "usage: wikidata add FILE.wdkb (sub|inst|disj) A B [--out FILE]"
      return 1
  | some kb' =>
      IO.println s!"adding {kind} {a} {b} to {file}"
      IO.println s!"  keeps everything the base knew: {kb'.EntailsT kb}"
      let ok ← reportOn o kb'
      if ok then maybeWrite o kb'
      else IO.println "  the new statement breaks the ontology; nothing written"
      return (if ok then 0 else 1)

/-- `lean`: compile a knowledge base into a Lean module.

The module states the downloaded facts as a `KB`, lists everything they entail
about the declared items, and proves — citing `Cli.subFacts_sound`,
`Cli.subFacts_complete`, `Cli.instFacts_sound`, `Cli.instFacts_complete` — that
the list is exactly the set of consequences.  Nothing here is trusted: Lean
re-checks the generated file. -/
def cmdLean (file : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  let some mod := o.module
    | IO.eprintln "usage: wikidata lean FILE.wdkb --module Some.Module.Name [--out F.lean] [--kernel] [--highlights N]"
      return 1
  let tac := if o.kernel then "decide" else "native_decide"
  let labels ← readLabels o.cache o.offline kb.items
  let src := leanModule mod kb tac o.highlights ("`" ++ file ++ "`") labels
  let target := o.out.getD (mod.replace "." "/" ++ ".lean")
  if let some dir := (System.FilePath.mk target).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile target src
  IO.println s!"compiled {file} to {target}"
  IO.println s!"  module               {mod}"
  IO.println s!"  items                {kb.items.length}"
  IO.println s!"  P279 / P31           {kb.sub.length} / {kb.inst.length}"
  IO.println s!"  derived subclass     {(subFacts kb).length}"
  IO.println s!"  derived instance     {(instFacts kb).length}"
  IO.println s!"  checked by           {tac}"
  IO.println s!"  named fact theorems  {2 * min o.highlights (min (subFacts kb).length (instFacts kb).length)}"
  return 0

/-- `normalize`: drop repeated items and repeated statements.

Every query is answered exactly as before (`KB.normalize_isSubclassOf`,
`KB.normalize_isInstanceOf`), the validator gives the same verdict
(`KB.normalize_valid`), and no knowledge is gained or lost
(`KB.normalize_entails`, `KB.entails_normalize`). -/
def cmdNormalize (file : String) (o : Opts) : IO UInt32 := do
  let kb ← readKB file
  let n := kb.normalize
  IO.println s!"normalising {file}"
  IO.println s!"  items  {kb.items.length} → {n.items.length}"
  IO.println s!"  P279   {kb.sub.length} → {n.sub.length}"
  IO.println s!"  P31    {kb.inst.length} → {n.inst.length}"
  IO.println s!"  disj   {kb.disj.length} → {n.disj.length}"
  IO.println s!"  the two bases entail each other: {n.EntailsT kb && kb.EntailsT n}"
  let n := if o.inferLevels then withInferredLevels n else n
  let n := match o.name with | some nm => { n with name := nm } | none => n
  let _ok ← reportOn o n
  maybeWrite o n
  return 0

/-- `merge`: import knowledge bases into one another. -/
def cmdMerge (files : List String) (o : Opts) : IO UInt32 := do
  match files with
  | [] | [_] =>
      IO.eprintln "usage: wikidata merge A.wdkb B.wdkb [C.wdkb …] [--dedup] [--out F]"
      return 1
  | f :: rest =>
      let mut m ← readKB f
      IO.println s!"merging {m.name}"
      for g in rest do
        let kb' ← readKB g
        m := m.merge kb'
        IO.println s!"  + {kb'.name}: everything it knew is kept: {m.EntailsT kb'}"
      if o.dedup then
        let n := m.normalize
        IO.println s!"  deduplicated: {m.items.length} → {n.items.length} items, {m.sub.length + m.inst.length} → {n.sub.length + n.inst.length} statements"
        IO.println s!"  which changes nothing: {n.EntailsT m && m.EntailsT n}"
        m := n
      if o.inferLevels then
        m := withInferredLevels m
        IO.println "  metaclass levels re-inferred from the merged statements"
      if let some nm := o.name then
        m := { m with name := nm }
      let _ok ← reportOn o m
      maybeWrite o m
      return 0

/-- `module`: extract the sub-ontology about the given items.

The items reachable from the seeds along `subclass of` and `instance of` statements,
with every statement issuing from them.  The extraction is proved sound
(`KB.moduleOf_isSubclassOf_le`, `KB.moduleOf_isInstanceOf_le`), conservative about the
items it keeps (`KB.moduleOf_isSubclassOf`, `KB.moduleOf_isInstanceOf`) and validity
preserving (`KB.moduleOf_valid`). -/
def cmdModule (file : String) (ids : List String) (o : Opts) : IO UInt32 := do
  match ids with
  | [] =>
      IO.eprintln "usage: wikidata module FILE.wdkb Q395 [Q5 …] [--out F]"
      return 1
  | _ =>
      let kb ← readKB file
      let seeds : List Qid := ids.map (fun id => .wd id)
      let m := kb.moduleOf seeds
      let m := match o.name with | some nm => { m with name := nm } | none => m
      IO.println s!"module of {kb.name} about {String.intercalate ", " ids}"
      IO.println s!"  items  {kb.items.length} → {m.items.length}"
      IO.println s!"  P279   {kb.sub.length} → {m.sub.length}"
      IO.println s!"  P31    {kb.inst.length} → {m.inst.length}"
      IO.println s!"  disj   {kb.disj.length} → {m.disj.length}"
      let missing := seeds.filter (fun q => !(q ∈ kb.items))
      if !missing.isEmpty then
        IO.println s!"  {missing.length} seed(s) are not items of the base"
      IO.println "  every `subclass of` and `instance of` answer about the kept items is unchanged"
      let _ok ← reportOn o m
      maybeWrite o m
      return 0

/-- The usage message. -/
def usage : String :=
"wikidata — a verified command line tool for the Wikidata ontology

  wikidata fetch Q42 [Q5 …] [--depth N] [--out F] [--cache DIR] [--offline]
      download entities (and, with --depth, what they are instances/subclasses of)
      from the Wikidata API, build a knowledge base and check it

  wikidata import FILE.json […] [--out F] [--name N]
      the same, from local copies of Special:EntityData JSON

  wikidata check FILE.wdkb
      validate a stored knowledge base; exit status 1 if anything is wrong

  wikidata derive FILE.wdkb [--out F]
      list the facts the base implies but does not state, and (with --out) save
      the saturated base

  wikidata ask FILE.wdkb (subclass|instance) A B
      is the statement derivable?  exit status 0 for yes, 1 for no

  wikidata query FILE.wdkb 'inst ?x Q5' ['sub ?x Q35120' …] [--select x,y]
      evaluate a conjunctive query: each argument is one atom, written
      (sub|inst|dsub|dinst|ne) TERM TERM or `class TERM`, with ?name for a variable
      and an item id for a constant; sub/inst use the derived relations, dsub/dinst
      only the asserted statements.  Exit status 1 if there are no answers

  wikidata why FILE.wdkb A B
      print, and re-check, a chain of asserted P279 statements from A to B

  wikidata add FILE.wdkb (sub|inst|disj) A B [--out F]
      assert a new statement, check that the ontology still holds up, and save it

  wikidata lean FILE.wdkb --module M [--out F.lean] [--kernel] [--highlights N]
      compile the base, and everything it entails, into a Lean module that Lean
      re-checks: the facts come with proofs from the downloaded statements

  wikidata series FILE.wdkb Q
      print the series (P155 / P179) that Q belongs to, in order, with its `series
      ordinal` values; exit status 1 if the series does not have a unique beginning

  wikidata scheck FILE.wdkb
      validate the series layer of a file: dangling statements, self-following items,
      cycles, forks, mismatched series and taxonomic confusion are errors; ordinals
      that disagree with the `follows` statements are warnings

  wikidata report FILE.wdkb [FILE.wdkb …] [--out PREFIX] [--warn|--no-warn]
      write the diagnostics as three files — PREFIX.csv (one line per issue, with
      the identifiers, their labels, the suggested fix and its status), PREFIX.html
      (a page with a summary by error type and status) and PREFIX.svg (a bar chart
      of the counts); exit status 1 if anything reported on has errors

  wikidata worklist FILE [FILE …] [--out DIR] [--gaps] [--warn|--no-warn]
      write the same issues grouped into things to work on: DIR/by-code.*,
      by-source.*, by-layer.* and by-status.* (a CSV table, an HTML page and an
      SVG chart each, biggest task first), one CSV per task under DIR/tasks/, and
      DIR/README.md indexing them; with --gaps the tables also carry what is
      missing rather than wrong — items with no `subclass of`/`instance of`
      statement, items no statement mentions, classes with nothing under them;
      exit status 1 if anything reported on has errors

  wikidata repairs FILE [FILE …] [--out DIR] [--out-base]
      the patch review: a candidate repair for every flagged issue — including the
      cycles, level mismatches and disjointness clashes `fix` refuses to touch —
      each with the change it makes, the reason for it, the verdict of the check
      and what it does to the repair debt.  Written as DIR/NAME.{csv,html,txt};
      nothing is applied, and with --out-base the candidate base is saved beside
      the review for comparison

  wikidata fix FILE [--out F]
      suggest a repair for every issue and apply the ones that are checked safe:
      an action is performed only if the candidate answers every question about the
      declared items as before and carries no new error; destructive decisions —
      which half of a cycle to cut, which item to re-level — are left to a human

  wikidata gloss (Q64 | P279 | FILE.wdkb) […]
      what Wikidata says about an identifier — label, description, Wikidata page and
      English Wikipedia article — or about every item of a stored base; exit status 1
      if an identifier is not in the glossary

  wikidata sitelinks Q42989 [Q…] [--out F.tsv] [--module M]
      the Wikimedia pages about the items, in every language Wikidata records;
      with --module, compile the table into a Lean module and check that it is a
      partial bijection between items and pages

  wikidata scan Q42989 [Q…] --langs en,de,fr [--max-links N] [--max-cites N] [--out F.scan]
      download those Wikipedia articles and reduce each to a scanned source: the
      items its links point at, the properties of the item it is about, and the
      external sources it cites

  wikidata frontier F.scan [--base B.wdkb] [--top N]
      what the scan points at and the library does not have: the most referenced
      missing terms, the most used properties with no Lean predicate, and the most
      cited sources not yet downloaded

  wikidata sources F.scan [--top N] [--out F2.scan]
      download the most cited sources, scan them for glossary terms and for the
      further sources they cite, and add them to the scan

  wikidata enrich F.scan --base B.wdkb [--top N] [--out F.wdkb] [--name N]
      autoformalise: download the most referenced missing terms, turn their P279
      and P31 statements into candidate statements tagged with their source, and
      add them to the base (conservatively: KB.enrich_entails)

  wikidata authority Q42989 [Q…] [--module M] [--name N]
      collect the external identifiers of the items — the string-valued statements
      whose property has a formatter URL — and check that each property identifies
      the item it belongs to

  wikidata scanlean F.scan --module M [--out F.lean]
      compile a scan into a Lean module

  wikidata classes FILE.wdkb Q      the classes and superclasses of Q
  wikidata instances FILE.wdkb Q    the instances of Q
  wikidata stats FILE.wdkb          a summary of the base
  wikidata merge A.wdkb B.wdkb [C.wdkb …] [--dedup] [--out F]
      import bases into one another; --dedup drops the repetitions
  wikidata normalize FILE.wdkb [--out F]
      drop repeated items and statements, changing no answer
  wikidata module FILE.wdkb Q395 [Q5 …] [--out F] [--name N]
      extract the sub-ontology about the given items: everything reachable from
      them along `subclass of` and `instance of`, with the statements out of it.
      The module answers every question about those items exactly as the whole
      base does, and a module of a valid base is valid
  wikidata publish FILE.wdkb [FILE.wdkb …] [--out DIR]
      generate the static site the project deploys to GitHub Pages, Vercel,
      Cloudflare Pages, a Hugging Face Space and Wikimedia Toolforge: a page per
      ontology, the data as JSON Lines and as .wdkb, a small JSON API, and
      manifest.json listing every file with its length, digest and content address

  wikidata onepage FILE.wdkb [FILE.wdkb …] [--out F.html] [--assets DIR] [--name TITLE]
      write the whole report as ONE self-contained HTML file — the ontologies, the
      diagnostics, a query engine, SVG charts and PNG export, with no network and no
      other file — ready to drop on any static host

  wikidata archive FILE.wdkb [--out DIR]
      build the archive.org deposit for a base: the two copies of the ontology,
      the manifest and the item metadata, checked to re-import to the same base

  wikidata unarchive DIR [--out F.wdkb]
      read a deposit back and report whether its two copies agree

  wikidata sync A.wdkb B.wdkb [C.wdkb …] [--out F.wdkb]
      one round of gossip between replicas: pool what they know, check that every
      replica is kept and that after the round they all agree

  wikidata wiki templates           the documented wiki templates, as a table
  wikidata wiki pages [--out DIR]   write the imported and generated wiki pages
  wikidata wiki import FILE.wiki    read a page of wikitext and report on it
  wikidata wiki expand NAME ARG…    expand a call to a documented template

Options: --out FILE, --cache DIR, --offline, --depth N, --name NAME, --quiet, --select V,
         --langs L, --base FILE, --top N, --max-links N, --max-cites N (enrichment),
         --warn / --no-warn (the redundancy scan; on by default for small bases),
         --module NAME, --kernel, --highlights N (for `lean`), --dedup, --infer-levels"

/-- The entry point. -/
def run (args : List String) : IO UInt32 := do
  let (pos, o) := parseOpts args
  match pos with
  | [] => IO.println usage; return 0
  | "help" :: _ => IO.println usage; return 0
  | "--help" :: _ => IO.println usage; return 0
  | "fetch" :: ids => cmdFetch ids o
  | "import" :: files => cmdImport files o
  | ["check", f] => cmdCheck f o
  | ["derive", f] => cmdDerive f o
  | ["ask", f, kind, a, b] => cmdAsk f kind a b
  | "query" :: f :: pats => cmdQuery f pats o
  | ["why", f, a, b] => cmdWhy f a b
  | ["series", f, q] => cmdSeries f q
  | ["scheck", f] => cmdSeriesCheck f
  | "report" :: files => cmdReport files o
  | "worklist" :: files => cmdWorklist files o
  | "repairs" :: files => cmdRepairs files o
  | ["fix", f] => cmdFix f o
  | "gloss" :: rest => cmdGloss rest
  | "wiki" :: rest => cmdWiki rest o.out
  | ["classes", f, q] => cmdClasses f q
  | ["instances", f, q] => cmdInstances f q
  | ["stats", f] => cmdStats f o
  | ["lean", f] => cmdLean f o
  | "merge" :: files => cmdMerge files o
  | "module" :: f :: ids => cmdModule f ids o
  | ["normalize", f] => cmdNormalize f o
  | "publish" :: files => cmdPublish files o.out
  | "onepage" :: files => cmdOnePage files o.out o.assets o.name o.warn
  | ["archive", f] => cmdArchive f o.out
  | ["unarchive", d] => cmdUnarchive d o.out
  | "sync" :: files => cmdSync files o.out
  | "sitelinks" :: ids => cmdSitelinks o.cache o.offline ids o.out o.module
  | "scan" :: ids =>
      cmdScan o.cache o.offline ids
        (((splitChar ',' (o.langs.getD "en")).filter (· ≠ ""))) o.maxLinks o.maxCites o.out
  | ["frontier", f] => cmdFrontier f o.base o.top
  | "authority" :: ids => cmdAuthority o.cache o.offline ids o.name o.module
  | ["sources", f] => cmdSources o.cache f o.offline o.top o.out
  | ["enrich", f] =>
      match o.base with
      | some b => cmdEnrich o.cache f o.offline b o.top o.name o.out
      | none =>
          IO.eprintln "usage: wikidata enrich F.scan --base B.wdkb [--top N] [--out F.wdkb]"
          return 1
  | ["scanlean", f] =>
      match o.module with
      | some m => cmdScanLean f m o.out
      | none =>
          IO.eprintln "usage: wikidata scanlean F.scan --module M [--out F.lean]"
          return 1
  | ["add", f, kind, a, b] => cmdAdd f kind a b o
  | cmd :: _ =>
      IO.eprintln s!"unknown command `{cmd}`"
      IO.eprintln usage
      return 1

end Cli
end Wikidata

/-- The `wikidata` executable. -/
def main (args : List String) : IO UInt32 := Wikidata.Cli.run args
