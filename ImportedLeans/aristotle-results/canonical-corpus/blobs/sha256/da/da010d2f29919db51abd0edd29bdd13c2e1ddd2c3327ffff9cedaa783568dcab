import RequestProject.Cli.Fetch
import RequestProject.Cli.Derive
import RequestProject.Cli.Codegen
import RequestProject.Cli.Query
import RequestProject.Cli.SeriesFormat
import RequestProject.Generated.Glossary
import RequestProject.Normalize
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
| `series`  | `SKB.mem_chainFrom_iff` (the chain printed is exactly the items that come after), `SKB.exists_unique_origin` |
| `gloss`   | `Grounded.lookup_unique` (each identifier gets the one entry that carries it), `Grounded.corpus_covered` |
| `scheck`  | `SKB.report_eq_nil_iff_sValid` (empty report ⟺ the series layer is valid) |
| load/save | `Cli.parseKB?_renderKB`, `Cli.parseSKB?_renderSKB` (a round trip through disk changes nothing) |
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
  /-- `--select x,y`: which query variables to report, and in which order. -/
  select : Option String := none
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
  | "--select" :: v :: rest => let (ps, o) := parseOpts rest; (ps, { o with select := some v })
  | "--offline" :: rest => let (ps, o) := parseOpts rest; (ps, { o with offline := true })
  | "--quiet" :: rest => let (ps, o) := parseOpts rest; (ps, { o with quiet := true })
  | "--warn" :: rest => let (ps, o) := parseOpts rest; (ps, { o with warn := some true })
  | "--no-warn" :: rest => let (ps, o) := parseOpts rest; (ps, { o with warn := some false })
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

  wikidata gloss (Q64 | P279 | FILE.wdkb) […]
      what Wikidata says about an identifier — label, description, Wikidata page and
      English Wikipedia article — or about every item of a stored base; exit status 1
      if an identifier is not in the glossary

  wikidata classes FILE.wdkb Q      the classes and superclasses of Q
  wikidata instances FILE.wdkb Q    the instances of Q
  wikidata stats FILE.wdkb          a summary of the base
  wikidata merge A.wdkb B.wdkb [C.wdkb …] [--dedup] [--out F]
      import bases into one another; --dedup drops the repetitions
  wikidata normalize FILE.wdkb [--out F]
      drop repeated items and statements, changing no answer

Options: --out FILE, --cache DIR, --offline, --depth N, --name NAME, --quiet, --select V,
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
  | "gloss" :: rest => cmdGloss rest
  | ["classes", f, q] => cmdClasses f q
  | ["instances", f, q] => cmdInstances f q
  | ["stats", f] => cmdStats f o
  | ["lean", f] => cmdLean f o
  | "merge" :: files => cmdMerge files o
  | ["normalize", f] => cmdNormalize f o
  | ["add", f, kind, a, b] => cmdAdd f kind a b o
  | cmd :: _ =>
      IO.eprintln s!"unknown command `{cmd}`"
      IO.eprintln usage
      return 1

end Cli
end Wikidata

/-- The `wikidata` executable. -/
def main (args : List String) : IO UInt32 := Wikidata.Cli.run args
