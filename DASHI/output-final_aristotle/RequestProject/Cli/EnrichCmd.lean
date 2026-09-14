import RequestProject.Cli.Enrich
import RequestProject.Cli.Derive
import RequestProject.FastEval

/-!
# The enrichment commands of the `wikidata` tool

Six commands, one per stage of the loop described in
`RequestProject.Enrichment`:

```
wikidata sitelinks Q42989 …                     # the articles about an item, in every language
wikidata scan Q42989 … --langs en,de,fr         # download those articles and scan them
wikidata frontier F.scan --base B.wdkb          # what is missing, most referenced first
wikidata sources F.scan --top 5                 # download the most cited sources and scan them
wikidata enrich F.scan --base B.wdkb --top 40   # autoformalise: add the missing terms
wikidata scanlean F.scan --module M             # compile the scan into a Lean module
```

Everything the commands print about what is missing, and everything `enrich`
adds, is computed by the verified core: `Enrichment.termDemand`,
`Enrichment.predicateDemand`, `Enrichment.sourceDemand` and `KB.enrich`.
-/

namespace Wikidata
namespace Cli

/-- The label of an identifier, from the project glossary, for printing. -/
def glossLabel (id : String) : String :=
  match Generated.glossary.lookup id with
  | some g => g.label
  | none => ""

/-- An item with its label, for printing. -/
def showItem (q : Qid) : String :=
  match q with
  | .wd id =>
      let l := glossLabel id
      if l.isEmpty then id else s!"{id} ({l})"
  | _ => qidTok q

/-- `sitelinks`: the Wikimedia pages about the given items, in every language. -/
def cmdSitelinks (cache : String) (offline : Bool) (ids : List String)
    (out : Option String) (mod : Option String) : IO UInt32 := do
  if ids.isEmpty then
    IO.eprintln "usage: wikidata sitelinks Q42989 [Q…] [--out F.tsv] [--module M]"
    return 1
  let mut links : List (Qid × Sitelink) := []
  let mut items : List Qid := []
  for id in ids do
    let body ← fetchEntityJson cache offline id
    match entityJson? body id with
    | none =>
        IO.eprintln s!"{id}: malformed entity JSON"
        return 1
    | some j =>
        let sl := sitelinksOfJson j
        items := items ++ [.wd id]
        links := links ++ sl.map fun (site, title) => (Qid.wd id, ⟨site, title⟩)
        let wikis := sl.filter fun p => p.1.endsWith "wiki"
        IO.println s!"{showItem (.wd id)}: {sl.length} sitelink(s), {wikis.length} Wikipedia article(s)"
  let S : SiteKB := ⟨items, links⟩
  IO.println s!"total: {links.length} sitelink(s) over {(links.map fun l => l.2.site).dedup.length} sites"
  IO.println s!"  one page per item and site: {S.functionalB}"
  IO.println s!"  one item per page:          {S.pageInjectiveB}"
  match out with
  | some f =>
      IO.FS.writeFile f (String.join (links.map fun l =>
        s!"{qidTok l.1}\t{l.2.site}\t{l.2.page}\n"))
      IO.println s!"  wrote {links.length} rows to {f}"
  | none => pure ()
  match mod with
  | some m =>
      let target := m.replace "." "/" ++ ".lean"
      if let some dir := (System.FilePath.mk target).parent then IO.FS.createDirAll dir
      IO.FS.writeFile target (sitelinksModule m "the Wikidata API" S)
      IO.println s!"  compiled the table to {target}"
  | none => pure ()
  return 0

/-- `scan`: download the Wikipedia articles about the given items in the given
languages and reduce each of them to a `ScannedSource`. -/
def cmdScan (cache : String) (offline : Bool) (ids : List String) (langs : List String)
    (maxLinks maxCites : ℕ) (out : Option String) : IO UInt32 := do
  if ids.isEmpty then
    IO.eprintln "usage: wikidata scan Q42989 [Q…] --langs en,de,fr [--max-links N] [--out F.scan]"
    return 1
  let langs := if langs.isEmpty then ["en"] else langs
  let mut ss : List ScannedSource := []
  for id in ids do
    let body ← fetchEntityJson cache offline id
    match entityJson? body id with
    | none =>
        IO.eprintln s!"{id}: malformed entity JSON"
        return 1
    | some j =>
        let sl := sitelinksOfJson j
        let preds := predicatesOfJson j
        for lang in langs do
          match sl.lookup (lang ++ "wiki") with
          | none => IO.println s!"  {id}: no {lang} article"
          | some title => do
              let s ← scanArticle cache offline lang title preds
              let s := { s with mentions := s.mentions.take maxLinks, cites := s.cites.take maxCites }
              IO.println s!"  {id} [{lang}] {title}: {s.mentions.length} link(s), {s.predicates.length} propert(y/ies), {s.cites.length} cited source(s)"
              ss := ss ++ [s]
  IO.println s!"scanned {ss.length} document(s)"
  match out with
  | some f =>
      writeScan f ss
      IO.println s!"  wrote {f}"
  | none => pure ()
  return 0

/-- The knowledge base a command works against. -/
def readBase (file : Option String) : IO KB :=
  match file with
  | some f => readKB f
  | none => return { name := "empty", items := [] }

/-- `frontier`: what the scanned documents point at and the library does not
have — the most referenced missing terms, the most used unmodelled properties
and the most cited sources still to download. -/
def cmdFrontier (scanFile : String) (baseFile : Option String) (top : ℕ) : IO UInt32 := do
  let ss ← readScan scanFile
  let base ← readBase baseFile
  let terms := Enrichment.termDemand base ss
  let preds := Enrichment.predicateDemand modelledPredicates ss
  let srcs := Enrichment.sourceDemand ss
  IO.println s!"{scanFile}: {ss.length} scanned document(s), base {base.name} ({base.items.length} items)"
  IO.println s!"missing terms ({terms.length}), most referenced first:"
  for (q, n) in terms.take top do
    IO.println s!"  {n}×  {showItem q}"
  IO.println s!"unmodelled properties ({preds.length}), most used first:"
  for (p, n) in preds.take top do
    IO.println s!"  {n}×  {p} {glossLabel p}"
  IO.println s!"uncollected sources ({srcs.length}), most cited first:"
  for (u, n) in srcs.take top do
    IO.println s!"  {n}×  {u}"
  let closed := (Enrichment.State.mk base ss modelledPredicates).frontier.isEmpty
  IO.println s!"frontier empty (nothing left to pull in): {closed}"
  return 0

/-- `sources`: download the most cited sources and scan them for further terms
and further sources. -/
def cmdSources (cache scanFile : String) (offline : Bool) (top : ℕ)
    (out : Option String) : IO UInt32 := do
  let ss ← readScan scanFile
  let demand := Enrichment.sourceDemand ss
  let picked := (demand.take top).map Prod.fst
  IO.println s!"{scanFile}: downloading {picked.length} of {demand.length} cited source(s)"
  let labels := glossaryLabels
  let mut fresh : List ScannedSource := []
  for u in picked do
    try
      let s ← scanWebSource (cache ++ "/sources") offline labels u
      IO.println s!"  {u}: {s.mentions.length} term(s), {s.cites.length} further source(s)"
      fresh := fresh ++ [s]
    catch e =>
      IO.println s!"  {u}: skipped ({e})"
  let all := ss ++ fresh
  IO.println s!"scan now holds {all.length} document(s)"
  writeScan (out.getD scanFile) all
  IO.println s!"  wrote {out.getD scanFile}"
  return 0

/-- `enrich`: the autoformalisation step.  Download the most referenced missing
items, read their `subclass of` and `instance of` statements, and add them to the
base as candidate statements tagged with the source they came from. -/
def cmdEnrich (cache scanFile : String) (offline : Bool) (baseFile : String) (top : ℕ)
    (name : Option String) (out : Option String) : IO UInt32 := do
  let ss ← readScan scanFile
  let base ← readKB baseFile
  let demand := Enrichment.termDemand base ss
  let picked := (demand.take top).filterMap fun p =>
    match p.1 with | .wd id => some id | _ => none
  IO.println s!"enriching {base.name} with the {picked.length} most referenced of {demand.length} missing term(s)"
  let mut cands : List Candidate := []
  let mut fetched := 0
  for id in picked do
    try
      let es ← fetchEntity cache offline id
      fetched := fetched + 1
      for e in es do
        for (prop, val) in e.claims do
          if prop == "P279" then
            cands := cands ++ [⟨.sub (.wd e.id) (.wd val), entityDataUrl id⟩]
          else if prop == "P31" then
            cands := cands ++ [⟨.inst (.wd e.id) (.wd val), entityDataUrl id⟩]
    catch e =>
      IO.println s!"  {id}: skipped ({e})"
  let grown := base.enrich cands
  let grown := { grown with
    name := name.getD base.name
    levels := inferLevels grown.items grown.sub grown.inst }
  IO.println s!"  downloaded {fetched} entity/entities, extracted {cands.length} candidate statement(s)"
  IO.println s!"  items       {base.items.length} → {grown.items.length}"
  IO.println s!"  P279 / P31  {base.sub.length} / {base.inst.length} → {grown.sub.length} / {grown.inst.length}"
  IO.println s!"  well formed (every mentioned item declared): {grown.wellFormed}"
  IO.println s!"  keeps everything the base knew: {grown.EntailsT base}"
  let stillMissing := Enrichment.missingTerms grown ss
  IO.println s!"  missing terms {(Enrichment.missingTerms base ss).length} → {stillMissing.length}"
  match out with
  | some f =>
      writeKB f grown
      IO.println s!"  wrote {grown.items.length} items and {grown.sub.length + grown.inst.length} statements to {f}"
  | none => pure ()
  return 0

/-- `authority`: collect the external identifiers of the given items — the
string-valued statements whose property carries a `formatter URL` (P1630) — and
compile them into a Lean module of the `IdKB` layer.

This is how a property reported by `frontier` as an *external identifier* is
added: not as a new predicate, but as one more column of the authority file the
development already models. -/
def cmdAuthority (cache : String) (offline : Bool) (ids : List String) (name : Option String)
    (mod : Option String) : IO UInt32 := do
  if ids.isEmpty then
    IO.eprintln "usage: wikidata authority Q42989 [Q…] [--module M] [--name N]"
    return 1
  let mut rows : List (Qid × Qid × String) := []
  let mut props : List String := []
  for id in ids do
    let body ← fetchEntityJson cache offline id
    match entityJson? body id with
    | none =>
        IO.eprintln s!"{id}: malformed entity JSON"
        return 1
    | some j =>
        let cs := stringClaimsOfJson j
        IO.println s!"{showItem (.wd id)}: {cs.length} string-valued statement(s)"
        for (p, v) in cs do
          props := props ++ [p]
          rows := rows ++ [(Qid.wd id, Qid.wd p, v)]
  -- keep only the properties that have a formatter URL: those are the external
  -- identifier properties
  let mut formatters : List (Qid × String × String) := []
  for p in props.dedup do
    let body ← fetchEntityJson cache offline p
    match entityJson? body p with
    | none => pure ()
    | some j =>
        match formatterOfJson j with
        | some (pre, post) => formatters := formatters ++ [(Qid.wd p, pre, post)]
        | none => pure ()
  let keep := formatters.map Prod.fst
  let idRows := rows.filter fun r => keep.contains r.2.1
  let T : IdKB :=
    { name := name.getD "authority file"
      items := ids.map Qid.wd
      ids := ⟨idRows⟩
      formatters := formatters }
  IO.println s!"{idRows.length} external identifier(s) over {keep.length} identifier propert(y/ies)"
  IO.println s!"  one identifier per item and property: {T.singleValueB}"
  IO.println s!"  one item per identifier:              {T.distinctValuesB}"
  match mod with
  | some m =>
      let target := m.replace "." "/" ++ ".lean"
      if let some dir := (System.FilePath.mk target).parent then IO.FS.createDirAll dir
      IO.FS.writeFile target (authorityModule m "the Wikidata API" T)
      IO.println s!"  compiled the authority file to {target}"
  | none => pure ()
  return 0

/-- `scanlean`: compile a scan into a Lean module. -/
def cmdScanLean (scanFile : String) (mod : String) (out : Option String) : IO UInt32 := do
  let ss ← readScan scanFile
  let target := out.getD (mod.replace "." "/" ++ ".lean")
  if let some dir := (System.FilePath.mk target).parent then IO.FS.createDirAll dir
  IO.FS.writeFile target (scanModule mod ("`" ++ scanFile ++ "`") ss)
  IO.println s!"compiled {scanFile} to {target}"
  IO.println s!"  documents  {ss.length}"
  IO.println s!"  mentions   {(ss.flatMap fun s => s.mentions).length}"
  IO.println s!"  citations  {(ss.flatMap fun s => s.cites).length}"
  return 0

end Cli
end Wikidata
