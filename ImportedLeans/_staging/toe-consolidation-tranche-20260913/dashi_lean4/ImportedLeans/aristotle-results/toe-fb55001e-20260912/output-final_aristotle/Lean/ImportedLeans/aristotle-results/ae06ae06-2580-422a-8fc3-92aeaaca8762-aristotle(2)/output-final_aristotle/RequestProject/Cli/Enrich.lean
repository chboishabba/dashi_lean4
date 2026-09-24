import RequestProject.Cli.Fetch
import RequestProject.Cli.ScanFormat
import RequestProject.Generated.Glossary
import RequestProject.Sitelinks
import RequestProject.ExternalIds

/-!
# The enrichment tool: downloading and scanning sources

This is the `IO` half of the auto-enrichment loop whose verified core is
`RequestProject.Enrichment`.  It knows about three kinds of document:

* a **Wikidata entity** (`Special:EntityData/Q….json`), from which the tool reads
  the *sitelinks* — the Wikipedia articles about the item, in every language —
  and the *properties* the item's statements use;
* a **Wikipedia article** in some language, from which it reads the articles it
  links to (turned into Wikidata items through `pageprops.wikibase_item`) and
  the external addresses it cites — the article's sources;
* an **external source**, from which it reads the addresses it links to and the
  terms of the glossary it names.

Each document is reduced to a `Wikidata.ScannedSource`, and everything after
that is the verified core: `Enrichment.termDemand`, `Enrichment.predicateDemand`
and `Enrichment.sourceDemand` say what is missing and how often it is referred
to, and `KB.enrich` adds the statements the scan suggests.

Nothing here is trusted.  The scan is written to disk in the format of
`RequestProject.Cli.ScanFormat` (which round-trips), the enriched knowledge base
is written in the `.wdkb` format (which round-trips) and re-validated, and the
compiled Lean module is re-checked by Lean.
-/

namespace Wikidata
namespace Cli

open Lean (Json)

/-! ### Small string utilities -/

/-- Percent-encodes a string for use in a URL. -/
def urlEncode (s : String) : String :=
  String.join <| s.toList.map fun c =>
    if c.isAlphanum || c = '-' || c = '_' || c = '.' || c = '~' then c.toString
    else
      let n := c.toNat
      if n < 128 then
        let hex := fun (d : Nat) => "0123456789ABCDEF".toList.getD d '0'
        "%" ++ (hex (n / 16)).toString ++ (hex (n % 16)).toString
      else
        -- non-ASCII: encode the UTF-8 bytes
        String.join (c.toString.toUTF8.toList.map fun b =>
          let hex := fun (d : Nat) => "0123456789ABCDEF".toList.getD d '0'
          "%" ++ (hex (b.toNat / 16)).toString ++ (hex (b.toNat % 16)).toString)

/-- A filesystem-safe name for a cached document. -/
def cacheKey (s : String) : String :=
  String.ofList <| (s.toList.map fun c => if c.isAlphanum then c else '_').take 120

/-- Whether `needle` occurs in `hay`. -/
def hasSubstr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The addresses of the form `http…` occurring in a text, cut at the first
character that cannot occur in a URL. -/
def urlStopChar (c : Char) : Bool :=
  c = '"' || c = '\'' || c = '<' || c = '>' || c = ' ' || c = '\n' || c = '\t' ||
  c = ')' || c = ']' || c = '}' || c = '\\'

/-- Collects the addresses in a character list. -/
partial def extractUrlsAux : List Char → List String → List String
  | [], acc => acc.reverse
  | c :: rest, acc =>
      let cs := c :: rest
      if c = 'h' && (String.ofList (cs.take 8) = "https://" ||
          String.ofList (cs.take 7) = "http://") then
        let url := cs.takeWhile fun d => !urlStopChar d
        extractUrlsAux (cs.drop (max 1 url.length)) (String.ofList url :: acc)
      else extractUrlsAux rest acc

def extractUrls (s : String) : List String :=
  ((extractUrlsAux s.toList []).map fun u =>
      -- drop trailing punctuation
      if u.endsWith "." || u.endsWith "," || u.endsWith ";" then (u.dropEnd 1).toString else u).dedup

/-- The items of a label table whose label occurs in a text.  Only labels of at
least six characters are used, so that short words do not create spurious
mentions. -/
def mentionsOfText (labels : List (String × String)) (text : String) : List Qid :=
  let low := text.toLower
  (labels.filterMap fun (id, lab) =>
    if lab.length ≥ 6 && hasSubstr low lab.toLower then some (Qid.wd id) else none).dedup

/-! ### Reading the JSON of the APIs -/

/-- The JSON of one entity inside a `Special:EntityData` document. -/
def entityJson? (body : String) (id : String) : Option Json :=
  match Json.parse body with
  | .ok j => ((j.getObjVal? "entities").bind (·.getObjVal? id)).toOption
  | .error _ => none

/-- The sitelinks of an entity: pairs `(site, page title)`, over **all**
languages. -/
def sitelinksOfJson (j : Json) : List (String × String) :=
  match (j.getObjVal? "sitelinks").toOption with
  | some sl => (objEntries sl).filterMap fun (site, v) =>
      ((v.getObjValAs? String "title").toOption).map fun t => (site, t)
  | none => []

/-- The Wikidata properties an entity's statements use. -/
def predicatesOfJson (j : Json) : List String :=
  match (j.getObjVal? "claims").toOption with
  | some cs => (objEntries cs).map Prod.fst
  | none => []

/-- The string-valued statements of an entity, as pairs `(property, value)`.
External identifiers (P646, P373, …) are exactly the statements of this kind
that this development cares about. -/
def stringClaimsOfJson (j : Json) : List (String × String) :=
  match (j.getObjVal? "claims").toOption with
  | some cs => (objEntries cs).flatMap fun (prop, arr) =>
      ((arr.getArr?).toOption.getD #[]).toList.filterMap fun st =>
        if statementRank st = "deprecated" then none
        else
          (((st.getObjVal? "mainsnak").bind (·.getObjVal? "datavalue")
            |>.bind (·.getObjValAs? String "value")).toOption).map fun v => (prop, v)
  | none => []

/-- The `formatter URL` (P1630) of a property, split at the `$1` placeholder. -/
def formatterOfJson (j : Json) : Option (String × String) :=
  ((stringClaimsOfJson j).lookup "P1630").map fun u =>
    match u.splitOn "$1" with
    | [pre, post] => (pre, post)
    | _ => (u, "")

/-- The pages of a `formatversion=2` `action=query` response. -/
def apiPages (body : String) : List Json :=
  match Json.parse body with
  | .ok j =>
      match ((j.getObjVal? "query").bind (·.getObjVal? "pages")).toOption with
      | some ps =>
          match ps.getArr? with
          | .ok arr => arr.toList
          | .error _ => (objEntries ps).map Prod.snd
      | none => []
  | .error _ => []

/-- The Wikidata item a page is about, from `pageprops.wikibase_item`. -/
def pageItem? (p : Json) : Option String :=
  ((p.getObjVal? "pageprops").bind (·.getObjValAs? String "wikibase_item")).toOption

/-- The external addresses a page cites. -/
def pageExtLinks (p : Json) : List String :=
  match (p.getObjVal? "extlinks").toOption with
  | some arr =>
      match arr.getArr? with
      | .ok a => a.toList.filterMap fun e =>
          ((e.getObjValAs? String "url").toOption).orElse fun _ =>
            (e.getObjValAs? String "*").toOption
      | .error _ => []
  | none => []

/-! ### Talking to the APIs -/

/-- Fetches a URL, retrying a few times when the API asks us to slow down. -/
partial def httpGetRetry (url : String) (attempts : ℕ := 8) : IO String := do
  try
    httpGet url
  catch e =>
    if attempts = 0 then throw e
    IO.sleep 15000
    httpGetRetry url (attempts - 1)

/-- Fetches a URL, caching the answer under `dir` with the given key. -/
def fetchCached (dir : System.FilePath) (offline : Bool) (key url : String) : IO String := do
  let path := dir / (key ++ ".json")
  if ← path.pathExists then
    IO.FS.readFile path
  else if offline then
    throw (IO.userError s!"{key} is not in the cache ({path}) and --offline was given")
  else
    let body ← httpGetRetry url
    IO.FS.createDirAll dir
    IO.FS.writeFile path body
    IO.sleep 1000
    return body

/-- The API query for the links, the item identifiers behind them and the
external addresses of one article. -/
def articleQueryUrl (lang title : String) : String :=
  s!"https://{lang}.wikipedia.org/w/api.php?action=query&format=json&formatversion=2" ++
    "&generator=links&gpllimit=500&gplnamespace=0&prop=pageprops&ppprop=wikibase_item" ++
    "&titles=" ++ urlEncode title

/-- The API query for the external addresses (the references) of one article. -/
def extLinkQueryUrl (lang title : String) : String :=
  s!"https://{lang}.wikipedia.org/w/api.php?action=query&format=json&formatversion=2" ++
    "&prop=extlinks&ellimit=500&titles=" ++ urlEncode title

/-- The address of an article. -/
def articleUrl (lang title : String) : String :=
  s!"https://{lang}.wikipedia.org/wiki/" ++ urlEncode (title.replace " " "_")

/-- Downloads and scans one Wikipedia article: the items its links point at, the
properties of the Wikidata item it is about, and the sources it cites. -/
def scanArticle (dir : System.FilePath) (offline : Bool) (lang title : String)
    (predicates : List String) : IO ScannedSource := do
  let links ← fetchCached dir offline (cacheKey s!"{lang}-{title}-links") (articleQueryUrl lang title)
  let exts ← fetchCached dir offline (cacheKey s!"{lang}-{title}-ext") (extLinkQueryUrl lang title)
  let mentions := (apiPages links).filterMap fun p => (pageItem? p).map Qid.wd
  let cites := ((apiPages exts).flatMap pageExtLinks).dedup
  return { ref := ⟨articleUrl lang title, lang, title⟩
           mentions := mentions.dedup
           predicates := predicates
           cites := cites }

/-- Downloads an external source, caching its text. -/
def fetchWebText (dir : System.FilePath) (offline : Bool) (url : String) : IO String := do
  let path := dir / (cacheKey url ++ ".txt")
  if ← path.pathExists then
    return (← IO.FS.readFile path)
  if offline then
    throw (IO.userError s!"{url} is not in the cache ({path}) and --offline was given")
  IO.FS.createDirAll dir
  let tmp := dir / (cacheKey url ++ ".raw")
  let out ← IO.Process.output
    { cmd := "curl"
      args := #["-sSL", "--max-time", "60", "--max-filesize", "8000000", "-A", userAgent,
                "-o", tmp.toString, url] }
  let body ←
    if out.exitCode = 0 then do
      let bytes ← IO.FS.readBinFile tmp
      -- documents are of every imaginable encoding; anything that is not valid
      -- UTF-8 is read as its ASCII skeleton, which is enough to find addresses
      -- and English terms
      pure (String.fromUTF8? bytes |>.getD
        (String.ofList (bytes.toList.filterMap fun b =>
          if b.toNat < 128 then some (Char.ofNat b.toNat) else none)))
    else pure ""
  IO.FS.writeFile path body
  try IO.FS.removeFile tmp catch _ => pure ()
  return body

/-- Downloads an external source and scans it: the addresses it links to, and
the glossary terms it names. -/
def scanWebSource (dir : System.FilePath) (offline : Bool) (labels : List (String × String))
    (url : String) : IO ScannedSource := do
  let body ← fetchWebText dir offline url
  let text := String.ofList (body.toList.take 400000)
  return { ref := ⟨url, "", ""⟩
           mentions := mentionsOfText labels text
           predicates := []
           cites := (extractUrls text).filter fun u => u ≠ url }

/-- The label table used when scanning external sources: everything the project's
glossary knows. -/
def glossaryLabels : List (String × String) :=
  Generated.glossary.entries.map fun g => (g.id, g.label)

/-- The Wikidata properties this development has a Lean predicate for: the
identifiers that occur in its sources.  A property a source uses and this list
does not contain is a candidate for a new predicate
(`Enrichment.predicateDemand`). -/
def modelledPredicates : List String :=
  ["P279", "P31", "P361", "P171", "P27", "P155", "P26", "P105", "P22", "P25",
   "P179", "P131", "P1963", "P569", "P527", "P17", "P156", "P19", "P1545",
   "P8810", "P1082", "P1038", "P2670", "P225", "P1647", "P36", "P2738", "P2737",
   "P1696", "P582", "P580", "P1889", "P585", "P1709", "P5137", "P3448", "P1630",
   "P1376", "P854", "P248", "P2370", "P227", "P214", "P143", "P40", "P2241",
   "P1039", "P571", "P460", "P3831", "P1628",
   -- added by the enrichment run of `docs/ENRICHMENT.md`, in the order the
   -- ranking asked for them: `RequestProject/FieldsOfStudy.lean`
   "P2578", "P2579", "P910", "P301"]

/-! ### Reading and writing scans -/

/-- Reads a scan from disk. -/
def readScan (path : System.FilePath) : IO (List ScannedSource) := do
  let raw ← IO.FS.readFile path
  let txt := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
  match parseScan? txt with
  | some ss => return ss
  | none => throw (IO.userError s!"{path}: not a well-formed .scan file")

/-- Drops from a scanned source everything that cannot be written to disk, so
that `Cli.scanCleanB` holds and the round-trip theorem applies. -/
def sanitizeSource (s : ScannedSource) : ScannedSource :=
  { ref := ⟨sanitizeField s.ref.url, sanitizeField s.ref.lang, sanitizeField s.ref.title⟩
    mentions := s.mentions.filter fun q => isWdB q && cleanTokenB (qidTok q)
    predicates := s.predicates.filter cleanTokenB
    cites := s.cites.filter cleanTokenB }
where
  /-- Replaces the separators by spaces. -/
  sanitizeField (x : String) : String := (x.replace "\t" " ").replace "\n" " "

/-- Writes a scan to disk, refusing anything the codec cannot round-trip. -/
def writeScan (path : System.FilePath) (ss : List ScannedSource) : IO Unit := do
  let ss := ss.map sanitizeSource
  if !scanCleanB ss then
    throw (IO.userError "refusing to write: a field contains a separator")
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (renderScan ss)

/-! ### Generating Lean modules -/

/-- A Lean string literal. -/
def leanQuote (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

/-- An identifier, as a Lean term. -/
def leanQid : Qid → String
  | .wd id => "Qid.wd " ++ leanQuote id
  | .ont n => "Qid.ont " ++ leanQuote n
  | .about q => "Qid.about (" ++ leanQid q ++ ")"
  | .lvl n => "Qid.lvl " ++ toString n

/-- One scanned document, as a Lean term. -/
def leanSource (s : ScannedSource) : String :=
  let list := fun (xs : List String) => "[" ++ String.intercalate ", " xs ++ "]"
  "  ⟨⟨" ++ leanQuote s.ref.url ++ ", " ++ leanQuote s.ref.lang ++ ", " ++
    leanQuote s.ref.title ++ "⟩,\n   " ++ list (s.mentions.map leanQid) ++ ",\n   " ++
    list (s.predicates.map leanQuote) ++ ",\n   " ++ list (s.cites.map leanQuote) ++ "⟩"

/-- Compiles a scan into a Lean module: the scanned documents as data, plus the
state of the enrichment run they belong to. -/
def scanModule (mod : String) (origin : String) (ss : List ScannedSource) : String :=
  let header :=
    "/-\n  " ++ mod ++ "\n\n  Machine-generated by `wikidata scanlean` from " ++ origin ++
    ".\n  Do not edit by hand: re-run the tool instead.\n\n  " ++
    toString ss.length ++ " scanned document(s), " ++
    toString (ss.flatMap (fun s => s.mentions)).length ++ " mention(s), " ++
    toString (ss.flatMap (fun s => s.cites)).length ++ " cited source(s).\n-/\n"
  let ns := "Wikidata" :: (mod.splitOn ".").drop 1
  let opens := String.join ((ns.map fun n => "namespace " ++ n ++ "\n"))
  let closes := String.join ((ns.reverse.map fun n => "end " ++ n ++ "\n"))
  header ++ "import RequestProject.Cli.Enrich\n\nset_option maxRecDepth 100000\n\n" ++
    opens ++ "\nopen Wikidata Cli\n\n" ++
    "/-- The documents the enrichment run downloaded and scanned. -/\ndef sources : List ScannedSource := [\n" ++
    String.intercalate ",\n" (ss.map leanSource) ++ "]\n\n" ++
    "/-- The languages of the scanned Wikipedia articles. -/\ndef languages : List String :=\n  " ++
    "(sources.map fun s => s.ref.lang).dedup\n\n" ++
    "/-- The properties this development models, as a list. -/\ndef modelled : List String := modelledPredicates\n\n" ++
    closes

/-- The identifier properties of a table that carry two different identifiers
for one item, i.e. that violate the single-value constraint. -/
def multiValuedProps (T : IdKB) : List Qid :=
  (T.ids.rows.filter fun r =>
    T.ids.rows.any fun r' => r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2 != r.2.2).map
      (fun r => r.2.1) |>.dedup

/-- The table with those properties dropped. -/
def singleValuedPart (T : IdKB) : IdKB :=
  let bad := multiValuedProps T
  { T with
    ids := ⟨T.ids.rows.filter fun r => !bad.contains r.2.1⟩
    formatters := T.formatters.filter fun f => !bad.contains f.1 }

/-- Compiles an authority file (external identifiers) into a Lean module.

Two tables are emitted: the whole downloaded file, with the verdict of each
constraint check on it, and its single-valued part, for which the partial
bijection theorem of `RequestProject.ExternalIds` applies. -/
def authorityModule (mod : String) (origin : String) (T : IdKB) : String :=
  let S := singleValuedPart T
  let bad := multiValuedProps T
  let header :=
    "/-\n  " ++ mod ++ "\n\n  Machine-generated by `wikidata authority` from " ++ origin ++
    ".\n  Do not edit by hand: re-run the tool instead.\n\n  " ++
    toString T.items.length ++ " item(s), " ++ toString T.ids.rows.length ++
    " external identifier(s) for " ++
    toString (T.ids.rows.map fun r => r.2.1).dedup.length ++ " propert(y/ies), of which " ++
    toString bad.length ++ " carry more than one identifier for one item.\n-/\n"
  let ns := "Wikidata" :: (mod.splitOn ".").drop 1
  let opens := String.join ((ns.map fun n => "namespace " ++ n ++ "\n"))
  let closes := String.join ((ns.reverse.map fun n => "end " ++ n ++ "\n"))
  let table := fun (nm : String) (U : IdKB) =>
    "def " ++ nm ++ " : IdKB where\n  name := " ++ leanQuote U.name ++ "\n  items := [" ++
    String.intercalate ", " (U.items.map leanQid) ++ "]\n  ids := ⟨[\n" ++
    String.intercalate ",\n" (U.ids.rows.map fun r =>
      "    (" ++ leanQid r.1 ++ ", " ++ leanQid r.2.1 ++ ", " ++ leanQuote r.2.2 ++ ")") ++
    "]⟩\n  formatters := [\n" ++
    String.intercalate ",\n" (U.formatters.map fun f =>
      "    (" ++ leanQid f.1 ++ ", " ++ leanQuote f.2.1 ++ ", " ++ leanQuote f.2.2 ++ ")") ++
    "]\n\n"
  let verdicts :=
    "/-- The verdict of the single-value constraint (Q19474404) on the downloaded\nfile. -/\n" ++
    "theorem authority_singleValueB : authority.singleValueB = " ++
      (if T.singleValueB then "true" else "false") ++ " := by native_decide\n\n" ++
    "/-- The verdict of the distinct-values constraint (Q21502410). -/\n" ++
    "theorem authority_distinctValuesB : authority.distinctValuesB = " ++
      (if T.distinctValuesB then "true" else "false") ++ " := by native_decide\n\n" ++
    (if T.singleValueB then
      "/-- So every item has at most one identifier per property. -/\n" ++
      "theorem authority_singleValue : authority.SingleValue :=\n" ++
      "  (IdKB.singleValueB_iff authority).1 authority_singleValueB\n\n"
     else
      "/-- Some property carries two identifiers for one item, so the single-value\nconstraint fails on the downloaded file: " ++
      String.intercalate ", " (bad.map qidTok) ++ ". -/\n" ++
      "theorem authority_not_singleValue : ¬ authority.SingleValue := fun h =>\n" ++
      "  absurd ((IdKB.singleValueB_iff authority).2 h) (by rw [authority_singleValueB]; decide)\n\n") ++
    (if T.distinctValuesB then
      "/-- Every identifier belongs to at most one item. -/\n" ++
      "theorem authority_distinctValues : authority.DistinctValues :=\n" ++
      "  (IdKB.distinctValuesB_iff authority).1 authority_distinctValuesB\n\n"
     else
      "/-- Two items share an identifier, so the distinct-values constraint fails. -/\n" ++
      "theorem authority_not_distinctValues : ¬ authority.DistinctValues := fun h =>\n" ++
      "  absurd ((IdKB.distinctValuesB_iff authority).2 h) (by rw [authority_distinctValuesB]; decide)\n\n")
  let singlePart :=
    "/-- The same file with the properties that carry several identifiers for one\nitem removed. -/\n" ++
    table "authoritySingle" S ++
    "/-- On this part both constraints hold. -/\n" ++
    "theorem authoritySingle_singleValue : authoritySingle.SingleValue :=\n" ++
    "  (IdKB.singleValueB_iff authoritySingle).1 (by native_decide)\n\n" ++
    "theorem authoritySingle_distinctValues : authoritySingle.DistinctValues :=\n" ++
    "  (IdKB.distinctValuesB_iff authoritySingle).1 (by native_decide)\n\n" ++
    "/-- So each of these identifier properties is a partial bijection between items\nand identifiers: the identifier identifies the item. -/\n" ++
    "theorem authoritySingle_partialBijection {q p : Qid} {v : String} :\n" ++
    "    authoritySingle.idOf q p = some v ↔ authoritySingle.itemById p v = some q :=\n" ++
    "  IdKB.idOf_eq_some_iff_itemById_eq_some authoritySingle_singleValue\n" ++
    "    authoritySingle_distinctValues\n\n"
  header ++ "import RequestProject.ExternalIds\n\nset_option maxRecDepth 100000\n\n" ++
    opens ++ "\nopen Wikidata\n\n" ++
    "/-- The external identifiers Wikidata records for these items. -/\n" ++
    table "authority" T ++ verdicts ++ singlePart ++ closes

/-- Compiles a sitelink table into a Lean module. -/
def sitelinksModule (mod : String) (origin : String) (S : SiteKB) : String :=
  let header :=
    "/-\n  " ++ mod ++ "\n\n  Machine-generated by `wikidata sitelinks --module` from " ++ origin ++
    ".\n  Do not edit by hand: re-run the tool instead.\n\n  " ++
    toString S.items.length ++ " item(s), " ++ toString S.links.length ++
    " sitelink(s) across " ++ toString (S.links.map fun l => l.2.site).dedup.length ++
    " sites.\n-/\n"
  let ns := "Wikidata" :: (mod.splitOn ".").drop 1
  let opens := String.join ((ns.map fun n => "namespace " ++ n ++ "\n"))
  let closes := String.join ((ns.reverse.map fun n => "end " ++ n ++ "\n"))
  header ++ "import RequestProject.Sitelinks\n\nset_option maxRecDepth 100000\n\n" ++
    opens ++ "\nopen Wikidata\n\n" ++
    "/-- The Wikipedia (and other Wikimedia) pages about these items, in every\nlanguage Wikidata records. -/\ndef sites : SiteKB where\n  items := [" ++
    String.intercalate ", " (S.items.map leanQid) ++ "]\n  links := [\n" ++
    String.intercalate ",\n" (S.links.map fun l =>
      "    (" ++ leanQid l.1 ++ ", ⟨" ++ leanQuote l.2.site ++ ", " ++
        leanQuote l.2.page ++ "⟩)") ++ "]\n\n" ++
    "/-- Every item has at most one page per site. -/\n" ++
    "theorem sites_functional : sites.Functional := SiteKB.functionalB_iff.1 (by native_decide)\n\n" ++
    "/-- Every page is linked from at most one item. -/\n" ++
    "theorem sites_pageInjective : sites.PageInjective :=\n  SiteKB.pageInjectiveB_iff.1 (by native_decide)\n\n" ++
    "/-- So the two lookups are mutually inverse: the downloaded table is a partial\nbijection between items and pages. -/\n" ++
    "theorem sites_partialBijection {q : Qid} {site p : String} :\n    sites.pageOf q site = some p ↔ sites.itemOf site p = some q :=\n" ++
    "  SiteKB.pageOf_eq_some_iff_itemOf_eq_some sites_functional sites_pageInjective\n\n" ++
    closes

end Cli
end Wikidata
