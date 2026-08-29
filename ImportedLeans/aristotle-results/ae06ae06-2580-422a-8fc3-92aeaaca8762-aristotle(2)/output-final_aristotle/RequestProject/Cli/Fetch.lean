import RequestProject.Cli.Import
import RequestProject.Cli.Format

/-!
# Talking to the Wikidata API and to the local disk

The `IO` layer of the command line tool:

* `Cli.fetchEntityJson` downloads `Special:EntityData/<id>.json` (through `curl`)
  and caches it under a local directory, so repeated runs work offline;
* `Cli.crawl` follows `instance of` / `subclass of` links up to a given depth,
  which is how a self-contained fragment of the Wikidata ontology is obtained;
* `Cli.readKB` / `Cli.writeKB` read and write the verified text format of
  `RequestProject.Cli.Format`.

There is no mathematics here — every claim about what these functions produce is
proved in `RequestProject.Cli.Import` (faithfulness of the import) and
`RequestProject.Cli.Format` (losslessness of the file format).
-/

namespace Wikidata
namespace Cli

open Lean (Json)

/-- The user agent sent to the Wikidata API. -/
def userAgent : String := "wikidata-lean-cli/1.0 (Lean 4 formalisation of the Wikidata ontology)"

/-- The URL of the JSON serialisation of an entity. -/
def entityDataUrl (id : String) : String :=
  "https://www.wikidata.org/wiki/Special:EntityData/" ++ id ++ ".json"

/-- Fetches a URL with `curl`. -/
def httpGet (url : String) : IO String := do
  let out ← IO.Process.output
    { cmd := "curl", args := #["-sSL", "--fail", "--max-time", "60", "-A", userAgent, url] }
  if out.exitCode ≠ 0 then
    throw (IO.userError s!"download failed ({out.exitCode}) for {url}: {out.stderr}")
  return out.stdout

/-- Where a downloaded entity is cached. -/
def cachePath (dir : System.FilePath) (id : String) : System.FilePath := dir / (id ++ ".json")

/-- Returns the JSON of an entity, from the cache if possible.  With `offline` set,
never touches the network. -/
def fetchEntityJson (dir : System.FilePath) (offline : Bool) (id : String) : IO String := do
  let path := cachePath dir id
  if ← path.pathExists then
    IO.FS.readFile path
  else if offline then
    throw (IO.userError s!"{id} is not in the cache ({path}) and --offline was given")
  else
    let body ← httpGet (entityDataUrl id)
    IO.FS.createDirAll dir
    IO.FS.writeFile path body
    return body

/-- Reads one entity, from the cache or from the network. -/
def fetchEntity (dir : System.FilePath) (offline : Bool) (id : String) : IO (List Entity) := do
  let body ← fetchEntityJson dir offline id
  match Json.parse body with
  | .ok j => return entitiesOfJson j
  | .error e => throw (IO.userError s!"{id}: malformed JSON ({e})")

/-- The identifiers an entity links to through `instance of` or `subclass of`. -/
def ontologyLinks (e : Entity) : List String :=
  (e.claims.filter fun c => c.1 = "P31" || c.1 = "P279").map Prod.snd

/-- Downloads `ids` and, up to `depth` further steps, everything they are instances
or subclasses of. -/
partial def crawl (dir : System.FilePath) (offline : Bool) (verbose : Bool)
    (ids : List String) (depth : ℕ) : IO (List Entity) := do
  let mut seen : List String := []
  let mut acc : List Entity := []
  let mut frontier := ids
  let mut d := depth
  repeat
    let todo := (frontier.filter fun i => !seen.contains i).dedup
    if todo.isEmpty then break
    seen := seen ++ todo
    let mut next : List String := []
    for i in todo do
      if verbose then IO.println s!"  fetching {i}"
      let es ← fetchEntity dir offline i
      for e in es do
        acc := acc ++ [e]
        next := next ++ ontologyLinks e
    if d = 0 then break
    d := d - 1
    frontier := next
  return acc

/-! ### Labels

Labels are never part of what is proved: they end up in comments of the generated
Lean modules, so that a reader can tell `Q5` from `Q515`.  They are fetched in
batches from the `wbgetentities` API and cached in a single tab-separated file. -/

/-- Where the label cache lives. -/
def labelsPath (dir : System.FilePath) : System.FilePath := dir / "labels.tsv"

/-- The cached labels. -/
def readLabelCache (dir : System.FilePath) : IO (List (String × String)) := do
  let path := labelsPath dir
  if ← path.pathExists then
    let txt ← IO.FS.readFile path
    return (txt.splitOn "\n").filterMap fun line =>
      match line.splitOn "\t" with
      | [id, l] => if id.isEmpty then none else some (id, l)
      | _ => none
  else
    return []

/-- Adds rows to the label cache. -/
def appendLabelCache (dir : System.FilePath) (rows : List (String × String)) : IO Unit := do
  if rows.isEmpty then return
  IO.FS.createDirAll dir
  let old ← IO.FS.readFile (labelsPath dir) <|> pure ""
  let new := String.intercalate "" (rows.map fun p => p.1 ++ "\t" ++ p.2 ++ "\n")
  IO.FS.writeFile (labelsPath dir) (old ++ new)

/-- The API request asking for the labels of up to fifty entities. -/
def labelsUrl (ids : List String) : String :=
  "https://www.wikidata.org/w/api.php?action=wbgetentities&format=json&props=labels" ++
    "&languages=en%7Cmul%7Cen-gb&ids=" ++ String.intercalate "%7C" ids

/-- The labels carried by a `wbgetentities` response. -/
def labelsOfJson (j : Json) : List (String × String) :=
  match (j.getObjVal? "entities").toOption with
  | some ents => (objEntries ents).filterMap fun p =>
      let l := entityLabel p.2
      if l.isEmpty then none else some (p.1, l)
  | none => []

/-- Splits a list into chunks of at most `n + 1` elements. -/
def chunks {α : Type} (n : ℕ) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs).take (n + 1) :: chunks n ((x :: xs).drop (n + 1))
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- The labels of the given entities, from the cache and, unless `offline`, from
the API. -/
def fetchLabels (dir : System.FilePath) (offline : Bool) (ids : List String) :
    IO (List (String × String)) := do
  let cached ← readLabelCache dir
  let missing := ids.filter fun i => (cached.lookup i).isNone
  if offline || missing.isEmpty then
    return cached
  let mut fresh : List (String × String) := []
  for batch in chunks 49 missing do
    let body ← httpGet (labelsUrl batch)
    match Json.parse body with
    | .ok j => fresh := fresh ++ labelsOfJson j
    | .error _ => pure ()
  appendLabelCache dir fresh
  return cached ++ fresh

/-! ### Local files -/

/-- Reads a knowledge base from a file in the verified text format. -/
def readKB (path : System.FilePath) : IO KB := do
  let txt ← IO.FS.readFile path
  match parseKB? txt with
  | some kb => return kb
  | none => throw (IO.userError s!"{path}: not a well-formed .wdkb file")

/-- Writes a knowledge base in the verified text format.  Fails if some identifier
contains a separator, which is exactly the condition under which reading the file
back is guaranteed to return the same knowledge base
(`Cli.parseKB?_renderKB`). -/
def writeKB (path : System.FilePath) (kb : KB) : IO Unit := do
  if !KB.cleanB kb then
    throw (IO.userError "refusing to write: an identifier contains a tab or newline")
  IO.FS.writeFile path (renderKB kb)

end Cli
end Wikidata
