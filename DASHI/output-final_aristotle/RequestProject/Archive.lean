/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Publish

/-!
# Long term archives: exporting to, and importing from, an archive item

An *archive item* (the shape `archive.org` items have: an identifier, some Dublin
Core style metadata and a list of named files) is how the project deposits a
snapshot of an ontology somewhere that outlives the project.

`Archive.bundleOf kb` is the deposit made for a knowledge base.  It carries the
same ontology twice — once in the project's own `.wdkb` text
(`Wikidata.Cli.renderKB`) and once as the public JSON Lines file
(`Wikidata.Publish.jsonlOfKB`) — together with a manifest listing, for every file,
its length and digest.

What is proved:

* `Archive.importKB?_bundleOf` — **an export can be imported**: reading the deposit
  back returns exactly the knowledge base that was deposited;
* `Archive.importKB?_rows_only` — and it can be imported even if only the public
  JSON Lines file survives, so the archive does not depend on the project's own
  format being understood;
* `Archive.bundle_copies_agree` — the two copies in a deposit are the same
  ontology, so a reader may use either;
* `Archive.checkManifest_manifestRows` and `Archive.checkManifest_bundleOf` — the
  manifest is honest: an importer that verifies every length and digest against
  the files accepts what the project deposits.
-/

namespace Wikidata
namespace Archive

open Wikidata.Cli Wikidata.Publish

/-! ### Items -/

/-- An archive item: an identifier, metadata and named files.  The field names are
those of an `archive.org` item. -/
structure Item where
  /-- The archive identifier, e.g. `wikidata-ontology-wdkb1-…`. -/
  identifier : String
  /-- The human readable title. -/
  title : String
  /-- The description. -/
  description : String := ""
  /-- The media type; data deposits use `data`. -/
  mediatype : String := "data"
  /-- The collection the item is filed under. -/
  collection : String := "opensource"
  /-- The licence of the deposit. -/
  licenseurl : String := "https://creativecommons.org/publicdomain/zero/1.0/"
  /-- Free-form subject tags. -/
  subjects : List String := []
  /-- The files of the item, as `(name, contents)`. -/
  files : List (String × String) := []
deriving DecidableEq, Repr, Inhabited

/-- The file holding the project's own text format. -/
def payloadName : String := "ontology.wdkb"

/-- The file holding the public JSON Lines export. -/
def rowsName : String := "ontology.jsonl"

/-- The file holding the manifest. -/
def manifestName : String := "manifest.tsv"

/-! ### Manifests -/

/-- The digest recorded for a file. -/
def digestOf (c : String) : String := hex16 (fnv1a c)

/-- The manifest of a list of files: name, length and digest of each. -/
def manifestRows (files : List (String × String)) : List (String × ℕ × String) :=
  files.map fun f => (f.1, f.2.length, digestOf f.2)

/-- The manifest as text: one tab separated line per file. -/
def renderManifest (files : List (String × String)) : String :=
  joinChar nl ((manifestRows files).map fun r =>
    joinChar tab [r.1, renderNat r.2.1, r.2.2])

/-- What an importer does with a manifest: check that every row matches the file
of that name. -/
def checkManifest (files : List (String × String)) (rows : List (String × ℕ × String)) : Bool :=
  rows.all fun r =>
    match files.lookup r.1 with
    | some c => (c.length == r.2.1) && (digestOf c == r.2.2)
    | none => false

/-- **The manifest is honest**: as long as no two files share a name, an importer
verifying every length and digest accepts. -/
theorem checkManifest_manifestRows :
    ∀ (files : List (String × String)), (files.map Prod.fst).Nodup →
      checkManifest files (manifestRows files) = true
  | [], _ => rfl
  | (n, c) :: fs, h => by
      have hnd : (fs.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using h)).2
      have hn : n ∉ fs.map Prod.fst := (List.nodup_cons.1 (by simpa using h)).1
      have ih := checkManifest_manifestRows fs hnd
      simp only [checkManifest, manifestRows, List.map_cons, List.all_cons, List.all_eq_true,
        List.mem_map, Bool.and_eq_true, List.lookup_cons] at ih ⊢
      refine ⟨by simp, ?_⟩
      rintro r ⟨f, hf, rfl⟩
      have hne : (f.1 == n) = false := by
        refine beq_eq_false_iff_ne.2 ?_
        intro hEq
        exact hn (List.mem_map.2 ⟨f, hf, hEq⟩)
      have := ih (f.1, f.2.length, digestOf f.2) ⟨f, hf, rfl⟩
      simpa [hne] using this

/-! ### Deposits -/

/-- The files of the deposit made for a knowledge base. -/
def bundleFiles (kb : KB) : List (String × String) :=
  let payload := renderKB kb
  let rows := jsonlOfKB kb
  let core := [(payloadName, payload), (rowsName, rows)]
  core ++ [(manifestName, renderManifest core)]

/-- The archive deposit for a knowledge base. -/
def bundleOf (kb : KB) : Item where
  identifier := "wikidata-ontology-" ++ cid kb
  title := "Wikidata ontology snapshot: " ++ kb.name
  description :=
    "A machine checked snapshot of a Wikidata-style ontology: " ++
    toString kb.items.length ++ " items, " ++ toString kb.sub.length ++
    " `subclass of` and " ++ toString kb.inst.length ++ " `instance of` statements."
  subjects := ["wikidata", "ontology", "lean4", "knowledge graph"]
  files := bundleFiles kb

/-- What an importer reads back from a set of archived files: the project's own
format if it is there, otherwise the public JSON Lines export. -/
def importKB? (files : List (String × String)) : Option KB :=
  match (files.lookup payloadName).bind parseKB? with
  | some kb => some kb
  | none => (files.lookup rowsName).bind parseJsonl?

theorem lookup_payload (kb : KB) : (bundleFiles kb).lookup payloadName = some (renderKB kb) := by
  simp [bundleFiles]

theorem lookup_rows (kb : KB) : (bundleFiles kb).lookup rowsName = some (jsonlOfKB kb) := by
  have h1 : (rowsName == payloadName) = false := by decide
  simp [bundleFiles, List.lookup_cons, h1]

/-- **A deposit can be imported**: what comes back out of the archive is exactly
the knowledge base that went in. -/
theorem importKB?_bundleOf (kb : KB) (h : KB.cleanB kb = true) :
    importKB? (bundleOf kb).files = some kb := by
  simp [importKB?, bundleOf, lookup_payload, parseKB?_renderKB kb h]

/-- **The archive does not depend on the project's own format**: the public JSON
Lines file alone is enough to recover the ontology. -/
theorem importKB?_rows_only (kb : KB) (h : jsonSafeKB kb = true) :
    importKB? [(rowsName, jsonlOfKB kb)] = some kb := by
  simp [importKB?, payloadName, rowsName, parseJsonl?_jsonlOfKB kb h]

/-- The two copies in a deposit are the same ontology. -/
theorem bundle_copies_agree (kb : KB) (h : KB.cleanB kb = true) (h' : jsonSafeKB kb = true) :
    ((bundleOf kb).files.lookup payloadName).bind parseKB? =
      ((bundleOf kb).files.lookup rowsName).bind parseJsonl? := by
  simp [bundleOf, lookup_payload, lookup_rows, parseKB?_renderKB kb h,
    parseJsonl?_jsonlOfKB kb h']

theorem bundleFiles_names_nodup (kb : KB) :
    (((bundleFiles kb).map Prod.fst)).Nodup := by
  simp [bundleFiles, payloadName, rowsName, manifestName]

/-- An importer that verifies the manifest accepts the project's deposits. -/
theorem checkManifest_bundleOf (kb : KB) :
    checkManifest (bundleOf kb).files (manifestRows (bundleOf kb).files) = true :=
  checkManifest_manifestRows _ (bundleFiles_names_nodup kb)

/-! ### Metadata -/

/-- An XML entity-escaped string. -/
def xmlEscape (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = '&' then "&amp;".toList
    else if c = '<' then "&lt;".toList
    else if c = '>' then "&gt;".toList
    else if c = '"' then "&quot;".toList
    else [c])

/-- One metadata element. -/
def xmlField (tag v : String) : String :=
  "  <" ++ tag ++ ">" ++ xmlEscape v ++ "</" ++ tag ++ ">"

/-- The `_meta.xml` of an archive item, in the shape `archive.org` expects. -/
def metaXml (it : Item) : String :=
  joinChar nl
    (["<metadata>",
      xmlField "identifier" it.identifier,
      xmlField "title" it.title,
      xmlField "description" it.description,
      xmlField "mediatype" it.mediatype,
      xmlField "collection" it.collection,
      xmlField "licenseurl" it.licenseurl] ++
      it.subjects.map (xmlField "subject") ++
      ["</metadata>"])

end Archive
end Wikidata
