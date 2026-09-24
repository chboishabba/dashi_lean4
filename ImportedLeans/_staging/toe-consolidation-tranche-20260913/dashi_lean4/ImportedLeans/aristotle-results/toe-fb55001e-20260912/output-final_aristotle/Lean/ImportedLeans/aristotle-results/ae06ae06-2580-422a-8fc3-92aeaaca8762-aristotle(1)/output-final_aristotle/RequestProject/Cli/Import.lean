import RequestProject.Engine
import Lean.Data.Json

/-!
# Importing Wikidata JSON

The command line tool downloads entities from the Wikidata API
(`https://www.wikidata.org/wiki/Special:EntityData/Q42.json`) or reads a local
copy of that JSON, and turns them into a `Wikidata.KB`.

The import goes through an intermediate, JSON-free record type
`Wikidata.Cli.Entity`, which is what the theorems of this file talk about:

* `Cli.sub_kbOfEntities_iff` / `Cli.inst_kbOfEntities_iff`: the importer asserts a
  `subclass of` (resp. `instance of`) statement **exactly when** the source data
  contains the corresponding P279 (resp. P31) claim — nothing is invented and
  nothing is dropped;
* `Cli.kbOfEntities_wellFormed`: the imported knowledge base is always
  well-formed, so the certified queries of `RequestProject.Engine` apply to it
  immediately.

Metaclass levels are not part of the Wikidata data model, so they are *inferred*
by `Cli.inferLevels` (propagating `level (class) = level (instance) + 1` upwards).
This is a heuristic: the tool always re-runs `KB.valid` afterwards and reports
what it finds, rather than assuming the guess was right.
-/

namespace Wikidata
namespace Cli

open Lean (Json)

/-! ### Entities -/

/-- A minimal view of a Wikidata entity: its identifier, its English label and its
item-valued statements, as pairs `(property id, value item id)`. -/
structure Entity where
  /-- The entity identifier, e.g. `"Q42"`. -/
  id : String
  /-- The English label, if any. -/
  label : String := ""
  /-- Item-valued claims `(property, value)`, e.g. `("P31", "Q5")`. -/
  claims : List (String × String) := []
deriving Repr, DecidableEq, Inhabited

/-- The `subclass of` (P279) statements contributed by an entity. -/
def subsOf (e : Entity) : List (Qid × Qid) :=
  e.claims.filterMap fun c => if c.1 = "P279" then some (Qid.wd e.id, Qid.wd c.2) else none

/-- The `instance of` (P31) statements contributed by an entity. -/
def instsOf (e : Entity) : List (Qid × Qid) :=
  e.claims.filterMap fun c => if c.1 = "P31" then some (Qid.wd e.id, Qid.wd c.2) else none

theorem mem_subsOf {e : Entity} {p : Qid × Qid} :
    p ∈ subsOf e ↔ ∃ v, p = (Qid.wd e.id, Qid.wd v) ∧ ("P279", v) ∈ e.claims := by
  simp only [subsOf, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hif⟩
    obtain ⟨c1, c2⟩ := c
    by_cases h : c1 = "P279"
    · subst h
      rw [if_pos rfl] at hif
      exact ⟨c2, (Option.some.inj hif).symm, hc⟩
    · rw [if_neg h] at hif; exact absurd hif (by simp)
  · rintro ⟨v, rfl, hv⟩
    exact ⟨("P279", v), hv, by simp⟩

theorem mem_instsOf {e : Entity} {p : Qid × Qid} :
    p ∈ instsOf e ↔ ∃ v, p = (Qid.wd e.id, Qid.wd v) ∧ ("P31", v) ∈ e.claims := by
  simp only [instsOf, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hif⟩
    obtain ⟨c1, c2⟩ := c
    by_cases h : c1 = "P31"
    · subst h
      rw [if_pos rfl] at hif
      exact ⟨c2, (Option.some.inj hif).symm, hc⟩
    · rw [if_neg h] at hif; exact absurd hif (by simp)
  · rintro ⟨v, rfl, hv⟩
    exact ⟨("P31", v), hv, by simp⟩

/-! ### Inferring metaclass levels -/

/-- One propagation step for the level assignment. -/
def inferStep (items : List Qid) (sub inst : List (Qid × Qid)) (L : List (Qid × ℕ)) :
    List (Qid × ℕ) :=
  items.map fun q =>
    let get : Qid → ℕ := fun x => (L.lookup x).getD 0
    let base := if sub.any (fun p => p.1 == q || p.2 == q) then 1 else 0
    let ups := (inst.filter (fun p => p.2 == q)).map fun p => get p.1 + 1
    let sames := ((sub.filter (fun p => p.1 == q)).map fun p => get p.2) ++
      ((sub.filter (fun p => p.2 == q)).map fun p => get p.1)
    (q, (get q :: base :: (ups ++ sames)).foldl max 0)

/-- Iterated propagation. -/
def inferIter (items : List Qid) (sub inst : List (Qid × Qid)) :
    ℕ → List (Qid × ℕ) → List (Qid × ℕ)
  | 0, L => L
  | n + 1, L => inferIter items sub inst n (inferStep items sub inst L)

/-- A guess at the metaclass levels: individuals sit at level `0`, a class sits one
level above its instances, and classes related by `subclass of` sit at the same
(positive) level. -/
def inferLevels (items : List Qid) (sub inst : List (Qid × Qid)) : List (Qid × ℕ) :=
  inferIter items sub inst (items.length + 1) []

/-! ### Building a knowledge base -/

/-- The items mentioned by a list of entities: their own identifiers together with
the values of their P31 and P279 claims. -/
def entityItems (es : List Entity) : List Qid :=
  (es.flatMap fun e => Qid.wd e.id :: ((subsOf e ++ instsOf e).map Prod.snd)).dedup

/-- The knowledge base determined by a list of entities. -/
def kbOfEntities (name : String) (es : List Entity) : KB :=
  let items := entityItems es
  let sub := es.flatMap subsOf
  let inst := es.flatMap instsOf
  { name := name
    items := items
    levels := inferLevels items sub inst
    sub := sub
    inst := inst }

@[simp] theorem kbOfEntities_sub (name : String) (es : List Entity) :
    (kbOfEntities name es).sub = es.flatMap subsOf := rfl

@[simp] theorem kbOfEntities_inst (name : String) (es : List Entity) :
    (kbOfEntities name es).inst = es.flatMap instsOf := rfl

@[simp] theorem kbOfEntities_items (name : String) (es : List Entity) :
    (kbOfEntities name es).items = entityItems es := rfl

@[simp] theorem kbOfEntities_disj (name : String) (es : List Entity) :
    (kbOfEntities name es).disj = [] := rfl

/-- **The importer is faithful for `subclass of`**: it asserts `a ⊑ b` exactly when
some source entity carries the corresponding P279 claim. -/
theorem sub_kbOfEntities_iff {name : String} {es : List Entity} {a b : Qid} :
    (a, b) ∈ (kbOfEntities name es).sub ↔
      ∃ e ∈ es, ∃ v, a = Qid.wd e.id ∧ b = Qid.wd v ∧ ("P279", v) ∈ e.claims := by
  simp only [kbOfEntities_sub, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨v, hv, hc⟩ := mem_subsOf.1 hp
    exact ⟨e, he, v, by simp_all⟩
  · rintro ⟨e, he, v, rfl, rfl, hc⟩
    exact ⟨e, he, mem_subsOf.2 ⟨v, rfl, hc⟩⟩

/-- **The importer is faithful for `instance of`**. -/
theorem inst_kbOfEntities_iff {name : String} {es : List Entity} {a c : Qid} :
    (a, c) ∈ (kbOfEntities name es).inst ↔
      ∃ e ∈ es, ∃ v, a = Qid.wd e.id ∧ c = Qid.wd v ∧ ("P31", v) ∈ e.claims := by
  simp only [kbOfEntities_inst, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨v, hv, hc⟩ := mem_instsOf.1 hp
    exact ⟨e, he, v, by simp_all⟩
  · rintro ⟨e, he, v, rfl, rfl, hc⟩
    exact ⟨e, he, mem_instsOf.2 ⟨v, rfl, hc⟩⟩

theorem mem_entityItems_of_mem_subsOf {es : List Entity} {e : Entity} (he : e ∈ es)
    {p : Qid × Qid} (hp : p ∈ subsOf e) : p.1 ∈ entityItems es ∧ p.2 ∈ entityItems es := by
  obtain ⟨v, rfl, hc⟩ := mem_subsOf.1 hp
  refine ⟨?_, ?_⟩ <;> simp only [entityItems, List.mem_dedup, List.mem_flatMap]
  · exact ⟨e, he, List.mem_cons_self⟩
  · exact ⟨e, he, List.mem_cons_of_mem _ (by
      simp only [List.mem_map, List.mem_append]
      exact ⟨(Qid.wd e.id, Qid.wd v), Or.inl (mem_subsOf.2 ⟨v, rfl, hc⟩), rfl⟩)⟩

theorem mem_entityItems_of_mem_instsOf {es : List Entity} {e : Entity} (he : e ∈ es)
    {p : Qid × Qid} (hp : p ∈ instsOf e) : p.1 ∈ entityItems es ∧ p.2 ∈ entityItems es := by
  obtain ⟨v, rfl, hc⟩ := mem_instsOf.1 hp
  refine ⟨?_, ?_⟩ <;> simp only [entityItems, List.mem_dedup, List.mem_flatMap]
  · exact ⟨e, he, List.mem_cons_self⟩
  · exact ⟨e, he, List.mem_cons_of_mem _ (by
      simp only [List.mem_map, List.mem_append]
      exact ⟨(Qid.wd e.id, Qid.wd v), Or.inr (mem_instsOf.2 ⟨v, rfl, hc⟩), rfl⟩)⟩

/-- **An imported knowledge base is always well-formed**: every statement mentions
declared items, so the certified queries of the engine apply to it. -/
theorem kbOfEntities_wellFormed (name : String) (es : List Entity) :
    (kbOfEntities name es).wellFormed = true := by
  simp only [KB.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    kbOfEntities_sub, kbOfEntities_inst, kbOfEntities_disj, kbOfEntities_items]
  refine ⟨⟨?_, ?_⟩, by simp⟩
  · intro p hp
    obtain ⟨e, he, hp⟩ := List.mem_flatMap.1 hp
    exact mem_entityItems_of_mem_subsOf he hp
  · intro p hp
    obtain ⟨e, he, hp⟩ := List.mem_flatMap.1 hp
    exact mem_entityItems_of_mem_instsOf he hp

/-! ### Reading Wikidata JSON

These functions are the (unverified) glue between the JSON returned by the
Wikidata API and the `Entity` records above; all the mathematical content lives in
the theorems proved for `kbOfEntities`. -/

/-- The key/value pairs of a JSON object (`[]` for anything else). -/
def objEntries : Json → List (String × Json)
  | .obj m => m.toArray.toList.map fun p => (p.1, p.2)
  | _ => []

/-- The item id a statement points at, if it is an item-valued statement. -/
def statementValueId? (st : Json) : Option String :=
  ((st.getObjVal? "mainsnak").bind (·.getObjVal? "datavalue") |>.bind (·.getObjVal? "value")
    |>.bind (·.getObjValAs? String "id")).toOption

/-- The rank of a statement (`"normal"` when absent). -/
def statementRank (st : Json) : String :=
  (st.getObjValAs? String "rank").toOption.getD "normal"

/-- The label of an entity in one language of the JSON, if present. -/
def entityLabelIn (j : Json) (lang : String) : Option String :=
  ((j.getObjVal? "labels").bind (·.getObjVal? lang) |>.bind
    (·.getObjValAs? String "value")).toOption

/-- The title of the English Wikipedia article of an entity, if any. -/
def entityEnwikiTitle (j : Json) : Option String :=
  ((j.getObjVal? "sitelinks").bind (·.getObjVal? "enwiki") |>.bind
    (·.getObjValAs? String "title")).toOption

/-- The English label of an entity, if any.  Wikidata increasingly stores names
that are the same in every language under the language code `mul`, and some items
have only an English Wikipedia article to go by, so those are used as fallbacks.
Labels are documentation: no theorem of this development depends on them. -/
def entityLabel (j : Json) : String :=
  ((entityLabelIn j "en").orElse fun _ =>
    (entityLabelIn j "mul").orElse fun _ =>
      (entityLabelIn j "en-gb").orElse fun _ => entityEnwikiTitle j).getD ""

/-- Reads one entity of the Wikidata JSON serialisation.  Deprecated statements and
statements whose value is not an item are skipped. -/
def entityOfJson (j : Json) : Option Entity := do
  let id ← (j.getObjValAs? String "id").toOption
  let claims := (j.getObjVal? "claims").toOption.getD Json.null
  let cs : List (String × String) := (objEntries claims).flatMap fun (prop, arr) =>
    ((arr.getArr?).toOption.getD #[]).toList.filterMap fun st =>
      if statementRank st = "deprecated" then none
      else (statementValueId? st).map fun v => (prop, v)
  return { id := id, label := entityLabel j, claims := cs }

/-- Reads the entities of a `Special:EntityData` JSON document, or of a bare JSON
object/array of entities. -/
def entitiesOfJson (j : Json) : List Entity :=
  match (j.getObjVal? "entities").toOption with
  | some ents => (objEntries ents).filterMap fun p => entityOfJson p.2
  | none =>
    match j.getArr? with
    | .ok arr => arr.toList.filterMap entityOfJson
    | .error _ =>
      match entityOfJson j with
      | some e => [e]
      | none => (objEntries j).filterMap fun p => entityOfJson p.2

/-- Reads a JSON document into a knowledge base. -/
def kbOfJson (name : String) (j : Json) : KB := kbOfEntities name (entitiesOfJson j)

/-- Reads a JSON string into a knowledge base. -/
def kbOfJsonString (name : String) (s : String) : Except String KB :=
  match Json.parse s with
  | .ok j => .ok (kbOfJson name j)
  | .error e => .error e

end Cli
end Wikidata
