import RequestProject.Alignment

/-!
# Merging items and renaming identifiers

Wikidata's editors constantly *merge* items: two identifiers turn out to denote the same
thing (duplicates, or items linked by `said to be the same as`, P460) and one is
redirected to the other.  Ontologically a merge is a **renaming** of identifiers: the
statements of the knowledge base are rewritten along a map `f : Qid → Qid` that
identifies the merged items.

This file adds that operation to the executable layer:

* `Wikidata.KB.rename` rewrites a knowledge base along a map of identifiers, and
  `Wikidata.KB.mergeItems` is the special case given by a redirect table;
* the renaming map is an `equivalent class` alignment
  (`Wikidata.KB.renameAlignment`), so **no derived fact is lost**: every derived
  `subclass of` and `instance of` statement of the original knowledge base holds, after
  renaming, in the merged one (`Wikidata.KB.subclassOf_rename`,
  `Wikidata.KB.instanceOf_rename`), and classes, metaclasses and the level step between
  an instance and its class are transported along it by the theorems of
  `RequestProject.Alignment`;
* validity, on the other hand, is **not** preserved — merging is exactly the operation
  that can make an ontology inconsistent.  The worked fragment shows a harmless merge of
  a duplicate item, and three merges that the validator rejects: one creating a cycle in
  the class hierarchy, one merging an individual with its class (a level clash), and one
  merging two items that are instances of disjoint classes.

As elsewhere the identifiers follow Wikidata but the fragments are stylised excerpts.
-/

namespace Wikidata

namespace KB

/-- Rewrite every statement of a knowledge base along a map of identifiers. -/
def rename (kb : KB) (f : Qid → Qid) : KB where
  name := kb.name
  items := kb.items.map f
  levels := kb.levels.map (fun r => (f r.1, r.2))
  sub := kb.sub.map (fun r => (f r.1, f r.2))
  inst := kb.inst.map (fun r => (f r.1, f r.2))
  disj := kb.disj.map (fun r => (f r.1, f r.2))

/-- The identifier map given by a redirect table: an item listed on the left is replaced
by its target, everything else is kept. -/
def mergeMap (pairs : List (Qid × Qid)) (q : Qid) : Qid := (pairs.lookup q).getD q

/-- Merge the items of a knowledge base according to a redirect table. -/
def mergeItems (kb : KB) (pairs : List (Qid × Qid)) : KB := kb.rename (mergeMap pairs)

variable {kb : KB} {f : Qid → Qid}

theorem sub_rename {a b : Qid} (h : kb.Sub a b) : (kb.rename f).Sub (f a) (f b) :=
  List.mem_map.2 ⟨(a, b), h, rfl⟩

theorem inst_rename {a c : Qid} (h : kb.Inst a c) : (kb.rename f).Inst (f a) (f c) :=
  List.mem_map.2 ⟨(a, c), h, rfl⟩

theorem disj_rename {c d : Qid} (h : kb.Disj c d) : (kb.rename f).Disj (f c) (f d) := by
  rcases h with h | h
  · exact Or.inl (List.mem_map.2 ⟨(c, d), h, rfl⟩)
  · exact Or.inr (List.mem_map.2 ⟨(d, c), h, rfl⟩)

theorem mem_items_rename {a : Qid} (h : a ∈ kb.items) : f a ∈ (kb.rename f).items :=
  List.mem_map.2 ⟨a, h, rfl⟩

/-- **A renaming is an alignment**: every asserted statement of the original knowledge
base becomes a derived fact of the renamed one. -/
def renameAlignment (kb : KB) (f : Qid → Qid) (hv : kb.valid = true)
    (hv' : (kb.rename f).valid = true) :
    Ontology.Alignment (kb.toOntology hv) ((kb.rename f).toOntology hv') where
  map := f
  map_P279 h := Ontology.subclassOf_of_P279 (sub_rename h)
  map_P31 h := Ontology.instanceOf_of_P31 (inst_rename h)

@[simp] theorem renameAlignment_map (kb : KB) (f : Qid → Qid) (hv : kb.valid = true)
    (hv' : (kb.rename f).valid = true) : (renameAlignment kb f hv hv').map = f := rfl

/-- Renaming preserves the derived class hierarchy. -/
theorem subclassOf_rename (hv : kb.valid = true) (hv' : (kb.rename f).valid = true)
    {a b : Qid} (h : (kb.toOntology hv).SubclassOf a b) :
    ((kb.rename f).toOntology hv').SubclassOf (f a) (f b) :=
  (renameAlignment kb f hv hv').subclassOf h

/-- Renaming preserves the derived instance relation. -/
theorem instanceOf_rename (hv : kb.valid = true) (hv' : (kb.rename f).valid = true)
    {a c : Qid} (h : (kb.toOntology hv).InstanceOf a c) :
    ((kb.rename f).toOntology hv').InstanceOf (f a) (f c) :=
  (renameAlignment kb f hv hv').instanceOf h

/-- A class of the original knowledge base is still a class after the merge. -/
theorem isClass_rename (hv : kb.valid = true) (hv' : (kb.rename f).valid = true)
    {c : Qid} (h : (kb.toOntology hv).HasInstance c) :
    ((kb.rename f).toOntology hv').IsClass (f c) :=
  (renameAlignment kb f hv hv').isClass h

/-- A metaclass of the original knowledge base is still a metaclass after the merge. -/
theorem isMetaclass_rename (hv : kb.valid = true) (hv' : (kb.rename f).valid = true)
    {c : Qid} (h : (kb.toOntology hv).IsMetaclass c) :
    ((kb.rename f).toOntology hv').IsMetaclass (f c) :=
  (renameAlignment kb f hv hv').isMetaclass h

/-- Merged items are interchangeable: if two identifiers are sent to the same one, the
merged ontology derives for each the facts of the other. -/
theorem instanceOf_of_merge_eq (hv : kb.valid = true) (hv' : (kb.rename f).valid = true)
    {a b c : Qid} (hab : f a = f b) (h : (kb.toOntology hv).InstanceOf a c) :
    ((kb.rename f).toOntology hv').InstanceOf (f b) (f c) := by
  rw [← hab]
  exact instanceOf_rename hv hv' h

/-- An identifier listed in the redirect table is replaced by its target. -/
theorem mergeMap_eq_of_mem {pairs : List (Qid × Qid)} {a b : Qid}
    (h : pairs.lookup a = some b) : mergeMap pairs a = b := by
  simp [mergeMap, h]

/-- An identifier absent from the redirect table is untouched. -/
theorem mergeMap_eq_self {pairs : List (Qid × Qid)} {a : Qid}
    (h : pairs.lookup a = none) : mergeMap pairs a = a := by
  simp [mergeMap, h]

end KB

/-! ### A worked fragment -/

namespace MergeExample

open KB

/-- Abbreviation for an item. -/
def Q (s : String) : Qid := .wd s

/-- A fragment with a duplicate: `Q42` and `Q42-dup` both denote Douglas Adams. -/
def dupKB : KB where
  name := "dup"
  items := [Q "Q42", Q "Q42-dup", Q "Q5", Q "Q215627"]
  levels := [(Q "Q42", 0), (Q "Q42-dup", 0), (Q "Q5", 1), (Q "Q215627", 1)]
  sub := [(Q "Q5", Q "Q215627")]
  inst := [(Q "Q42", Q "Q5"), (Q "Q42-dup", Q "Q5")]

theorem dupKB_valid : dupKB.valid = true := by decide

/-- The redirect table merging the duplicate into `Q42`. -/
def redirect : List (Qid × Qid) := [(Q "Q42-dup", Q "Q42")]

/-- The merged knowledge base. -/
def mergedKB : KB := dupKB.mergeItems redirect

/-- Merging the duplicate keeps the knowledge base valid. -/
theorem mergedKB_valid : mergedKB.valid = true := by decide

/-- After the merge the duplicate identifier no longer occurs; both statements are now
statements about `Q42`. -/
theorem mergedKB_inst : mergedKB.inst = [(Q "Q42", Q "Q5"), (Q "Q42", Q "Q5")] := by decide

/-- The derived fact survives the merge. -/
theorem merged_instanceOf_person :
    mergedKB.isInstanceOf (Q "Q42") (Q "Q215627") = true := by decide

/-- Abstractly: the inherited fact about the duplicate is, after the merge, a fact about
`Q42`. -/
theorem merged_instanceOf_person_abstract :
    (mergedKB.toOntology mergedKB_valid).InstanceOf (Q "Q42") (Q "Q215627") := by
  have h : (dupKB.toOntology dupKB_valid).InstanceOf (Q "Q42-dup") (Q "Q215627") :=
    (KB.isInstanceOf_iff_instanceOf dupKB_valid (Q "Q42-dup") (Q "Q215627")).1 (by decide)
  have key := KB.instanceOf_of_merge_eq (f := mergeMap redirect) dupKB_valid mergedKB_valid
    (a := Q "Q42-dup") (b := Q "Q42") (by decide) h
  have e1 : mergeMap redirect (Q "Q42") = Q "Q42" := by decide
  have e2 : mergeMap redirect (Q "Q215627") = Q "Q215627" := by decide
  rw [e1, e2] at key
  exact key

/-! #### Merges the validator rejects -/

/-- Two disjoint chains of the class hierarchy. -/
def chainKB : KB where
  name := "chains"
  items := [Q "A", Q "B", Q "C", Q "D"]
  levels := [(Q "A", 1), (Q "B", 1), (Q "C", 1), (Q "D", 1)]
  sub := [(Q "A", Q "B"), (Q "C", Q "D")]

theorem chainKB_valid : chainKB.valid = true := by decide

/-- Merging `A` with `D` and `B` with `C` creates a cycle in the class hierarchy, and
the merged knowledge base is rejected. -/
theorem cyclicMerge_invalid :
    (chainKB.mergeItems [(Q "D", Q "A"), (Q "C", Q "B")]).valid = false := by decide

/-- Merging an individual with its own class breaks the level discipline. -/
theorem levelClashMerge_invalid :
    (dupKB.mergeItems [(Q "Q42", Q "Q5")]).valid = false := by decide

/-- A fragment with two items in classes declared disjoint. -/
def disjKB : KB where
  name := "disj"
  items := [Q "Q42", Q "Q11424-x", Q "Q5", Q "Q11424"]
  levels := [(Q "Q42", 0), (Q "Q11424-x", 0), (Q "Q5", 1), (Q "Q11424", 1)]
  inst := [(Q "Q42", Q "Q5"), (Q "Q11424-x", Q "Q11424")]
  disj := [(Q "Q5", Q "Q11424")]

theorem disjKB_valid : disjKB.valid = true := by decide

/-- Merging a human with a film violates the disjointness declaration: merging can turn
a consistent ontology into an inconsistent one. -/
theorem disjointMerge_invalid :
    (disjKB.mergeItems [(Q "Q11424-x", Q "Q42")]).valid = false := by decide

end MergeExample

end Wikidata
