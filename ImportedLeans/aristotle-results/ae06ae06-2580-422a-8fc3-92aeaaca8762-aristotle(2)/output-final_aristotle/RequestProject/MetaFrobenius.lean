import RequestProject.Renaming

/-!
# The ontology inside the ontology: lift, reduction, retraction, pullback

Wikidata describes itself with its own vocabulary: `Q35120` (*entity*),
`Q16889133` (*class*), `Q19478619` (*metaclass*), `Q23958852` (*variable-order
class*) and so on are ordinary items, and statements *about* items are made with
the same properties as statements about the world. `RequestProject.SelfDescription`
builds a meta-ontology for an arbitrary knowledge base. This file studies the
*operation* that puts an ontology inside itself, and identifies it with four
familiar constructions.

The operation is the **meta lift**

```
KB.metaLift kb = kb.rename Qid.about
```

which re-reads every identifier `x` as the meta-level name `about x` of `x`; the
inverse operation is the **reduction**

```
KB.metaReduce kb = kb.rename Qid.deMeta
```

which strips one meta level (`about x ↦ x`, everything else unchanged).

What is proved.

* **Reduction.** `KB.metaReduce_metaLift`: the reduction undoes the lift exactly,
  `metaReduce (metaLift kb) = kb`, so no information is lost by moving an
  ontology to the meta level. Consequently `KB.metaLift` is injective.

* **Retraction.** `KB.metaRetract` packages the lift and the reduction as an
  `Ontology.Retract` in the sense of `RequestProject.Reflection`. Hence
  (`KB.metaLift_subclassOf_iff`, `KB.metaLift_instanceOf_iff`,
  `KB.metaLift_isMetaclass_iff`) the meta copy is a **conservative extension**:
  it derives exactly the facts the original derives, about the corresponding
  items, and nothing more. The composite `metaLift ∘ metaReduce` is the
  idempotent `KB.metaCore` whose fixed points are precisely the knowledge bases
  written entirely in meta-vocabulary (`KB.metaCore_eq_self_iff`).

* **A Frobenius-like automorphism.** Like the Frobenius endomorphism of a ring,
  `metaLift` is an injective structure-preserving endo-operation which is *not*
  surjective, fixes nothing (`KB.metaLift_ne_self`), commutes with the join of
  knowledge bases (`KB.metaLift_merge`) and with entailment
  (`KB.metaLift_entails_iff`), and becomes an **isomorphism onto the "perfect"
  part** — the meta-written knowledge bases — with inverse the reduction:
  `KB.metaEquiv : KB ≃ {kb // kb.allMetaB = true}`. Its iterates give the whole
  tower of meta levels (`KB.metaReduce_iterate_metaLift_iterate`), and the
  reduction fixes exactly the ground identifiers (`Qid.deMeta_eq_self_iff`),
  the analogue of the prime field.

* **Pullback.** `KB.metaLift_isPullback`: the meta copy, with the reduction back
  to the original, *is* the fibre product of the reduction along the identity —
  the two morphisms of `KB.metaPullbackLift` and `Ontology.pullback.fst` are
  mutually inverse. So "the ontology in the ontology" is a pullback square, not
  merely an embedding.

A small worked fragment at the end checks all of this by computation.
-/

namespace Wikidata

/-! ## Meta names and their reduction -/

/-- The **reduction** of an identifier: a meta-level name `about x` denotes `x`,
every other identifier denotes itself. -/
def Qid.deMeta : Qid → Qid
  | .about q => q
  | q => q

/-- How deeply an identifier is nested inside `about`. -/
def Qid.depth : Qid → ℕ
  | .about q => q.depth + 1
  | _ => 0

/-- An identifier is a *meta name* when it names another identifier. -/
def Qid.IsMeta (q : Qid) : Prop := ∃ x, q = .about x

/-- The decision procedure for `Qid.IsMeta`. -/
def Qid.isMetaB : Qid → Bool
  | .about _ => true
  | _ => false

@[simp] theorem Qid.deMeta_about (q : Qid) : (Qid.about q).deMeta = q := rfl
@[simp] theorem Qid.isMetaB_about (q : Qid) : (Qid.about q).isMetaB = true := rfl

theorem Qid.about_injective : Function.Injective Qid.about := by
  intro a b h; cases h; rfl

@[simp] theorem Qid.depth_about (q : Qid) : (Qid.about q).depth = q.depth + 1 := rfl

theorem Qid.about_ne_self (q : Qid) : Qid.about q ≠ q := by
  intro h
  have := congrArg Qid.depth h
  simp at this

theorem Qid.isMetaB_iff {q : Qid} : q.isMetaB = true ↔ q.IsMeta := by
  cases q <;> simp [Qid.isMetaB, Qid.IsMeta]

/-- The lift is a section of the reduction. -/
@[simp] theorem Qid.deMeta_comp_about : Qid.deMeta ∘ Qid.about = id := rfl

/-- An identifier is a meta name exactly when re-lifting its reduction returns it. -/
theorem Qid.about_deMeta_iff {q : Qid} : Qid.about q.deMeta = q ↔ q.IsMeta := by
  cases q <;> simp [Qid.deMeta, Qid.IsMeta]

/-- **The fixed points of the reduction are the ground identifiers** — the
analogue of the prime field of a Frobenius endomorphism. -/
theorem Qid.deMeta_eq_self_iff {q : Qid} : q.deMeta = q ↔ ¬ q.IsMeta := by
  cases q with
  | about x =>
      simp only [Qid.deMeta, Qid.IsMeta, not_exists]
      constructor
      · intro h; exact absurd h.symm (Qid.about_ne_self x)
      · intro h; exact absurd rfl (h x)
  | wd s => simp [Qid.deMeta, Qid.IsMeta]
  | ont s => simp [Qid.deMeta, Qid.IsMeta]
  | lvl n => simp [Qid.deMeta, Qid.IsMeta]

namespace KB

/-! ## The lift and the reduction of a knowledge base -/

/-- **The meta lift**: re-encode a whole knowledge base inside its own
meta-vocabulary, reading each identifier `x` as the meta name `about x`. -/
def metaLift (kb : KB) : KB := kb.rename Qid.about

/-- **The reduction**: read every meta name as the item it names. -/
def metaReduce (kb : KB) : KB := kb.rename Qid.deMeta

/-- The idempotent `metaLift ∘ metaReduce`: it rewrites a knowledge base into
meta-vocabulary, forgetting whatever was already there. -/
def metaCore (kb : KB) : KB := kb.metaReduce.metaLift

variable (kb kb' : KB)

@[simp] theorem metaLift_items : kb.metaLift.items = kb.items.map Qid.about := rfl
@[simp] theorem metaLift_sub :
    kb.metaLift.sub = kb.sub.map (fun r => (Qid.about r.1, Qid.about r.2)) := rfl
@[simp] theorem metaLift_inst :
    kb.metaLift.inst = kb.inst.map (fun r => (Qid.about r.1, Qid.about r.2)) := rfl

/-- **The reduction undoes the lift**: nothing is lost by moving an ontology to
the meta level. -/
@[simp] theorem metaReduce_metaLift : kb.metaLift.metaReduce = kb := by
  rw [metaLift, metaReduce, rename_rename, Qid.deMeta_comp_about, rename_id]

/-- The lift is injective. -/
theorem metaLift_injective : Function.Injective metaLift := by
  intro a b h
  have := congrArg metaReduce h
  rwa [metaReduce_metaLift, metaReduce_metaLift] at this

/-- Asserted statements are carried to the meta level. -/
theorem sub_metaLift {a b : Qid} (h : kb.Sub a b) :
    kb.metaLift.Sub (Qid.about a) (Qid.about b) := sub_rename h

theorem inst_metaLift {a c : Qid} (h : kb.Inst a c) :
    kb.metaLift.Inst (Qid.about a) (Qid.about c) := inst_rename h

/-- Statements of the meta copy come from statements of the original. -/
theorem sub_metaLift_iff {a b : Qid} :
    kb.metaLift.Sub (Qid.about a) (Qid.about b) ↔ kb.Sub a b :=
  sub_rename_iff Qid.about_injective

theorem inst_metaLift_iff {a c : Qid} :
    kb.metaLift.Inst (Qid.about a) (Qid.about c) ↔ kb.Inst a c :=
  inst_rename_iff Qid.about_injective

/-- Metaclass levels are unchanged by the lift. -/
@[simp] theorem metaLift_levelOf (q : Qid) : kb.metaLift.levelOf (Qid.about q) = kb.levelOf q :=
  levelOf_rename Qid.about_injective q

/-- **The meta copy of a valid ontology is valid, and only of a valid one.** -/
theorem metaLift_valid_iff : kb.metaLift.valid = true ↔ kb.valid = true :=
  valid_rename_iff Qid.about_injective

theorem metaLift_valid {kb : KB} (hv : kb.valid = true) : kb.metaLift.valid = true :=
  (metaLift_valid_iff kb).2 hv

theorem metaLift_wellFormed {kb : KB} (hwf : kb.wellFormed = true) :
    kb.metaLift.wellFormed = true := wellFormed_rename Qid.about_injective hwf

/-- The engine computes the same answers on the meta copy. -/
theorem metaLift_isSubclassOf_iff {kb : KB} (hwf : kb.wellFormed = true) {a b : Qid} :
    kb.metaLift.isSubclassOf (Qid.about a) (Qid.about b) = true ↔
      kb.isSubclassOf a b = true :=
  isSubclassOf_rename_iff Qid.about_injective hwf

theorem metaLift_isInstanceOf_iff {kb : KB} (hwf : kb.wellFormed = true) {a c : Qid} :
    kb.metaLift.isInstanceOf (Qid.about a) (Qid.about c) = true ↔
      kb.isInstanceOf a c = true :=
  isInstanceOf_rename_iff Qid.about_injective hwf

/-! ## The lift and the reduction as a retraction -/

/-- The lift, as a strict morphism of ontologies. -/
def metaSec {kb : KB} (hv : kb.valid = true) :
    Ontology.Morphism (kb.toOntology hv) (kb.metaLift.toOntology (metaLift_valid hv)) where
  map := Qid.about
  map_P279 h := sub_rename h
  map_P31 h := inst_rename h

/-- The reduction, as a strict morphism of ontologies back. -/
def metaRet {kb : KB} (hv : kb.valid = true) :
    Ontology.Morphism (kb.metaLift.toOntology (metaLift_valid hv)) (kb.toOntology hv) where
  map := Qid.deMeta
  map_P279 h := by
    obtain ⟨u, v, rfl, rfl, huv⟩ := sub_rename_exists h
    simpa using huv
  map_P31 h := by
    obtain ⟨u, v, rfl, rfl, huv⟩ := inst_rename_exists h
    simpa using huv

@[simp] theorem metaSec_map {kb : KB} (hv : kb.valid = true) : (metaSec hv).map = Qid.about := rfl
@[simp] theorem metaRet_map {kb : KB} (hv : kb.valid = true) : (metaRet hv).map = Qid.deMeta := rfl

/-- **The ontology is a retract of its meta copy.** -/
def metaRetract {kb : KB} (hv : kb.valid = true) :
    Ontology.Retract (kb.toOntology hv) (kb.metaLift.toOntology (metaLift_valid hv)) where
  sec := metaSec hv
  ret := metaRet hv
  ret_sec _ := rfl

/-- **The meta copy is a conservative extension for the class hierarchy.** -/
theorem metaLift_subclassOf_iff {kb : KB} (hv : kb.valid = true) {a b : Qid} :
    (kb.metaLift.toOntology (metaLift_valid hv)).SubclassOf (Qid.about a) (Qid.about b) ↔
      (kb.toOntology hv).SubclassOf a b :=
  (metaRetract hv).subclassOf_iff

/-- **The meta copy is a conservative extension for the instance relation.** -/
theorem metaLift_instanceOf_iff {kb : KB} (hv : kb.valid = true) {a c : Qid} :
    (kb.metaLift.toOntology (metaLift_valid hv)).InstanceOf (Qid.about a) (Qid.about c) ↔
      (kb.toOntology hv).InstanceOf a c :=
  (metaRetract hv).instanceOf_iff

/-- Metaclasshood is reflected by the lift. -/
theorem metaLift_isMetaclass_iff {kb : KB} (hv : kb.valid = true) {c : Qid} :
    (kb.metaLift.toOntology (metaLift_valid hv)).IsMetaclass (Qid.about c) ↔
      (kb.toOntology hv).IsMetaclass c :=
  (metaRetract hv).isMetaclass_iff

/-- **Extensions are pulled back exactly**: the instances of a lifted class are
exactly the lifts of the instances. -/
theorem metaLift_extension {kb : KB} (hv : kb.valid = true) (c : Qid) :
    (metaSec hv).toAlignment.pull
        ((kb.metaLift.toOntology (metaLift_valid hv)).extension (Qid.about c)) =
      (kb.toOntology hv).extension c :=
  (metaRetract hv).preimage_extension c

/-! ## The idempotent and its fixed points -/

theorem metaCore_eq_rename : kb.metaCore = kb.rename (fun q => Qid.about q.deMeta) := by
  rw [metaCore, metaReduce, metaLift, rename_rename]
  rfl

theorem metaCore_idempotent : kb.metaCore.metaCore = kb.metaCore := by
  rw [metaCore_eq_rename, metaCore_eq_rename, rename_rename]
  exact rename_congr kb (fun q => by simp)

theorem metaLift_metaCore : kb.metaLift.metaCore = kb.metaLift := by
  rw [metaCore, metaReduce_metaLift]

/-- A knowledge base written entirely in meta-vocabulary. -/
def allMetaB (kb : KB) : Bool :=
  kb.items.all Qid.isMetaB &&
  kb.levels.all (fun r => r.1.isMetaB) &&
  kb.sub.all (fun r => r.1.isMetaB && r.2.isMetaB) &&
  kb.inst.all (fun r => r.1.isMetaB && r.2.isMetaB) &&
  kb.disj.all (fun r => r.1.isMetaB && r.2.isMetaB)

theorem map_eq_self_iff {α : Type*} {g : α → α} {l : List α} :
    l.map g = l ↔ ∀ x ∈ l, g x = x := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem rename_eq_self_iff (kb : KB) (f : Qid → Qid) :
    kb.rename f = kb ↔
      ((∀ q ∈ kb.items, f q = q) ∧ (∀ r ∈ kb.levels, f r.1 = r.1) ∧
        (∀ r ∈ kb.sub, f r.1 = r.1 ∧ f r.2 = r.2) ∧
        (∀ r ∈ kb.inst, f r.1 = r.1 ∧ f r.2 = r.2) ∧
        (∀ r ∈ kb.disj, f r.1 = r.1 ∧ f r.2 = r.2)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact map_eq_self_iff.1 (congrArg KB.items h)
    · intro r hr
      have := map_eq_self_iff.1 (congrArg KB.levels h) r hr
      exact congrArg Prod.fst this
    · intro r hr
      have := map_eq_self_iff.1 (congrArg KB.sub h) r hr
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · intro r hr
      have := map_eq_self_iff.1 (congrArg KB.inst h) r hr
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · intro r hr
      have := map_eq_self_iff.1 (congrArg KB.disj h) r hr
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨hi, hl, hs, hn, hd⟩
    exact rename_eq_self_of_forall hi hl hs hn hd

/-- **The fixed points of the idempotent are exactly the knowledge bases written
in meta-vocabulary.** -/
theorem metaCore_eq_self_iff : kb.metaCore = kb ↔ kb.allMetaB = true := by
  rw [metaCore_eq_rename, rename_eq_self_iff]
  simp only [allMetaB, Bool.and_eq_true, List.all_eq_true, Qid.about_deMeta_iff,
    ← Qid.isMetaB_iff]
  constructor
  · rintro ⟨hi, hl, hs, hn, hd⟩
    exact ⟨⟨⟨⟨hi, hl⟩, fun r hr => by simp [(hs r hr).1, (hs r hr).2]⟩,
      fun r hr => by simp [(hn r hr).1, (hn r hr).2]⟩,
      fun r hr => by simp [(hd r hr).1, (hd r hr).2]⟩
  · rintro ⟨⟨⟨⟨hi, hl⟩, hs⟩, hn⟩, hd⟩
    exact ⟨hi, hl, fun r hr => by simpa using hs r hr, fun r hr => by simpa using hn r hr,
      fun r hr => by simpa using hd r hr⟩

/-- The lift always lands in meta-vocabulary. -/
@[simp] theorem allMetaB_metaLift : kb.metaLift.allMetaB = true := by
  simp [allMetaB, metaLift, List.all_map, Function.comp_def]

/-- On meta-written knowledge bases the lift and the reduction are mutually
inverse. -/
theorem metaLift_metaReduce_of_allMeta (h : kb.allMetaB = true) :
    kb.metaReduce.metaLift = kb := (metaCore_eq_self_iff kb).2 h

/-- **The Frobenius-like automorphism.** The meta lift is a bijection from all
knowledge bases onto the meta-written ones, with the reduction as its inverse. -/
def metaEquiv : KB ≃ {kb : KB // kb.allMetaB = true} where
  toFun kb := ⟨kb.metaLift, allMetaB_metaLift kb⟩
  invFun p := p.1.metaReduce
  left_inv kb := metaReduce_metaLift kb
  right_inv p := Subtype.ext (metaLift_metaReduce_of_allMeta p.1 p.2)

@[simp] theorem metaEquiv_apply : (metaEquiv kb).1 = kb.metaLift := rfl
@[simp] theorem metaEquiv_symm_apply (p : {kb : KB // kb.allMetaB = true}) :
    metaEquiv.symm p = p.1.metaReduce := rfl

/-- The lift moves every non-empty knowledge base: like a Frobenius
endomorphism, it has no fixed points beyond the degenerate ones. -/
theorem metaLift_ne_self (h : kb.items ≠ []) : kb.metaLift ≠ kb := by
  intro hEq
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  have := map_eq_self_iff.1 (congrArg KB.items hEq) q hq
  exact Qid.about_ne_self q this

/-! ## Frobenius-like algebra of the lift -/

/-- The lift is a homomorphism for the join of knowledge bases. -/
theorem metaLift_merge : (kb.merge kb').metaLift = kb.metaLift.merge kb'.metaLift := by
  simp [merge, metaLift, rename, List.map_append]

/-- The lift is a homomorphism for entailment: the meta copies entail exactly
what the originals entail. -/
theorem metaLift_entails_iff {kb kb' : KB} (hwf : kb.wellFormed = true) :
    kb.metaLift.Entails kb'.metaLift = true ↔ kb.Entails kb' = true := by
  simp [Entails, metaLift, List.all_map, Function.comp_def, List.all_eq_true,
    isSubclassOf_rename_iff Qid.about_injective hwf,
    isInstanceOf_rename_iff Qid.about_injective hwf]

/-- Iterating the lift builds the whole tower of meta levels, and iterating the
reduction climbs back down. -/
theorem metaReduce_iterate_metaLift_iterate (n : ℕ) :
    metaReduce^[n] (metaLift^[n] kb) = kb :=
  Function.LeftInverse.iterate metaReduce_metaLift n kb

theorem valid_metaLift_iterate {kb : KB} (hv : kb.valid = true) (n : ℕ) :
    (metaLift^[n] kb).valid = true := by
  induction n with
  | zero => simpa using hv
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact metaLift_valid ih

/-! ## The meta copy as a pullback -/

section Pullback

variable {kb : KB} (hv : kb.valid = true)

/-- The comparison morphism from the meta copy into the fibre product of the
reduction with the identity. -/
def metaPullbackLift :
    Ontology.Morphism (kb.metaLift.toOntology (metaLift_valid hv))
      (Ontology.pullback (metaRet hv) (Ontology.Morphism.id (kb.toOntology hv))) :=
  Ontology.pullback.lift (metaRet hv) (Ontology.Morphism.id (kb.toOntology hv))
    (Ontology.Morphism.id _) (metaRet hv) (fun _ => rfl)

/-- **The ontology inside the ontology is a pullback.** The comparison morphism
and the first projection of the fibre product are mutually inverse, so the meta
copy *is* the pullback of the reduction along the identity. -/
theorem metaLift_isPullback :
    ((metaPullbackLift hv).comp
        (Ontology.pullback.fst (metaRet hv) (Ontology.Morphism.id (kb.toOntology hv)))).map =
      _root_.id ∧
    ((Ontology.pullback.fst (metaRet hv) (Ontology.Morphism.id (kb.toOntology hv))).comp
        (metaPullbackLift hv)).map = _root_.id := by
  constructor
  · rfl
  · funext p
    exact Subtype.ext (Prod.ext rfl p.2)

end Pullback

/-! ## Agreement with the self-description -/

/-- Every item of the meta copy is an item of the meta-ontology built in
`RequestProject.SelfDescription`: the lift lands inside the self-description. -/
theorem metaLift_items_subset_selfDescription {kb : KB} {q : Qid}
    (hq : q ∈ kb.metaLift.items) : q ∈ kb.selfDescription.items := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (show q ∈ kb.items.map Qid.about from hq)
  exact mem_selfDescription_items_about kb ha

/-- The two constructions agree on metaclass levels. -/
theorem selfDescription_levelOf_eq_metaLift {kb : KB} {x : Qid} (hx : x ∈ kb.items) :
    kb.selfDescription.levelOf (Qid.about x) = kb.metaLift.levelOf (Qid.about x) := by
  rw [selfDescription_levelOf_about kb hx, metaLift_levelOf]

/-! ## A worked fragment

`Q5` *human* is a subclass of `Q215627` *person*, and `Q42` is an instance of
`Q5`. Everything above can be checked on this fragment by computation. -/

section Demo

/-- Shorthand for a Wikidata identifier. -/
private def Q (s : String) : Qid := .wd s

/-- A three-item fragment. -/
def demoKB : KB where
  name := "demo"
  items := [Q "Q5", Q "Q215627", Q "Q42"]
  levels := [(Q "Q5", 1), (Q "Q215627", 1), (Q "Q42", 0)]
  sub := [(Q "Q5", Q "Q215627")]
  inst := [(Q "Q42", Q "Q5")]

theorem demoKB_valid : demoKB.valid = true := by decide

/-- The meta copy of a valid fragment is valid. -/
theorem demoKB_metaLift_valid : demoKB.metaLift.valid = true := by decide

/-- The lift only renames: the meta copy has the meta names as items. -/
theorem demoKB_metaLift_items :
    demoKB.metaLift.items = [.about (Q "Q5"), .about (Q "Q215627"), .about (Q "Q42")] := by
  decide

/-- The reduction undoes the lift, computationally. -/
theorem demoKB_metaReduce_metaLift : demoKB.metaLift.metaReduce = demoKB := by decide

/-- Inheritance is derived in the meta copy exactly as in the original. -/
theorem demoKB_metaLift_inherits :
    demoKB.metaLift.isInstanceOf (.about (Q "Q42")) (.about (Q "Q215627")) = true := by decide

/-- Nothing new is derived: the meta copy says nothing about ground identifiers. -/
theorem demoKB_metaLift_no_ground :
    demoKB.metaLift.isInstanceOf (Q "Q42") (.about (Q "Q5")) = false := by decide

/-- The meta copy is written in meta-vocabulary; the original is not. -/
theorem demoKB_allMeta : demoKB.metaLift.allMetaB = true := by decide

theorem demoKB_not_allMeta : demoKB.allMetaB = false := by decide

/-- The idempotent fixes the meta copy. -/
theorem demoKB_metaCore : demoKB.metaLift.metaCore = demoKB.metaLift := by decide

/-- Two meta levels: the tower of `RequestProject.SelfDescription`, computed. -/
theorem demoKB_two_levels :
    (demoKB.metaLift.metaLift).isInstanceOf
      (.about (.about (Q "Q42"))) (.about (.about (Q "Q215627"))) = true := by decide

#eval demoKB.metaLift.items
#eval demoKB.metaLift.metaReduce == demoKB
#eval (demoKB.merge demoKB).metaLift == demoKB.metaLift.merge demoKB.metaLift

end Demo

end KB
end Wikidata
