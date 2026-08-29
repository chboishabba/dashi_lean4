import RequestProject.Reflection
import RequestProject.MetaFrobenius
import RequestProject.DisjointUnion
import RequestProject.Concepts
import RequestProject.Kinship

/-!
# The mathematics the formalisation is made of

Wikidata has an article for each of the mathematical notions this development
turns out to use: `pullback` (Q1397439), `retract` (Q2141963), `idempotent
function` (Q44106280), `fixed point` (Q217608), `adjoint functor` (Q357858),
`monoid` (Q208237), `preorder` (Q1425985), `equivalence relation` (Q130998),
`quotient set` (Q3966112), `partition of a set` (Q381060), `strict order`
(Q11077412), `bijection` (Q180907), and so on.  `RequestProject.Vocabulary`
records which declaration of the library each of those articles names; this file
is the other half of that grounding: it says the same thing *in Mathlib's own
vocabulary*, so that the claim "this construction really is a pullback / a
retract / an idempotent / a Galois connection" is a theorem and not a comment.

Nothing here is new mathematics about Wikidata.  Each result restates a
construction that already exists in the library — `Ontology.pullback`,
`Ontology.Retract`, `KB.metaCore`, `KB.metaEquiv`, `Alignment.push`/`pull`,
`KB.Entails`, `Ontology.IsDisjointUnion`, `KB.rename` — as an instance of the
standard notion Wikidata's article describes:

* **monoid** — the structure-preserving self-maps of an ontology form a
  submonoid of `Function.End` (`Ontology.endoSubmonoid`), and the strict
  endomorphisms of `RequestProject.Reflection` are exactly its elements;
* **preorder** — entailment between well-formed knowledge bases is a `Preorder`
  (`KB.WellFormedKB`), and it is genuinely not a partial order;
* **strict order** — proper `subclass of` is an `IsStrictOrder`;
* **Galois connection / adjoint functor** — pushing a set of classes forward
  along an alignment is left adjoint to pulling back (`Alignment.pushPull_gc`),
  and Frobenius reciprocity is the projection formula of that adjunction;
* **idempotent function and fixed point** — the retraction idempotent and the
  meta core are `IsIdempotentElem` in `Function.End`, and their
  `Function.fixedPoints` are computed exactly;
* **injection, surjection, bijection** — the meta lift is injective, and it is a
  bijection onto the meta-written knowledge bases;
* **equivalence relation and quotient set** — merging items is renaming along a
  map, whose kernel `Setoid.ker` is the equivalence relation it imposes, and the
  merged vocabulary is the quotient set;
* **partition of a set** — a disjoint union of classes partitions the extension
  of the whole into the extensions of its parts;
* **well-founded relation** — recorded genealogies are well founded;
* **least fixed point** — the reachable set of the saturation engine is the
  least set containing the source and closed under successors
  (`Reach.reach_isLeast`).
-/

namespace Wikidata

open scoped Function

/-! ## Monoid: the endomorphisms of an ontology -/

namespace Ontology

variable {I J : Type*}

/-- The **submonoid of `Function.End I`** consisting of the maps that preserve
the direct `subclass of` and `instance of` statements of `O` — the structure-
preserving self-maps of the ontology, i.e. the underlying maps of the strict
endomorphisms of `RequestProject.Reflection`. -/
def endoSubmonoid (O : Ontology I) : Submonoid (Function.End I) where
  carrier := {f | (∀ a b, O.P279 a b → O.P279 (f a) (f b)) ∧
                  (∀ a c, O.P31 a c → O.P31 (f a) (f c))}
  mul_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun a b h => hf1 _ _ (hg1 a b h), fun a c h => hf2 _ _ (hg2 a c h)⟩
  one_mem' := ⟨fun _ _ h => h, fun _ _ h => h⟩

@[simp] theorem mem_endoSubmonoid {O : Ontology I} {f : Function.End I} :
    f ∈ O.endoSubmonoid ↔
      (∀ a b, O.P279 a b → O.P279 (f a) (f b)) ∧ (∀ a c, O.P31 a c → O.P31 (f a) (f c)) :=
  Iff.rfl

/-- Every strict endomorphism of an ontology lies in the endomorphism monoid. -/
theorem Morphism.map_mem_endoSubmonoid {O : Ontology I} (F : Morphism O O) :
    (F.map : Function.End I) ∈ O.endoSubmonoid :=
  ⟨fun _ _ h => F.map_P279 h, fun _ _ h => F.map_P31 h⟩

/-- Conversely, every element of the endomorphism monoid is a strict endomorphism. -/
def Morphism.ofEndo {O : Ontology I} (f : O.endoSubmonoid) : Morphism O O where
  map := (f : Function.End I)
  map_P279 h := f.2.1 _ _ h
  map_P31 h := f.2.2 _ _ h

@[simp] theorem Morphism.ofEndo_map {O : Ontology I} (f : O.endoSubmonoid) :
    (Morphism.ofEndo f).map = (f : Function.End I) := rfl

/-- The multiplication of the monoid is composition of morphisms. -/
theorem Morphism.endo_mul {O : Ontology I} (F G : Morphism O O) :
    (⟨G.map, G.map_mem_endoSubmonoid⟩ * ⟨F.map, F.map_mem_endoSubmonoid⟩ : O.endoSubmonoid) =
      ⟨(F.comp G).map, (F.comp G).map_mem_endoSubmonoid⟩ := rfl

/-! ## Strict order: proper `subclass of` -/

/-- Proper `subclass of`: a subclass that is not the class itself. -/
def ProperSubclassOf (O : Ontology I) (a b : I) : Prop := O.SubclassOf a b ∧ a ≠ b

theorem properSubclassOf_irrefl {O : Ontology I} (a : I) : ¬ O.ProperSubclassOf a a :=
  fun h => h.2 rfl

theorem properSubclassOf_trans {O : Ontology I} {a b c : I} (hab : O.ProperSubclassOf a b)
    (hbc : O.ProperSubclassOf b c) : O.ProperSubclassOf a c := by
  refine ⟨subclassOf_trans hab.1 hbc.1, ?_⟩
  rintro rfl
  exact hbc.2 (subclassOf_antisymm hbc.1 hab.1)

/-- **Proper `subclass of` is a strict order** in the sense of Mathlib: it is
irreflexive and transitive. -/
instance properSubclassOf_isStrictOrder (O : Ontology I) :
    IsStrictOrder I O.ProperSubclassOf where
  irrefl := properSubclassOf_irrefl
  trans _ _ _ := properSubclassOf_trans

/-! ## Adjunction: pushforward is left adjoint to pullback -/

variable {O₁ : Ontology I} {O₂ : Ontology J}

/-- **Pushforward is left adjoint to pullback**: `Alignment.push_subset_iff` is a
`GaloisConnection` in the sense of Mathlib, i.e. the adjunction
`f_* A ⊆ B ↔ A ⊆ f^* B` between the powersets of the two vocabularies. -/
theorem Alignment.pushPull_gc (F : Alignment O₁ O₂) :
    GaloisConnection F.push F.pull :=
  fun _ _ => Alignment.push_subset_iff F _ _

/-- The unit of the adjunction. -/
theorem Alignment.le_pull_push (F : Alignment O₁ O₂) (A : Set I) : A ≤ F.pull (F.push A) :=
  (Alignment.pushPull_gc F).le_u_l A

/-- The counit of the adjunction. -/
theorem Alignment.push_pull_le (F : Alignment O₁ O₂) (B : Set J) : F.push (F.pull B) ≤ B :=
  (Alignment.pushPull_gc F).l_u_le B

/-! ## Idempotent functions and their fixed points -/

/-- **The retraction idempotent is an idempotent element** of the monoid
`Function.End` of self-maps of the larger vocabulary. -/
theorem Retract.idem_isIdempotentElem (R : Retract O₁ O₂) :
    IsIdempotentElem (M := Function.End J) R.idem.map :=
  funext fun x => R.idem_idempotent x

/-- **Its fixed points are exactly the embedded items**: the split idempotent of
a retract cuts out the image of the section. -/
theorem Retract.fixedPoints_idem (R : Retract O₁ O₂) :
    Function.fixedPoints R.idem.map = Set.range R.sec.map := by
  ext x
  simpa [Function.IsFixedPt, eq_comm] using R.idem_fixed_iff x

/-! ## Partitions: a disjoint union partitions the extension -/

/-- **A disjoint union is a partition**: the extension of the whole class is the
union of the extensions of its parts. -/
theorem IsDisjointUnion.extension_eq_iUnion {O : Ontology I} {c : I} {Part : I → Prop}
    (h : IsDisjointUnion O c Part) :
    O.extension c = ⋃ p ∈ {p | Part p}, O.extension p := by
  ext a
  simp only [mem_extension, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  exact h.instanceOf_iff

/-- **… and the parts are pairwise disjoint.** -/
theorem IsDisjointUnion.pairwiseDisjoint_extension {O : Ontology I} {c : I} {Part : I → Prop}
    (h : IsDisjointUnion O c Part) :
    {p | Part p}.PairwiseDisjoint O.extension := by
  intro p hp q hq hpq
  refine Set.disjoint_left.2 ?_
  intro a hap haq
  exact hpq (h.eq_of_common_instance hp hq hap haq)

end Ontology

/-! ## Preorder: entailment between knowledge bases -/

/-- A well-formed knowledge base. -/
def WellFormedKB : Type := {kb : KB // kb.wellFormed = true}

namespace WellFormedKB

instance : Coe WellFormedKB KB := ⟨Subtype.val⟩

/-- **Entailment is a preorder.** `kb ≤ kb'` when the second knowledge base
derives everything the first asserts; it is reflexive and transitive, but — see
`not_antisymm` — it is not antisymmetric, so entailment is a preorder and not a
partial order. -/
instance instPreorder : Preorder WellFormedKB where
  le a b := b.1.Entails a.1 = true
  le_refl a := KB.entails_refl a.2
  le_trans a b c hab hbc := KB.entails_trans c.2 b.2 hbc hab

theorem le_iff {a b : WellFormedKB} : a ≤ b ↔ b.1.Entails a.1 = true := Iff.rfl

/-- A two-step chain of classes. -/
def chain : KB where
  name := "chain"
  items := [Qid.wd "Q5", Qid.wd "Q215627", Qid.wd "Q35120"]
  sub := [(Qid.wd "Q5", Qid.wd "Q215627"), (Qid.wd "Q215627", Qid.wd "Q35120")]

/-- The same chain with the derived statement spelled out as well. -/
def chainSaturated : KB :=
  { chain with sub := chain.sub ++ [(Qid.wd "Q5", Qid.wd "Q35120")] }

theorem chain_wellFormed : chain.wellFormed = true := by decide

theorem chainSaturated_wellFormed : chainSaturated.wellFormed = true := by decide

/-- The chain with its statements dropped. -/
def chainBare : KB := { chain with sub := [] }

theorem chainBare_wellFormed : chainBare.wellFormed = true := by decide

/-- **Entailment is not symmetric**, so the preorder is not an equivalence
relation: a knowledge base that asserts nothing is entailed by one that asserts
something, but not conversely. -/
theorem not_symm : ∃ a b : WellFormedKB, a ≤ b ∧ ¬ b ≤ a := by
  refine ⟨⟨chainBare, chainBare_wellFormed⟩, ⟨chain, chain_wellFormed⟩, ?_, ?_⟩
  · show chain.Entails chainBare = true
    decide
  · show ¬ (chainBare.Entails chain = true)
    decide

/-- **Entailment is not antisymmetric**, so the preorder is genuinely not a
partial order: writing a derived `subclass of` statement out explicitly gives a
different knowledge base with exactly the same consequences. -/
theorem not_antisymm : ∃ a b : WellFormedKB, a ≤ b ∧ b ≤ a ∧ a ≠ b := by
  refine ⟨⟨chain, chain_wellFormed⟩, ⟨chainSaturated, chainSaturated_wellFormed⟩, ?_, ?_, ?_⟩
  · show chainSaturated.Entails chain = true
    decide
  · show chain.Entails chainSaturated = true
    decide
  · intro h
    exact absurd (congrArg Subtype.val h) (by decide)

end WellFormedKB

namespace KB

/-! ## Injection, surjection, bijection: the meta lift -/

/-- **The meta lift is a bijection** onto the meta-written knowledge bases. -/
theorem metaEquiv_bijective : Function.Bijective metaEquiv := metaEquiv.bijective

/-- Spelled out — the lift being injective is `KB.metaLift_injective` — it is
also surjective onto the knowledge bases written entirely in meta names. -/
theorem metaLift_surjective_onto_allMeta :
    Function.Surjective (fun kb : KB => (⟨kb.metaLift, allMetaB_metaLift kb⟩ :
      {kb : KB // kb.allMetaB = true})) :=
  metaEquiv.surjective

/-! ## Idempotent function and fixed points: the meta core -/

/-- **The meta core is an idempotent element** of `Function.End KB`. -/
theorem metaCore_isIdempotentElem : IsIdempotentElem (M := Function.End KB) KB.metaCore :=
  funext fun kb => metaCore_idempotent kb

/-- **Its fixed points are exactly the meta-written knowledge bases.** -/
theorem fixedPoints_metaCore :
    Function.fixedPoints KB.metaCore = {kb : KB | kb.allMetaB = true} := by
  ext kb
  exact metaCore_eq_self_iff kb

/-! ## Equivalence relation and quotient set: merging items -/

/-- The **equivalence relation** a renaming imposes on identifiers: two items are
identified by `kb.rename f` exactly when `f` sends them to the same name. This is
the kernel of `f` in the sense of Mathlib. -/
def renameSetoid (f : Qid → Qid) : Setoid Qid := Setoid.ker f

@[simp] theorem renameSetoid_iff {f : Qid → Qid} {a b : Qid} :
    (renameSetoid f).r a b ↔ f a = f b := Iff.rfl

/-- The vocabulary of a renamed knowledge base is the image of the renaming. -/
@[simp] theorem items_rename (kb : KB) (f : Qid → Qid) :
    (kb.rename f).items = kb.items.map f := rfl

/-- Two items of a knowledge base are merged exactly when they are equivalent
modulo the kernel of the merge map. -/
theorem mergeMap_eq_iff (pairs : List (Qid × Qid)) (a b : Qid) :
    KB.mergeMap pairs a = KB.mergeMap pairs b ↔ (renameSetoid (KB.mergeMap pairs)).r a b :=
  Iff.rfl

/-- **The merged vocabulary is the quotient set.** The identifiers after a merge
— the image of the merge map — are in bijection with the quotient of the
identifiers by the equivalence relation the merge imposes. -/
noncomputable def renameQuotientEquiv (f : Qid → Qid) :
    Quotient (renameSetoid f) ≃ Set.range f :=
  Setoid.quotientKerEquivRange f

end KB

/-! ## Well-founded relation: genealogies -/

namespace FKB

/-- **Recorded ancestry is a well-founded relation**, restated with Mathlib's
`WellFoundedRelation`: on a validated genealogy, going up a generation always
terminates. -/
noncomputable def properAncestorWellFoundedRelation (f : FKB) (h : f.fWellFormed = true)
    (hac : f.fAcyclic = true) : WellFoundedRelation Qid where
  rel b a := f.isProperAncestorB b a = true
  wf := f.properAncestor_wf h hac

end FKB

end Wikidata

/-! ## Least fixed point: the reachability engine -/

namespace Reach

variable {Q : Type*} [DecidableEq Q]

/-- **The reachable set is the least fixed point** of the one-step saturation:
it contains the source and is closed under successors, and it is contained in
every set with those two properties. -/
theorem reach_isLeast (succ : Q → Finset Q) {all : Finset Q} (hsucc : ∀ y, succ y ⊆ all)
    {x : Q} (hx : x ∈ all) :
    IsLeast {S : Set Q | x ∈ S ∧ ∀ u ∈ S, ∀ v ∈ succ u, v ∈ S}
      ↑(Reach.reach succ all x) := by
  constructor
  · refine ⟨mem_reach_self succ all x, ?_⟩
    intro u hu v hv
    have hu' : Relation.ReflTransGen (fun a b => b ∈ succ a) x u :=
      (mem_reach_iff succ hsucc hx u).1 hu
    exact (mem_reach_iff succ hsucc hx v).2 (hu'.tail hv)
  · rintro S ⟨hxS, hclosed⟩ b hb
    have hb' : Relation.ReflTransGen (fun a c => c ∈ succ a) x b :=
      (mem_reach_iff succ hsucc hx b).1 hb
    clear hb
    induction hb' with
    | refl => exact hxS
    | tail _ hstep ih => exact hclosed _ ih _ hstep

end Reach
