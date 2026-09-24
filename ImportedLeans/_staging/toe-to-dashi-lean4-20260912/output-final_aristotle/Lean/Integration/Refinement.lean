import Integration.ClopenBalls
import Cuisine.LoomBridge

/-!
# The corpus's resolution-indexed refinement interface, and its instances

`DASHI/Foundations/ConstraintClopenRefinement.agda` declares two interfaces.
The first, `ConstraintSystem`/`FineExtendsCoarse`, is mirrored in
`Cuisine.SupervoxelClopen` and already has four checked instances (cuisine
neutrality, the loom classifiers, the publication classifiers, ternary balls).
The second, `RefinementSystem` — levels, states at each level, a refinement
relation between levels, and a projection along it, with fibres `FibreAt` — is
never instantiated anywhere in the corpus.  This file mirrors it and supplies
the two instances the material actually supports:

* `loomRefinement` — the dialectic loom's three granularities (relation type →
  display bucket → coarse root) as one resolution-indexed system, with the
  projection at each level given by the loom's own classifiers.  The
  factorisation it needs is `Cuisine.LoomBridge.rootOfBucket_bucketFor`.
* `addressRefinement d` — depth-indexed 3/6/9 addresses, projecting by prefix
  truncation.  This is the ball refinement of `Integration.ClopenBalls` in the
  resolution-indexed form.

Both come with the projections proved surjective (`loom_project_surjective`,
`address_project_surjective`), so no level is vacuous.

The negative result at this junction:

* `loom_root_not_product` — **the loom is not a fibre bundle over its roots.**
  There is no type `F` and bijection `LoomRelationType ≃ LoomRelationRoot × F`
  whose first component is the root classifier, because the root classes have
  sizes `3, 2, 3, 1`.  So the loom's coarse/fine pair, unlike the address
  system's, genuinely cannot be presented as "a root plus an independent
  coordinate", and any attempt to give the loom an address-style ternary
  refinement must therefore break at the first level.

Boundary: the loom carriers are finite enumerations of *labels*.  Nothing here
is a claim about evidence, disputes, law, or reconciliation practice.
-/

namespace Integration.Refinement

open Integration.Address
open Integration.TernaryHub
open AgdaMirror.Loom
open Cuisine.LoomBridge (rootOfBucket rootOfBucket_bucketFor)

/-! ## The interface -/

/-- Mirror of `ConstraintClopenRefinement.RefinementSystem`. -/
structure RefinementSystem : Type 1 where
  /-- Resolution levels. -/
  Level : Type
  /-- The states visible at a level. -/
  StateAt : Level → Type
  /-- `Refines fine coarse` witnesses that `fine` is at least as fine. -/
  Refines : Level → Level → Type
  /-- Coarse-graining along a refinement witness. -/
  project : ∀ {fine coarse : Level}, Refines fine coarse → StateAt fine → StateAt coarse

/-- Mirror of `FibreAt`: the fine states above a given coarse state. -/
def FibreAt (R : RefinementSystem) {fine coarse : R.Level}
    (r : R.Refines fine coarse) (c : R.StateAt coarse) : Type :=
  {s : R.StateAt fine // R.project r s = c}

/-- The fibres are disjoint and cover: every fine state lies in exactly one. -/
def fibreOf (R : RefinementSystem) {fine coarse : R.Level} (r : R.Refines fine coarse)
    (s : R.StateAt fine) : FibreAt R r (R.project r s) := ⟨s, rfl⟩

/-! ## Instance 1: the dialectic loom -/

/-- The loom's three granularities. -/
inductive LoomLevel | typeLevel | bucketLevel | rootLevel
  deriving DecidableEq, Repr, Fintype

/-- States at each granularity. -/
def loomStateAt : LoomLevel → Type
  | .typeLevel => LoomRelationType
  | .bucketLevel => LoomBucket
  | .rootLevel => LoomRelationRoot

/-- Which granularity refines which. -/
inductive LoomRefines : LoomLevel → LoomLevel → Type
  | id (l : LoomLevel) : LoomRefines l l
  | typeToBucket : LoomRefines .typeLevel .bucketLevel
  | bucketToRoot : LoomRefines .bucketLevel .rootLevel
  | typeToRoot : LoomRefines .typeLevel .rootLevel

/-- The projections are the loom's own classifiers. -/
def loomProject : ∀ {f c : LoomLevel}, LoomRefines f c → loomStateAt f → loomStateAt c
  | _, _, .id _ => id
  | _, _, .typeToBucket => bucketFor
  | _, _, .bucketToRoot => rootOfBucket
  | _, _, .typeToRoot => relationRootFor

/-- **The loom as a resolution-indexed refinement system.** -/
def loomRefinement : RefinementSystem where
  Level := LoomLevel
  StateAt := loomStateAt
  Refines := LoomRefines
  project := loomProject

/-- The system is coherent: projecting type → bucket → root agrees with
projecting type → root, which is the loom factorisation. -/
theorem loom_project_coherent (t : LoomRelationType) :
    loomProject .bucketToRoot (loomProject .typeToBucket t) = loomProject .typeToRoot t :=
  rootOfBucket_bucketFor t

theorem loom_project_surjective :
    Function.Surjective (loomProject .typeToBucket) ∧
      Function.Surjective (loomProject .bucketToRoot) ∧
      Function.Surjective (loomProject .typeToRoot) := by
  refine ⟨fun b => ?_, fun r => ?_, fun r => ?_⟩
  · cases b
    exacts [⟨.exactSupport, rfl⟩, ⟨.explicitDispute, rfl⟩, ⟨.partialOverlap, rfl⟩,
      ⟨.adjacentEvent, rfl⟩, ⟨.substitution, rfl⟩, ⟨.proceduralNonanswer, rfl⟩,
      ⟨.unrelated, rfl⟩]
  · cases r
    exacts [⟨.supportedBucket, rfl⟩, ⟨.disputedBucket, rfl⟩, ⟨.adjacentEventBucket, rfl⟩,
      ⟨.missingBucket, rfl⟩]
  · cases r
    exacts [⟨.exactSupport, rfl⟩, ⟨.explicitDispute, rfl⟩, ⟨.adjacentEvent, rfl⟩,
      ⟨.unrelated, rfl⟩]

/-! ### The loom is not a bundle over its roots -/

instance : Fintype LoomRelationType :=
  ⟨{.exactSupport, .equivalentSupport, .explicitDispute, .implicitDispute, .partialOverlap,
    .adjacentEvent, .substitution, .proceduralNonanswer, .unrelated},
    fun x => by cases x <;> decide⟩

/-- The four root classes have sizes `3, 2, 3, 1`. -/
theorem loom_root_class_sizes :
    (Finset.univ.filter (fun t : LoomRelationType => relationRootFor t = .supports)).card = 3 ∧
    (Finset.univ.filter (fun t : LoomRelationType => relationRootFor t = .invalidates)).card = 2 ∧
    (Finset.univ.filter
      (fun t : LoomRelationType => relationRootFor t = .nonResolving)).card = 3 ∧
    (Finset.univ.filter (fun t : LoomRelationType => relationRootFor t = .unanswered)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **No product presentation.**  If the loom were `root × fibre`, all four root
classes would have the same size; they do not. -/
theorem loom_root_not_product :
    ¬ ∃ (F : Type) (e : LoomRelationType ≃ LoomRelationRoot × F),
        ∀ t, (e t).1 = relationRootFor t := by
  rintro ⟨F, e, he⟩
  -- `F` embeds in the `invalidates` class, which has two elements …
  have hinj2 : Function.Injective (fun x : F => e.symm (.invalidates, x)) := by
    intro x y hxy
    have := e.symm.injective hxy
    exact (Prod.ext_iff.1 this).2
  have hfin : Finite F := Finite.of_injective _ hinj2
  have hle : Nat.card F ≤ Nat.card {t : LoomRelationType // relationRootFor t = .invalidates} := by
    refine Nat.card_le_card_of_injective
      (fun x : F => (⟨e.symm (.invalidates, x), ?_⟩ :
        {t : LoomRelationType // relationRootFor t = .invalidates})) ?_
    · have := he (e.symm (.invalidates, x))
      simpa using this.symm
    · intro x y hxy
      exact hinj2 (congrArg Subtype.val hxy)
  -- … and the `supports` class, which has three, embeds in `F`.
  have hge : Nat.card {t : LoomRelationType // relationRootFor t = .supports} ≤ Nat.card F := by
    refine Nat.card_le_card_of_injective (fun t => (e t.1).2) ?_
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · rw [he x.1, he y.1, x.2, y.2]
    · exact hxy
  have h2 : Nat.card {t : LoomRelationType // relationRootFor t = .invalidates} = 2 := by
    simp [Nat.card_eq_fintype_card]
    decide
  have h3 : Nat.card {t : LoomRelationType // relationRootFor t = .supports} = 3 := by
    simp [Nat.card_eq_fintype_card]
    decide
  omega

/-! ## Instance 2: depth-indexed addresses -/

/-- Truncation of an address to a shallower depth. -/
def truncate {k j : ℕ} (h : j ≤ k) (s : Address369 k) : Address369 j :=
  fun i => s ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩

/-- **Depth-indexed 3/6/9 addresses as a refinement system.** -/
def addressRefinement : RefinementSystem where
  Level := ℕ
  StateAt := fun k => Address369 k
  Refines := fun fine coarse => PLift (coarse ≤ fine)
  project := fun h s => truncate h.down s

theorem address_project_surjective {k j : ℕ} (h : j ≤ k) :
    Function.Surjective (truncate (k := k) (j := j) h) := by
  intro c
  refine ⟨fun i => if hi : (i : ℕ) < j then c ⟨(i : ℕ), hi⟩ else .d6, ?_⟩
  funext i
  simp only [truncate, dif_pos i.isLt]

/-- Truncation is transitive, so the system is coherent. -/
theorem truncate_trans {k j m : ℕ} (h1 : j ≤ k) (h2 : m ≤ j) (s : Address369 k) :
    truncate h2 (truncate h1 s) = truncate (le_trans h2 h1) s := rfl

/-- One-step fibres of the address system are exactly the digit alphabet: the
uniformity the loom lacks. -/
def addressFibreEquiv (k : ℕ) (c : Address369 k) :
    {s : Address369 (k + 1) // truncate (Nat.le_succ k) s = c} ≃ Digit369 where
  toFun s := s.1 ⟨k, Nat.lt_succ_self k⟩
  invFun x := ⟨fun i => if hi : (i : ℕ) < k then c ⟨(i : ℕ), hi⟩ else x, by
    funext i
    simp only [truncate, dif_pos i.isLt]⟩
  left_inv := by
    rintro ⟨s, hs⟩
    apply Subtype.ext
    funext i
    by_cases hi : (i : ℕ) < k
    · simp only [dif_pos hi]
      have := congrFun hs ⟨(i : ℕ), hi⟩
      simpa [truncate] using this.symm
    · have hik : (i : ℕ) = k := by omega
      simp only [dif_neg hi]
      congr 1
      exact (Fin.ext hik).symm
  right_inv := by
    intro x
    exact dif_neg (lt_irrefl k)

end Integration.Refinement
