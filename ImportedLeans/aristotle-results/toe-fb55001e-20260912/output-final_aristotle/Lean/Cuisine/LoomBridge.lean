import Cuisine.SupervoxelClopen
import Cuisine.Publication
import AgdaMirror.LoomRelationAlgebra

/-!
# The dialectic-loom lane: classifier refinement, and what does *not* transport

`AgdaMirror.LoomRelationAlgebra` mirrors `LoomRelationAlgebra.agda`: nine
relation types, a four-valued *root* classifier, a seven-valued display
*bucket* classifier, and a promotion state kept deliberately separate from
relation typing.

This module asks two questions about that lane.

**What is shared.**  The loom's two classifiers, and the cuisine publication
lane's risk/decision classifiers, are both instances of the very interface the
supervoxel lane uses (`Cuisine.SupervoxelClopen.ConstraintSystem`,
`FineExtendsCoarse`).  Proved here:

* `rootOfBucket_bucketFor` — **the bucket classifier refines the root
  classifier**: the root is a function of the bucket, so the loom's two
  granularities really are a coarse/fine pair and not two unrelated labellings;
* `loomBucket_refines_root` — that factorisation, in the supervoxel interface;
* `loomRoot_not_atomic`, `publicationDecision_not_atomic` — neither coarse
  classifier is atomic: two distinct fine states share a coarse class.  Together
  with `Cuisine.SupervoxelClopen.cuisineNeutrality_not_atomic` and
  `no_atomic_ball`, this is one definition (`Atomic`) discharged in four
  different lanes;
* `publicationRisk_refines_decision` — the cuisine publication classifier is the
  same shape, and `decision_does_not_refine_risk` shows the refinement is
  strict.

**What does not transport.**  The loom has nine relation types and the corpus
has a nine-element nonary carrier (`TriTruth × TriTruth`,
`Cuisine.NonaryAction`).  That is a coincidence of numerals, and it is refuted
rather than assumed:

* `no_free_order3_root_preserving` — **no fixed-point-free order-three
  permutation of the relation types preserves the root classifier**, because the
  `invalidates` class has two elements.  Any identification of the nine relation
  types with the nonary carrier therefore fails to intertwine the nonary
  rotation with the loom's own classifier, so the shared numeral `9` is not a
  map;
* `loom_root_fibre_sizes` — the arithmetic behind it: the four root classes have
  sizes `3, 2, 3, 1`.

Boundary.  Nothing here concerns evidence, law, publication ethics or food.  The
loom carriers are finite enumerations; `Atomic` is a statement about a
satisfaction relation, nothing more.
-/

namespace Cuisine.LoomBridge

open AgdaMirror.Loom
open Cuisine.SupervoxelClopen

/-! ## The loom classifiers refine each other -/

/-- The root of a display bucket. -/
def rootOfBucket : LoomBucket → LoomRelationRoot
  | .supportedBucket => .supports
  | .partialSupportBucket => .supports
  | .disputedBucket => .invalidates
  | .adjacentEventBucket => .nonResolving
  | .substitutionBucket => .nonResolving
  | .nonSubstantiveResponseBucket => .nonResolving
  | .missingBucket => .unanswered

/-- **The bucket classifier refines the root classifier**: the coarse root is a
function of the display bucket. -/
theorem rootOfBucket_bucketFor (t : LoomRelationType) :
    rootOfBucket (bucketFor t) = relationRootFor t := by
  cases t <;> rfl

/-- Honest converse: the bucket is strictly finer, since `supports` splits into
two buckets. -/
theorem root_does_not_determine_bucket :
    relationRootFor .exactSupport = relationRootFor .partialOverlap ∧
      bucketFor .exactSupport ≠ bucketFor .partialOverlap := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-! ## Both loom classifiers, as a constraint system -/

/-- A loom constraint: a declared bucket, or a declared root. -/
inductive LoomConstraint
  | bucketIs : LoomBucket → LoomConstraint
  | rootIs : LoomRelationRoot → LoomConstraint
  deriving DecidableEq, Repr

/-- The loom classifier system, in the supervoxel interface. -/
def loomSystem : ConstraintSystem where
  State := LoomRelationType
  Constraint := LoomConstraint
  satisfies t
    | .bucketIs b => bucketFor t = b
    | .rootIs r => relationRootFor t = r

/-- **The bucket constraint refines the root constraint**, in the supervoxel
sense: fixing the display bucket forces the root. -/
theorem loomBucket_refines_root (b : LoomBucket) :
    FineExtendsCoarse loomSystem (.rootIs (rootOfBucket b)) (.bucketIs b) := by
  refine ⟨?_⟩
  intro t ht
  show relationRootFor t = rootOfBucket b
  rw [← rootOfBucket_bucketFor t]
  exact congrArg rootOfBucket ht

/-- The converse fails: fixing the root does not force the bucket. -/
theorem loomRoot_does_not_refine_bucket :
    ¬ FineExtendsCoarse loomSystem (.bucketIs .supportedBucket) (.rootIs .supports) := by
  intro h
  have : bucketFor LoomRelationType.partialOverlap = LoomBucket.supportedBucket :=
    h.forgetConstraint (state := .partialOverlap) rfl
  exact absurd this (by decide)

/-- **The loom's coarse classifier is not atomic**: `exactSupport` and
`equivalentSupport` are distinct relation types with the same root. -/
theorem loomRoot_not_atomic : ¬ Atomic loomSystem (.rootIs .supports) := by
  intro hAtomic
  have hEq := hAtomic ⟨LoomRelationType.exactSupport, rfl⟩
    ⟨LoomRelationType.equivalentSupport, rfl⟩
  have hEq' : LoomRelationType.exactSupport = LoomRelationType.equivalentSupport := hEq
  exact absurd hEq' (by decide)

/-! ## The cuisine publication lane has the same shape -/

open Cuisine.Publication

/-- A publication constraint: a declared risk, or a declared decision. -/
inductive PublicationConstraint
  | riskIs : PublicationRisk → PublicationConstraint
  | decisionIs : PublicationDecision → PublicationConstraint
  deriving DecidableEq, Repr

/-- The cuisine publication classifier system, in the same interface. -/
def publicationSystem : ConstraintSystem where
  State := PublicationRisk
  Constraint := PublicationConstraint
  satisfies r
    | .riskIs s => r = s
    | .decisionIs d => publicationDecision r = d

/-- Fixing the risk forces the decision. -/
theorem publicationRisk_refines_decision (r : PublicationRisk) :
    FineExtendsCoarse publicationSystem (.decisionIs (publicationDecision r)) (.riskIs r) := by
  refine ⟨?_⟩
  intro s hs
  show publicationDecision s = publicationDecision r
  exact congrArg publicationDecision hs

/-- The converse fails: `abstain` does not determine the risk. -/
theorem decision_does_not_refine_risk :
    ¬ FineExtendsCoarse publicationSystem (.riskIs .highPublicationRisk)
        (.decisionIs .abstainDecision) := by
  intro h
  have : PublicationRisk.unknownPublicationRisk = PublicationRisk.highPublicationRisk :=
    h.forgetConstraint (state := .unknownPublicationRisk) rfl
  exact absurd this (by decide)

/-- **The cuisine publication decision is not atomic**: high and unknown risk
share the `abstain` decision.  This is the fail-closed convention of the cuisine
lane, and it is the same non-atomicity the supervoxel lane declares. -/
theorem publicationDecision_not_atomic :
    ¬ Atomic publicationSystem (.decisionIs .abstainDecision) := by
  intro hAtomic
  have hEq := hAtomic ⟨PublicationRisk.highPublicationRisk, rfl⟩
    ⟨PublicationRisk.unknownPublicationRisk, rfl⟩
  have hEq' : PublicationRisk.highPublicationRisk = PublicationRisk.unknownPublicationRisk := hEq
  exact absurd hEq' (by decide)

/-! ## The nine relation types are not the nonary carrier -/

/-- The four root classes have sizes `3, 2, 3, 1`. -/
theorem loom_root_fibre_sizes :
    (canonicalRelationPrecedence.filter (fun t => relationRootFor t == .supports)).length = 3 ∧
    (canonicalRelationPrecedence.filter (fun t => relationRootFor t == .invalidates)).length = 2 ∧
    (canonicalRelationPrecedence.filter (fun t => relationRootFor t == .nonResolving)).length = 3 ∧
    (canonicalRelationPrecedence.filter (fun t => relationRootFor t == .unanswered)).length = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **No fixed-point-free order-three permutation of the relation types
preserves the root classifier.**  Consequently no identification of the nine
relation types with the nonary carrier `TriTruth × TriTruth` can carry the free
order-three nonary rotation to a classifier-preserving symmetry: the numeral `9`
is shared, the structure is not. -/
theorem no_free_order3_root_preserving
    (σ : LoomRelationType → LoomRelationType)
    (hfree : ∀ t, σ t ≠ t)
    (h3 : ∀ t, σ (σ (σ t)) = t)
    (hroot : ∀ t, relationRootFor (σ t) = relationRootFor t) : False := by
  have key : ∀ t : LoomRelationType,
      relationRootFor t = LoomRelationRoot.invalidates →
        t = .explicitDispute ∨ t = .implicitDispute := by
    intro t ht
    cases t <;> simp_all [relationRootFor]
  have h1 : σ LoomRelationType.explicitDispute = .implicitDispute := by
    rcases key _ ((hroot LoomRelationType.explicitDispute).trans rfl) with h | h
    · exact absurd h (hfree LoomRelationType.explicitDispute)
    · exact h
  have h2 : σ LoomRelationType.implicitDispute = .explicitDispute := by
    rcases key _ ((hroot LoomRelationType.implicitDispute).trans rfl) with h | h
    · exact h
    · exact absurd h (hfree LoomRelationType.implicitDispute)
  have := h3 LoomRelationType.explicitDispute
  rw [h1, h2, h1] at this
  exact absurd this (by decide)

end Cuisine.LoomBridge
