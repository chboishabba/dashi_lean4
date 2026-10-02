import Mathlib
import AgdaMirror.IntersectionalNonFactorability

/-!
# Singular-basin reduction obstruction

Lean mirror of the reusable logical core from the Agda singular-basin tranche.

Scientific source motivating the abstraction:
S. Yanchuk, S. Wieczorek, H. Jardón-Kojakhmetov, H. Alkhayuon,
"Singular Basins in Multiscale Systems: Tunneling between Stable States",
Physical Review Letters 137, 147202 (2026), DOI 10.1103/jtkh-9lz5.

The source motivates the problem. The factorisation and obstruction theorems
below are DASHI mathematics and reuse the repository-wide
IntersectionalNonFactorability spine.
-/

namespace AgdaMirror.Dynamics.SingularBasinReduction

namespace NF := AgdaMirror.IntersectionalNonFactorability

/-- Minimal basin-reduction surface. Basin membership is represented as a
predicate so the logical obstruction is independent of a chosen ODE solver,
topology, or convergence formalism. -/
structure BasinReduction (Full Reduced : Type*) where
  project : Full → Reduced
  fullInBasin : Full → Prop
  reducedInBasin : Reduced → Prop

/-- Every full-basin member remains a member after projection. -/
def BasinPreserving
    {Full Reduced : Type*}
    (R : BasinReduction Full Reduced) : Prop :=
  ∀ x, R.fullInBasin x → R.reducedInBasin (R.project x)

/-- Reduced membership reflects back to full membership. -/
def BasinReflecting
    {Full Reduced : Type*}
    (R : BasinReduction Full Reduced) : Prop :=
  ∀ x, R.reducedInBasin (R.project x) → R.fullInBasin x

def BasinExact
    {Full Reduced : Type*}
    (R : BasinReduction Full Reduced) : Prop :=
  BasinPreserving R ∧ BasinReflecting R

/-- Direct singular-funnel style mismatch: a selected state lies in the full
basin while its reduced image is excluded. -/
structure BasinReductionFailure
    {Full Reduced : Type*}
    (R : BasinReduction Full Reduced) where
  witness : Full
  fullMember : R.fullInBasin witness
  reducedExcluded : ¬ R.reducedInBasin (R.project witness)

theorem failure_refutes_preservation
    {Full Reduced : Type*}
    {R : BasinReduction Full Reduced}
    (failure : BasinReductionFailure R) :
    ¬ BasinPreserving R := by
  intro preserving
  exact failure.reducedExcluded
    (preserving failure.witness failure.fullMember)

theorem failure_refutes_exactness
    {Full Reduced : Type*}
    {R : BasinReduction Full Reduced}
    (failure : BasinReductionFailure R) :
    ¬ BasinExact R := by
  intro exactness
  exact failure_refutes_preservation failure exactness.1

/-- Stronger collision witness: same reduced state, different full basin
membership. This is exactly the shape needed by the repository-wide
non-factorability theorem. -/
structure BasinProjectionCollision
    {Full Reduced : Type*}
    (R : BasinReduction Full Reduced) where
  inside : Full
  outside : Full
  sameReducedState : R.project inside = R.project outside
  insideFullBasin : R.fullInBasin inside
  outsideFullBasin : ¬ R.fullInBasin outside

/-- Turn a basin collision into the canonical repository-wide coarse-observer
collision. We use Bool as the outcome so the phenomenon is an ordinary
function and can directly consume the generic non-factorability witness. -/
def collisionAsNonFactorabilityWitness
    {Full Reduced : Type*}
    {R : BasinReduction Full Reduced}
    (collision : BasinProjectionCollision R) :
    NF.NonFactorabilityWitness
      R.project
      (fun x => decide (R.fullInBasin x)) := by
  classical
  refine
    { left := collision.inside
      right := collision.outside
      sameFlatProjection := collision.sameReducedState
      situatedOutcomesDiffer := ?_ }
  simp [collision.insideFullBasin, collision.outsideFullBasin]

/-- Therefore full basin membership cannot be reconstructed from the selected
reduced coordinate alone. -/
theorem basin_collision_refutes_factorisation
    {Full Reduced : Type*}
    {R : BasinReduction Full Reduced}
    (collision : BasinProjectionCollision R) :
    ¬ NF.FactorsThrough
      R.project
      (fun x => decide (R.fullInBasin x)) := by
  classical
  intro factor
  exact NF.witnessRulesOutEveryFlatFactorisation
    (collisionAsNonFactorabilityWitness collision)
    factor

/-- Local attractor correspondence is deliberately weaker than global basin
preservation. A model may carry selected attractor representatives correctly
while still carrying a global basin-reduction failure witness. -/
structure LocalAttractorCorrespondence
    {Full Reduced FullAttractor ReducedAttractor : Type*}
    (R : BasinReduction Full Reduced) where
  fullPoint : FullAttractor → Full
  reducedPoint : ReducedAttractor → Reduced
  mapAttractor : FullAttractor → ReducedAttractor
  selectedPointsAgree :
    ∀ a, R.project (fullPoint a) = reducedPoint (mapAttractor a)

structure LocalCorrespondenceWithGlobalFailure
    {Full Reduced FullAttractor ReducedAttractor : Type*}
    (R : BasinReduction Full Reduced) where
  local :
    LocalAttractorCorrespondence
      (FullAttractor := FullAttractor)
      (ReducedAttractor := ReducedAttractor)
      R
  globalFailure : BasinReductionFailure R

end AgdaMirror.Dynamics.SingularBasinReduction
