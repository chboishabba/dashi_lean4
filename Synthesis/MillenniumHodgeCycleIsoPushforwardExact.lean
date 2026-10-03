import Synthesis.MillenniumHodgeActualCycleCorrespondenceActionExact
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Hodge max-cut: genuine cycle pushforward along a scheme isomorphism

The factor swap used by the P¹×P¹ regression is an actual scheme isomorphism.
For an isomorphism, every residue-field extension appearing in Mathlib's
`AlgebraicCycle.map` has degree one, and each target point has exactly one
source point.  Consequently pushforward is literal reindexing of cycle
coefficients along the inverse point map.

This specializes the generic map-composition problem to the exact geometric
operation needed by the current ruling-swap regression.  It uses Mathlib's
actual residue-degree weighted cycle map; no parallel cycle carrier or
unit-weight substitute is introduced.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

universe u

section IsoResidueDegree

variable {X Y : Scheme.{u}}

/-- A scheme isomorphism induces an isomorphism on residue fields, hence its
literal residue multiplicity in `AlgebraicCycle.map` is one. -/
@[simp] theorem schemeIso_residueDegree_one
    (e : X ≅ Y) (x : X) :
    e.hom.residueDegree x = 1 := by
  letI := (e.hom.residueFieldMap x).hom.toAlgebra
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  change Function.Bijective (e.hom.residueFieldMap x)
  exact ConcreteCategory.bijective_of_isIso _

/-- For the constant-weight convention used by `actualCyclePushforward`, the
Mathlib map coefficient of a scheme isomorphism is exactly one. -/
@[simp] theorem schemeIso_actualCycle_mapCoeff_one
    (e : X ≅ Y) (x : X) :
    AlgebraicCycle.mapCoeff e.hom
      (fun _ : X => ()) (fun _ : Y => ()) x = 1 := by
  simp [AlgebraicCycle.mapCoeff, schemeIso_residueDegree_one]

end IsoResidueDegree

section IsoPushforward

variable {X Y : Scheme.{u}}

/-- Genuine algebraic-cycle pushforward along a scheme isomorphism is pointwise
reindexing by the inverse isomorphism. -/
theorem actualCyclePushforward_iso_apply
    (e : X ≅ Y)
    (D : AlgebraicCycle X ℤ)
    (y : Y) :
    actualCyclePushforward e.hom D y = D (e.inv y) := by
  rw [actualCyclePushforward, AlgebraicCycle.map,
    Function.locallyFinsupp.map_apply]
  rw [finsum_eq_single _ (e.inv y)]
  · simp [schemeIso_actualCycle_mapCoeff_one]
  · intro x hx
    by_cases hxy : e.hom x = y
    · have : x = e.inv y := by
        calc
          x = e.inv (e.hom x) := (e.inv_hom_id_apply x).symm
          _ = e.inv y := by rw [hxy]
      exact (hx this).elim
    · simp [hxy]

/-- Equality of cycles after an isomorphism pushforward can therefore be
proved by equality of coefficients after inverse reindexing. -/
theorem actualCyclePushforward_iso_ext
    (e : X ≅ Y)
    (D E : AlgebraicCycle X ℤ)
    (h : ∀ y : Y, D (e.inv y) = E (e.inv y)) :
    actualCyclePushforward e.hom D = actualCyclePushforward e.hom E := by
  ext y
  simpa [actualCyclePushforward_iso_apply] using h y

/-- Pushforward by an isomorphism is injective on genuine algebraic cycles. -/
theorem actualCyclePushforward_iso_injective
    (e : X ≅ Y) :
    Function.Injective (actualCyclePushforward e.hom :
      AlgebraicCycle X ℤ → AlgebraicCycle Y ℤ) := by
  intro D E hDE
  ext x
  have h := congrArg (fun C : AlgebraicCycle Y ℤ => C (e.hom x)) hDE
  simpa [actualCyclePushforward_iso_apply] using h

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* residue degree of an actual scheme isomorphism is one on the literal Mathlib
  residue-field construction;
* the constant-weight genuine AlgebraicCycle pushforward along an isomorphism
  is literal coefficient reindexing along the inverse point map;
* such pushforward is injective.

IMMEDIATE REGRESSION CONSEQUENCE:
The actual relative factor swap no longer needs the full generic `map_comp`
theorem merely to understand its action on a cycle: its action can be reduced
pointwise to the inverse swap (which is the swap itself).  The next selected
P¹×P¹ owner should instantiate the two ruling cycles and evaluate this formula.

STILL OPEN:
* generic composition of residue-degree weighted `AlgebraicCycle.map`;
* actual P¹_Q Proj/section and the two ruling cycles;
* cycle-class compatibility and difficult primitive Hodge classes.
-/

end IsoPushforward

end Synthesis.Millennium.Hodge
