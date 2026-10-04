import Synthesis.MillenniumHodgeCycleIsoPushforwardExact
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Hodge max-cut: postcomposition by a scheme isomorphism

The selected ruling regression only needs functoriality of genuine
`AlgebraicCycle.map` when the second morphism is the factor-swap isomorphism.
This owner proves that specialization on the literal residue-degree weighted
Mathlib cycle map.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- Postcomposing a scheme morphism by an isomorphism does not change the
residue-field degree at a source point.  This is the scalar tower fact needed
by genuine cycle pushforward functoriality. -/
theorem residueDegree_postcompose_iso
    (f : X ⟶ Y) (e : Y ≅ Z) (x : X) :
    (f ≫ e.hom).residueDegree x = f.residueDegree x := by
  unfold Scheme.Hom.residueDegree
  letI := ((f ≫ e.hom).residueFieldMap x).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  let i : Z.residueField ((f ≫ e.hom) x) ≃+* Y.residueField (f x) :=
    (asIso (e.hom.residueFieldMap (f x))).commRingCatIsoToRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_
  ext a
  change
    f.residueFieldMap x (e.hom.residueFieldMap (f x) a) =
      (f ≫ e.hom).residueFieldMap x a
  have h := Scheme.residueFieldMap_comp f e.hom x
  exact congrArg (fun k => k a) h.symm

/-- Genuine cycle pushforward commutes with postcomposition by an isomorphism
for the exact residue-degree weighted Mathlib `AlgebraicCycle.map`. -/
theorem actualCyclePushforward_postcompose_iso
    (f : X ⟶ Y) [QuasiCompact f]
    (e : Y ≅ Z)
    (D : AlgebraicCycle X ℤ) :
    actualCyclePushforward e.hom (actualCyclePushforward f D) =
      actualCyclePushforward (f ≫ e.hom) D := by
  ext z
  rw [actualCyclePushforward_iso_apply e (actualCyclePushforward f D) z]
  simp only [actualCyclePushforward, AlgebraicCycle.map,
    Function.locallyFinsupp.map_apply]
  apply finsum_congr
  intro x
  have hfiber :
      f.base x = e.inv.base z ↔ (f ≫ e.hom).base x = z := by
    constructor
    · intro h
      rw [Scheme.comp_base_apply, h]
      exact e.hom_inv_id_apply z
    · intro h
      apply e.hom.base.injective
      rw [e.hom_inv_id_apply]
      simpa [Scheme.comp_base_apply] using h
  by_cases hx : f.base x = e.inv.base z
  · have hcomp : (f ≫ e.hom).base x = z := hfiber.mp hx
    simp [hx, hcomp, AlgebraicCycle.mapCoeff,
      residueDegree_postcompose_iso f e x]
  · have hcomp : (f ≫ e.hom).base x ≠ z := by
      exact fun h => hx (hfiber.mpr h)
    simp [hx, hcomp, AlgebraicCycle.mapCoeff]

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* residue-degree invariance under postcomposition by a genuine scheme iso;
* the full fiber/reindexing equality for the exact Mathlib cycle map;
* therefore `e_* (f_* D) = (f ≫ e)_* D` with genuine multiplicities.

SELECTED RULING CONSEQUENCE:
Once the actual P¹ fundamental cycle and quasicompact ruling instances are in
place, combine this theorem with `p1QRulingOne_swap` and
`p1QRulingTwo_swap` to obtain the exact `P1QRulingCycleExchange` consumed by
the already-written anti-invariant difference theorem.
-/

end

end Synthesis.Millennium.Hodge
