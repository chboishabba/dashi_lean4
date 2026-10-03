import Synthesis.MillenniumHodgeCycleIsoPushforwardExact
import Mathlib.Tactic

/-!
# Hodge max-cut: postcomposition by a scheme isomorphism

The selected ruling regression only needs functoriality of genuine
`AlgebraicCycle.map` when the *second* morphism is the factor-swap isomorphism.
This owner proves the entire locally-finite-sum/reindexing part of that theorem.
The sole remaining scalar obligation is the mathematically canonical fact that
postcomposing a residue-field extension by an isomorphism does not change its
finite degree.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- Genuine cycle pushforward commutes with postcomposition by an isomorphism
once the literal residue degrees for the composite are identified with those
for the original morphism.  No unit-weight replacement is used. -/
theorem actualCyclePushforward_postcompose_iso_of_residueDegree
    (f : X ⟶ Y) [QuasiCompact f]
    (e : Y ≅ Z)
    (D : AlgebraicCycle X ℤ)
    (hdeg : ∀ x : X, (f ≫ e.hom).residueDegree x = f.residueDegree x) :
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
    simp [hx, hcomp, AlgebraicCycle.mapCoeff, hdeg x]
  · have hcomp : (f ≫ e.hom).base x ≠ z := by
      exact fun h => hx (hfiber.mpr h)
    simp [hx, hcomp, AlgebraicCycle.mapCoeff]

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the complete fiber/reindexing part of `map (f ≫ e) = map e ∘ map f` for
  the exact residue-degree weighted Mathlib cycle pushforward when `e` is a
  scheme isomorphism;
* no synthetic cycle map and no altered multiplicity convention.

ONE SCALAR LIBRARY LEMMA REMAINS:

  (f ≫ e.hom).residueDegree x = f.residueDegree x.

This follows from `Scheme.Hom.residueFieldMap_comp`, the fact that the residue
field map of an isomorphism is an isomorphism, and finrank invariance under a
base-field ring equivalence.  Once packaged, the theorem above is unconditional
and can be applied directly to the two actual P¹ rulings and factor swap.
-/

end

end Synthesis.Millennium.Hodge
