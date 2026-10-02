import Synthesis.MillenniumHodgeActualCycleCorrespondenceActionExact
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Hodge max-cut: genuine relative factor-swap automorphism

For a scheme morphism f : X ⟶ S, the relative self-product is the actual
scheme pullback X ×[S] X.  Mathlib already provides its symmetry isomorphism

  pullbackSymmetry f f : X ×[S] X ≅ X ×[S] X.

This is the exact scheme automorphism needed for the factor-swap regression
once X is instantiated by P¹ over the chosen base.

The file packages that automorphism and feeds it into the genuine
`AlgebraicCycle.map` action introduced by the previous max-cut owner.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

section RelativeSwap

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Actual factor-swap automorphism of the relative self-product X ×[S] X. -/
noncomputable def relativeSelfProductSwap :
    pullback f f ≅ pullback f f :=
  pullbackSymmetry f f

/-- The factor swap exchanges the first and second relative projections. -/
@[simp] theorem relativeSelfProductSwap_hom_fst :
    (relativeSelfProductSwap f).hom ≫ pullback.fst f f =
      pullback.snd f f := by
  simpa [relativeSelfProductSwap] using
    (pullbackSymmetry_hom_comp_fst f f)

@[simp] theorem relativeSelfProductSwap_hom_snd :
    (relativeSelfProductSwap f).hom ≫ pullback.snd f f =
      pullback.fst f f := by
  simpa [relativeSelfProductSwap] using
    (pullbackSymmetry_hom_comp_snd f f)

/-- The inverse has the same projection-exchange behavior, as expected for
the factor-swap involution. -/
@[simp] theorem relativeSelfProductSwap_inv_fst :
    (relativeSelfProductSwap f).inv ≫ pullback.fst f f =
      pullback.snd f f := by
  simpa [relativeSelfProductSwap] using
    (pullbackSymmetry_inv_comp_fst f f)

@[simp] theorem relativeSelfProductSwap_inv_snd :
    (relativeSelfProductSwap f).inv ≫ pullback.snd f f =
      pullback.fst f f := by
  simpa [relativeSelfProductSwap] using
    (pullbackSymmetry_inv_comp_snd f f)

/-- Genuine cycle-side action of the relative factor swap. -/
noncomputable def relativeSelfProductSwapCycleAction
    (D : AlgebraicGeometry.AlgebraicCycle (pullback f f) ℤ) :
    AlgebraicGeometry.AlgebraicCycle (pullback f f) ℤ :=
  actualCycleAutomorphismAction (relativeSelfProductSwap f) D

/-!
MAX-CUT STATUS

PAID:
* actual relative product X ×[S] X as a Scheme pullback;
* actual factor-swap Scheme isomorphism on that same product;
* exact exchange of the two structural projections;
* genuine AlgebraicCycle pushforward action of that automorphism.

NEXT SAME-OBJECT WELD:
* instantiate X with the selected P¹ over Spec Q;
* construct a rational point section p : Spec Q ⟶ P¹;
* construct the two ruling divisors as the images/fibres corresponding to
  id × p and p × id on this exact pullback;
* evaluate `relativeSelfProductSwapCycleAction` and prove D₁ ↦ D₂,
  D₂ ↦ D₁ and therefore D₁-D₂ ↦ -(D₁-D₂).

No synthetic ruling lattice is used to assert those equalities here.
-/

end RelativeSwap

end Synthesis.Millennium.Hodge
