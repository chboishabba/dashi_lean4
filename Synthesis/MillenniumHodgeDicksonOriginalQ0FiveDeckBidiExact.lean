import Synthesis.MillenniumHodgeDicksonOriginalGenericQ0TorsorRealizationExact
import Synthesis.MillenniumHodgeDicksonGenericProjectionDegreeExact

/-!
Exact five-independent binary-coordinate geometry of the ACTUAL
six-root generic Q0 fibre. Even-deck product-one condition
determines the sixth coordinate; the original field root fibre is
not a sixfold unrestricted binary Cartesian product.

This is a finite generic-fibre equivalence. No global proper Chow
cycle, projective compactification or Hodge primitive-class inference.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

/-- Reverse-solve all original six Q0 roots using FIVE square-one
deck coordinates and the original anchored root basepoint.
`fiveDeckEquiv` pays the product-one constraint rather than
guessing a sixth sign; `actualOriginalRootEvenDeckEquiv` transports
the result to the real Q0 quadratic source. -/
def actualOriginalQ0FiveDeckEquiv
    (a y : Address → F) (δ : F)
    (base : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    (Fin 5 → {e : F // e^2=1}) ≃ ActualRootFibre a y δ :=
  (fiveDeckEquiv (F := F) 2 (by decide)).trans
    (actualOriginalRootEvenDeckEquiv a y δ base hδ)

/-- Every root in the original fibre has one and only one
five-coordinate deck description. -/
theorem actualOriginalQ0FiveDeckBidi
    (a y : Address → F) (δ : F)
    (base target : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    ∃! e : (Fin 5 → {z : F // z^2=1}),
      actualOriginalQ0FiveDeckEquiv a y δ base hδ e = target := by
  let E := actualOriginalQ0FiveDeckEquiv a y δ base hδ
  refine ⟨E.symm target, E.apply_symm_apply target, ?_⟩
  intro e he
  exact E.injective (he.trans (E.apply_symm_apply target).symm)

end
end DASHI.Hodge.DicksonCoupled
