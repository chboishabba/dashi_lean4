import Synthesis.MillenniumHodgeDicksonOriginalEvenDeckRootTorsorExact

/-!
Coarse original Hodge geometry: the actual generic six-root fibre,
when the original discriminant product has a nonzero compatible square
root, is a torsor over the original even-sign deck fibre.
All of the input data is the same quadratic Q0 family, not a
synthetic cover or alternate algebraic surface.

This is geometric fibre realization, not a proper projective algebraic
cycle or a proof of its primitive cohomology class.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- Eliminate the arbitrary base root from the statement: over an
algebraically closed characteristic-zero field, the original generic
Q0 fibre has an actual basepoint and a single explicit even-deck
equivalence, with no supplied unrelated source realization. -/
theorem actual_original_generic_Q0_torsor_realized
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (a y : Address → F) (δ : F)
    (hy : ∀ i, y i ≠ 0) (hδ : δ ≠ 0)
    (hprod : δ^2 = ∏ i, deltaField (a i) (y i)) :
    ∃ base : ActualRootFibre a y δ,
      Nonempty (EvenDeck F ≃ ActualRootFibre a y δ) := by
  obtain ⟨base⟩ :=
    actualOriginalRootPuncturedNonempty a y δ hy hδ hprod
  exact ⟨base, ⟨actualOriginalRootEvenDeckEquiv a y δ base hδ⟩⟩

/-- Each target root determines a UNIQUE original even-deck vector
relative to a fixed physical base root. This is the actual inverse
geometry, with no arbitrary sign loss. -/
theorem actual_original_Q0_root_unique_even_deck
    {F : Type*} [Field F] [CharZero F]
    (a y : Address → F) (δ : F)
    (base target : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    ∃! e : EvenDeck F,
      actualOriginalRootEvenDeckEquiv a y δ base hδ e = target := by
  let E := actualOriginalRootEvenDeckEquiv a y δ base hδ
  refine ⟨E.symm target, E.apply_symm_apply target, ?_⟩
  intro e he
  exact E.injective (he.trans (E.apply_symm_apply target).symm)

end
end DASHI.Hodge.DicksonCoupled
