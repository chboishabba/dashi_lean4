import Synthesis.MillenniumHodgeDicksonOriginalDenominatorSaturationGlueExact

/-!
Section36 Hodge original affine saturation under ALL powers of its
ACTUAL chart denominator, not only one multiplication.

A projective homogenization/gluing procedure must not reintroduce a
component supported entirely on the deleted puncture. The saturation
owner already proves one-step invariance; this theorem constructs
its entire power-indexed action on the SAME original quotient ideal.
It makes no assertion that the actual projective Chow cycle or
primitive cohomology class has been constructed.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

theorem actual_original_affine_saturation_all_denominator_powers
    (D : FoldPoly)
    (hD : Ideal.Quotient.mk originalFoldIdeal D = chartDenominator)
    (p : FoldPoly) :
    ∀ n : ℕ,
      (D^n * p ∈ actualAffineClosureIdeal ↔
        p ∈ actualAffineClosureIdeal) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hpower : D^(n+1) * p = D * (D^n * p) := by ring
    rw [hpower,
      actual_affine_saturation_mul_denominator_iff D hD,
      ih]

/-- The true source provides an original denominator lift witnessing
invariance at ALL powers, not a fresh chosen divisor at each n. -/
theorem actual_original_affine_saturation_one_lift_all_powers :
    ∃ D : FoldPoly,
      Ideal.Quotient.mk originalFoldIdeal D = chartDenominator ∧
      ∀ (p : FoldPoly) (n : ℕ),
        (D^n*p ∈ actualAffineClosureIdeal ↔
          p ∈ actualAffineClosureIdeal) := by
  obtain ⟨D,hD,_⟩ := actual_affine_closure_saturation
  exact ⟨D,hD,fun p n =>
    actual_original_affine_saturation_all_denominator_powers D hD p n⟩

end
end DASHI.Hodge.DicksonCoupled
