import Synthesis.MillenniumHodgeDicksonAffineSaturationExact

/-!
Section 35: original Dickson affine closure saturation is unchanged by
one more multiplication by the ORIGINAL chart denominator.

This is a source-level gluing compatibility fact for the actual
quotient ideal of the punctured affine chart. It is not a replacement
projective closure and does not silently discard components on the
branch divisor: the saturation explicitly removes exactly those
components killed by a power of the original denominator.

It consumes the original saturation equivalence rather than
creating a new generic ideal or changing the source X.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- Membership in the actual punctured-chart closure is equivalent
to membership after multiplying by any chosen ORIGINAL lift D of the
chart denominator. This is the saturation identity needed before
branch gluing and homogenization. -/
theorem actual_affine_saturation_mul_denominator_iff
    (D : FoldPoly)
    (hD : Ideal.Quotient.mk originalFoldIdeal D = chartDenominator)
    (p : FoldPoly) :
    D * p ∈ actualAffineClosureIdeal ↔
      p ∈ actualAffineClosureIdeal := by
  rw [actual_affine_saturation D (D*p) hD,
      actual_affine_saturation D p hD]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n+1, ?_⟩
    convert hn using 1 <;> ring
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    convert originalFoldIdeal.mul_mem_left D hn using 1 <;> ring

/-- The preceding compatibility holds for an ACTUAL original
denominator lift, supplied by the pre-existing quotient
presentation. No generic or independent chart is substituted. -/
theorem actual_affine_saturation_has_original_denominator_glue :
    ∃ D : FoldPoly,
      Ideal.Quotient.mk originalFoldIdeal D = chartDenominator ∧
      ∀ p : FoldPoly,
        (D*p ∈ actualAffineClosureIdeal ↔
          p ∈ actualAffineClosureIdeal) := by
  obtain ⟨D,hD,_⟩ := actual_affine_closure_saturation
  exact ⟨D,hD,fun p =>
    actual_affine_saturation_mul_denominator_iff D hD p⟩

end
end DASHI.Hodge.DicksonCoupled
