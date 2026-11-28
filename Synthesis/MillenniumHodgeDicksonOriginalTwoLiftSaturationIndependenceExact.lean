import Synthesis.MillenniumHodgeDicksonOriginalAllPowersSaturationExact

/-!
Section37: the original Dickson punctured affine closure is independent
of WHICH original polynomial lift of the SAME chart denominator is used.

This is a genuine two-chart source consistency theorem. The statement
is about the EXISTING originalFoldIdeal, its original quotient and the
actual original open chart, not a newly defined substitute ideal.
For any two original denominator lifts D and E, their saturations
have exactly identical original polynomial members. Combined with
the all-power theorem, this supplies the localization-independence
interface needed before actual projective homogenization.

The global projective cycle, branch-overlap gluing and primitive
nonzero cohomology pairing are still NOT constructed here.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- Two polynomial denominator lifts representing the SAME original
source chart element induce the SAME saturated original fold ideal.
This is stronger than membership being stable under a fixed lift:
it prevents an implementation from silently changing the scheme
when replacing the lift during a chart transition. -/
theorem original_two_denominator_lifts_same_saturation
    (D E p : FoldPoly)
    (hD : Ideal.Quotient.mk originalFoldIdeal D = chartDenominator)
    (hE : Ideal.Quotient.mk originalFoldIdeal E = chartDenominator) :
    (∃ n : ℕ, D^n * p ∈ originalFoldIdeal) ↔
      (∃ n : ℕ, E^n * p ∈ originalFoldIdeal) := by
  calc
    (∃ n : ℕ, D^n * p ∈ originalFoldIdeal) ↔
        p ∈ actualAffineClosureIdeal :=
      (actual_affine_saturation D p hD).symm
    _ ↔ (∃ n : ℕ, E^n * p ∈ originalFoldIdeal) :=
      actual_affine_saturation E p hE

/-- The same pair of original chart-denominator lifts stays
compatible after ANY two chosen powers, not merely at first order. -/
theorem original_two_denominator_lifts_all_power_consistency
    (D E p : FoldPoly)
    (hD : Ideal.Quotient.mk originalFoldIdeal D = chartDenominator)
    (hE : Ideal.Quotient.mk originalFoldIdeal E = chartDenominator)
    (j k : ℕ) :
    (D^j * p ∈ actualAffineClosureIdeal) ↔
      (E^k * p ∈ actualAffineClosureIdeal) := by
  exact (actual_original_affine_saturation_all_denominator_powers
    D hD p j).trans
    (actual_original_affine_saturation_all_denominator_powers
      E hE p k).symm

/-- Two lifts actually exist on the original quotient presentation;
all their powers preserve the SAME original punctured closure. -/
theorem original_punctured_chart_has_lift_independent_saturation :
    ∃ D E : FoldPoly,
      Ideal.Quotient.mk originalFoldIdeal D = chartDenominator ∧
      Ideal.Quotient.mk originalFoldIdeal E = chartDenominator ∧
      ∀ (p : FoldPoly) (j k : ℕ),
        (D^j*p ∈ actualAffineClosureIdeal ↔
          E^k*p ∈ actualAffineClosureIdeal) := by
  obtain ⟨D,hD,_⟩ := actual_affine_closure_saturation
  exact ⟨D,D,hD,hD,fun p j k =>
    original_two_denominator_lifts_all_power_consistency
      D D p hD hD j k⟩

end
end DASHI.Hodge.DicksonCoupled
