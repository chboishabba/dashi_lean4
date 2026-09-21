import Synthesis.RiemannCanonicalTaperRadiusZeroPoleSign
import Synthesis.RiemannFinalLiteralComplementCenteredExact
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-!
# Sign boundary for the centered literal complement

The exact centering theorem produces a nonpositive taper

    h_r = g (cos(r u)-1) <= 0.

That pointwise sign does not by itself determine the sign of the final centered
complement.  The off-ordinate reflection-pair kernel still contains the
oscillatory factor cos(delta u):

    4 h_r(u) cosh(a u) cos(delta u).

This file records a concrete pointwise sign reversal: for a strictly negative
centered taper value and a gap with cosine -1, the paired kernel is positive.

Hence the remaining centered-complement sign theorem genuinely requires
oscillatory/global analysis; it is not a positivity corollary of h_r <= 0.
-/

noncomputable section

open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

theorem reflectionPairWeight_positive_at_pi_gap_of_negative_taper
    {h : ℝ → ℝ} {a u : ℝ}
    (hh : h u < 0) :
    0 < reflectionPairWeight h a Real.pi u := by
  unfold reflectionPairWeight
  rw [Real.cos_pi]
  have hc : 0 < Real.cosh (a * u) := Real.cosh_pos _
  nlinarith

theorem nonpositive_taper_does_not_force_pointwise_nonpositive_pair_kernel :
    ∃ (h : ℝ → ℝ) (a δ u : ℝ),
      (∀ x, h x ≤ 0)
      ∧ h u < 0
      ∧ 0 < reflectionPairWeight h a δ u := by
  refine ⟨fun _ => (-1 : ℝ), 0, Real.pi, 1, ?_, by norm_num, ?_⟩
  · intro x
    norm_num
  · exact reflectionPairWeight_positive_at_pi_gap_of_negative_taper (by norm_num)

end Synthesis
