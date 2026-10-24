import Synthesis.RiemannG21CombinedPoleRank

namespace Synthesis

example (z : ℂ) : (z + starRingEnd ℂ z).im = 0 := by
  exact combinedConjugatePole_im_zero z

example (z : ℂ) : z + starRingEnd ℂ z = ((2*z.re : ℝ) : ℂ) := by
  exact combinedConjugatePole_eq_two_re z

example {Sample : Type*} (p : Sample → ℂ) :
    ∃ profile : Sample → ℂ,
      ∀ x, p x + starRingEnd ℂ (p x) = profile x := by
  exact combinedPole_has_singleProfile p

end Synthesis
