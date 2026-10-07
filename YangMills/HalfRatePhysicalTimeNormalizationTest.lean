import Mathlib
import YangMills.HalfRatePhysicalTimeNormalization

namespace RequestProject.YangMills

example (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  energy_ge_log_two_div_step_of_half_rate a E ha hDecay

end RequestProject.YangMills
