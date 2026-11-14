import Mathlib
import YangMills.HalfRatePhysicalTimeNormalization

namespace RequestProject.YangMills

example (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  energy_ge_log_two_div_step_of_half_rate a E ha hDecay

example (a E : ℝ) (ha : 0 < a)
    (hSubgap : E < Real.log 2 / a) :
    (1 / 2 : ℝ) < Real.exp (-a * E) :=
  transfer_above_half_of_energy_below_log_two_div_step a E ha hSubgap

end RequestProject.YangMills
