import Synthesis.HistoryVacuumConformalVariation

namespace Synthesis.HistoryVacuumConformalVariationRegression

example (λ : ℝ) : vacuumAction λ 0 = -λ := vacuumAction_zero λ
example (λ : ℝ) : HasDerivAt (vacuumAction λ) (-4 * λ) 0 := vacuumAction_hasDerivAt_zero λ
example {λ : ℝ} (hλ : 0 < λ) : vacuumTrace λ < 0 := vacuumTrace_neg hλ
example : vacuumTrace (21 / 64 : ℝ) = -21 / 16 := lowBirthmarkVacuumTrace
example : vacuumTrace (3 / 8 : ℝ) = -3 / 2 := highBirthmarkVacuumTrace

end Synthesis.HistoryVacuumConformalVariationRegression
