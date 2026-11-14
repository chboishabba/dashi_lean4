import Synthesis.RiemannG21IntegratedOddRemainder

/-! RED-first regression for the integrated sixth-scaled odd remainder. -/

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {R y r : ℝ}
    (hy : 0 < y)
    (hw : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hN5 : Integrable (fun x => x^4 * oddHeightWeight R w y x) volume) :
    |oddSixScaledRemainder R w y r| <= |r|^5 * oddN5 R w y / 20 := by
  exact oddSixScaledRemainder_le_N5 hy hw hN5

end Synthesis
