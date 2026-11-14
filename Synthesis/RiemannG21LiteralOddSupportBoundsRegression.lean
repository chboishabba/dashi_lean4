import Synthesis.RiemannG21LiteralOddSupportBounds

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {R y : ℝ}
    (hR : 0 <= R) (hy : 0 < y)
    (hw : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (h1 : Integrable (oddHeightWeight R w y) volume)
    (h3 : Integrable (fun x => x^2 * oddHeightWeight R w y x) volume)
    (h5 : Integrable (fun x => x^4 * oddHeightWeight R w y x) volume) :
    oddN3 R w y <= R^2 * oddN1 R w y ∧
    oddN5 R w y <= R^4 * oddN1 R w y := by
  exact literalOddSupportMomentBounds hR hy hw h1 h3 h5

end Synthesis
