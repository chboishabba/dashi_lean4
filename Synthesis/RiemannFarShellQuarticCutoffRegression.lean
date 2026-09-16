import Synthesis.RiemannFarShellQuarticCutoff

/-!
Regression surface for the two generic real-analysis atoms behind the quartic
cutoff schedule J(t)=t^4.
-/

namespace Synthesis

example {t : ℝ} (ht : 1 ≤ t) : Real.log (t + 4) ≤ 4 * t :=
  log_add_four_le_four_mul ht

example {t : ℝ} (ht : 0 ≤ t) : Real.sqrt (t ^ 4) = t ^ 2 :=
  sqrt_pow_four ht

end Synthesis
