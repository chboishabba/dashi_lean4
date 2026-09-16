import Synthesis.RiemannFarShellQuarticCutoff

/-!
Regression surface for the generic real-analysis atoms and their full far-shell
quartic-cutoff consequence.
-/

namespace Synthesis

example {t : ℝ} (ht : 1 ≤ t) : Real.log (t + 4) ≤ 4 * t :=
  log_add_four_le_four_mul ht

example {t : ℝ} (ht : 0 ≤ t) : Real.sqrt (t ^ 4) = t ^ 2 :=
  sqrt_pow_four ht

example {A t : ℝ} (hA : 0 ≤ A) (ht : 1 ≤ t) :
    18 * A * Real.log (t + 4) / (t ^ 4) +
      72 * A / Real.sqrt (t ^ 4)
      ≤ 144 * A / (t ^ 2) :=
  farShell_quartic_le_inverseSquare hA ht

end Synthesis
