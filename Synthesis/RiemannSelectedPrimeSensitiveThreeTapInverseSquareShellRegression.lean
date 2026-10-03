import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance

/-!
# Regression: literal inverse-square shell producer

This file intentionally names the final raw-tail producer rather than any
surrogate density or abstract shell hypothesis.  It is the compile-time guard
for the max-cut tranche that turns the already-paid literal unit-window bounds
into the half-height `O(log t/t)` inverse-square tail used by Route A.
-/

noncomputable section
namespace Synthesis

example : ∃ Ctail : ℝ, ThreeTapInverseSquareTailBound Ctail :=
  exists_threeTapInverseSquareTailBound

end Synthesis
