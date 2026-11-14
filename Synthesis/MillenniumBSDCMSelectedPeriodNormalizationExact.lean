import Mathlib.Tactic

/-!
# BSD: selected isogeny-class period normalization firewall

For the ORIGINAL selected curve y²=x³-x (LMFDB 32.a3,
Cremona 32a2), the standard real period is twice the
one-component/half-period convention. Its local Tamagawa
factor at 2 is TWO (Kodaira III), not the factor four
from the distinct isogenous 32.a4 curve.

This source PROVES ONLY the arithmetic identity reconciling
the two period conventions. It does NOT assert/prove that
L(E,1) equals either expression or that the actual period
of the original curve has been constructed in Bishop reals.

External provenance:
https://www.lmfdb.org/EllipticCurve/Q/32/a/3
-/

namespace Synthesis.Millennium.BSD

/-- Rank-zero BSD RHS numerical factor for the ORIGINAL CM curve,
using full-period Omega, Tamagawa c2=2, torsion order 4,
regulator 1 and assumed Sha order 1. This is strictly an
algebraic expression, not proof of those input invariants. -/
def cmSelectedRankZeroBSDRatioFullPeriod (omega : ℝ) : ℝ :=
  omega * 2 / 4 ^ 2

/-- Equivalent HALF-period convention. -/
def cmSelectedRankZeroBSDRatioHalfPeriod (omega : ℝ) : ℝ :=
  (omega / 2) / 4

/-- The two exact PERIOD CONVENTIONS agree on their predicted
ratio, without importing an analytic elliptic L-function or
silently changing the Tamagawa number. -/
theorem cmSelectedBSDPeriodNormalization
    (omega : ℝ) :
    cmSelectedRankZeroBSDRatioFullPeriod omega =
      cmSelectedRankZeroBSDRatioHalfPeriod omega := by
  dsimp [cmSelectedRankZeroBSDRatioFullPeriod,
    cmSelectedRankZeroBSDRatioHalfPeriod]
  ring

/-- The relevant scalar is one eighth of the standard full
period, and hence positive if that period is positive.
This does NOT assert L(E,1) equals this value. -/
theorem cmSelectedBSDPredictedRatio_positive
    (omega : ℝ) (h : 0 < omega) :
    0 < cmSelectedRankZeroBSDRatioFullPeriod omega := by
  unfold cmSelectedRankZeroBSDRatioFullPeriod
  positivity

end Synthesis.Millennium.BSD
