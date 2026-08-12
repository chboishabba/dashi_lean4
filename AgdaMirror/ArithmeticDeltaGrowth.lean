import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.DASHIValuation
import AgdaMirror.DeltaGrowth
import AgdaMirror.ArithmeticIntegerEmbedding

/-!
# Lean mirror of the delta-level divisibility frontier of
`DASHI/Arithmetic/DeltaGrowth.agda` (genuine number theory)

The first real arithmetic cap is divisibility: `p ^ δ_p ∣ x + y`
(`deltaPowerDividesSum`).  For the bounded valuation this is constructive: the
local lift `δ_p = γ_p − min(α_p, β_p) ≤ γ_p = v_p(x+y)`, and
`p ^ v_p(x+y) ∣ x+y`.  The nonzero size bound `p ^ δ_p ≤ x + y`
(`deltaPower_le_sum`) follows for nonzero sums.

(The Agda module's `logNat` / `deltaGrowthBound` are *postulates*; following the
honesty discipline they are **not** transcribed as axioms here — the
`DeltaGrowthStructure` record carries the logarithm bound as an honest field.)
-/

namespace AgdaMirror.ArithmeticDeltaGrowth

open AgdaMirror.MonsterOntos
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.DeltaGrowth (vpDepth_power_divides pow_mono_divides)
open SSP

/-- `pow = (· ^ ·)` on `Nat`. -/
def pow (a b : Nat) : Nat := a ^ b

/-- The local lift never exceeds the global valuation. -/
theorem deltaAt_le_gammaAt (p : SSP) (x y : IntCarrier) :
    deltaAt p x y ≤ gammaAt p x y := by
  unfold deltaAt; exact Nat.sub_le _ _

/-- The delta power divides the sum (mirrors `deltaPowerDividesSum`). -/
theorem deltaPowerDividesSum (p : SSP) (x y : IntCarrier) :
    pow (toNat p) (deltaAt p x y) ∣ (x + y) := by
  have h1 : pow (toNat p) (deltaAt p x y) ∣ pow (toNat p) (gammaAt p x y) :=
    pow_dvd_pow _ (deltaAt_le_gammaAt p x y)
  have h2 : pow (toNat p) (gammaAt p x y) ∣ (x + y) := by
    have := vpDepth_power_divides valuationFuel (toNat p) (x + y)
    simpa [pow, gammaAt, vp, add] using this
  exact h1.trans h2

/-- The nonzero size bound (mirrors `deltaPower≤sum`). -/
theorem deltaPower_le_sum (p : SSP) (x y : IntCarrier) (h : 0 < x + y) :
    pow (toNat p) (deltaAt p x y) ≤ x + y :=
  Nat.le_of_dvd h (deltaPowerDividesSum p x y)

/-- The packaged delta-growth surface (logarithm bound kept as an honest
field). -/
structure DeltaGrowthStructure where
  logarithm : Nat → Nat
  power : Nat → Nat → Nat
  powerDivides : ∀ (p : SSP) (x y : IntCarrier),
    power (toNat p) (deltaAt p x y) ∣ x + y
  powerBound : ∀ (p : SSP) (x y : IntCarrier), 0 < x + y →
    power (toNat p) (deltaAt p x y) ≤ x + y
  logBound : ∀ (p : SSP) (x y : IntCarrier), 0 < x + y →
    deltaAt p x y * logarithm (toNat p) ≤ logarithm (x + y)

end AgdaMirror.ArithmeticDeltaGrowth
