import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.DASHIValuation
import AgdaMirror.ArithmeticIntegerEmbedding

/-!
# Lean mirror of `DASHI/Arithmetic/VpAddUnequal.agda` (genuine, fully proved)

The add-unequal valuation corollary specialised to the tracked `SSP` carrier and
the embedding's local projections `alphaAt / betaAt / gammaAt`: when the two
input valuations disagree (`natEq α β = false`), the valuation of the sum equals
their minimum.  This is the companion to the depth-level
`vpDepth_add_min_unequal`.
-/

namespace AgdaMirror.VpAddUnequal

open AgdaMirror.MonsterOntos
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.DASHIValuation (natEq natEq_false_neq vpDepth_add_min_unequal minNat)
open SSP

/-- The add-unequal valuation corollary over the tracked carrier. -/
theorem vp_add_min_unequal (p : SSP) (x y : IntCarrier)
    (wallFalse : natEq (alphaAt p x y) (betaAt p x y) = false) :
    gammaAt p x y = minNat (alphaAt p x y) (betaAt p x y) := by
  have h := vpDepth_add_min_unequal valuationFuel (toNat p) x y
    (natEq_false_neq _ _ (by simpa [alphaAt, betaAt, vp] using wallFalse))
  simpa [gammaAt, alphaAt, betaAt, vp, add] using h

end AgdaMirror.VpAddUnequal
