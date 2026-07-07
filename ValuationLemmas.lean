import Mathlib
import AgdaMirror.DASHIValuation

/-!
# Lean mirror of `DASHI/Arithmetic/ValuationLemmas.agda` and `VpAddUnequal.agda`
(genuine number theory)

Faithful transcription of the "active wall" valuation lemmas built on the bounded
`p`-adic depth valuation of `AgdaMirror.DASHIValuation`.  Using the concrete
projections

* `alphaAt fuel p x y = v_p(x)`,
* `betaAt  fuel p x y = v_p(y)`,
* `gammaAt fuel p x y = v_p(x + y)`,
* `deltaAt fuel p x y = gammaAt − min(alphaAt, betaAt)`  (the "wall defect"),

we prove:

* `vp_add_min_unequal`: the local specialisation of the ultrametric valuation
  theorem (`gammaAt = min(alphaAt, betaAt)` when `alphaAt ≠ betaAt`);
* `deltaNonnegative`: the defect is `≥ 0` (trivial in `ℕ`);
* `offWallZero`: off the wall (`alphaAt ≠ betaAt`) the defect collapses to `0`.

All proofs reuse the genuine `vpDepth` theory; no `sorry`, axiom-clean.
-/

namespace AgdaMirror.ValuationLemmas

open AgdaMirror.DASHIValuation (vpDepth minNat natEq natEq_false_neq vpDepth_add_min_unequal)

/-- `v_p(x)`. -/
def alphaAt (fuel p x _y : Nat) : Nat := vpDepth fuel p x
/-- `v_p(y)`. -/
def betaAt (fuel p _x y : Nat) : Nat := vpDepth fuel p y
/-- `v_p(x + y)`. -/
def gammaAt (fuel p x y : Nat) : Nat := vpDepth fuel p (x + y)
/-- The wall defect `gammaAt − min(alphaAt, betaAt)`. -/
def deltaAt (fuel p x y : Nat) : Nat :=
  gammaAt fuel p x y - minNat (alphaAt fuel p x y) (betaAt fuel p x y)

/-- Local valuation theorem: when the valuations differ, the valuation of the sum
is their minimum (mirrors `vp-add-min-unequal`). -/
theorem vp_add_min_unequal (fuel p x y : Nat)
    (wallFalse : natEq (alphaAt fuel p x y) (betaAt fuel p x y) = false) :
    gammaAt fuel p x y = minNat (alphaAt fuel p x y) (betaAt fuel p x y) :=
  vpDepth_add_min_unequal fuel p x y
    (natEq_false_neq _ _ wallFalse)

/-- The wall defect is nonnegative (mirrors `deltaNonnegative`). -/
theorem deltaNonnegative (fuel p x y : Nat) : 0 ≤ deltaAt fuel p x y :=
  Nat.zero_le _

/-- Off the wall, the defect collapses to zero (mirrors `offWallZero`). -/
theorem offWallZero (fuel p x y : Nat)
    (wallFalse : natEq (alphaAt fuel p x y) (betaAt fuel p x y) = false) :
    deltaAt fuel p x y = 0 := by
  simp only [deltaAt, vp_add_min_unequal fuel p x y wallFalse, Nat.sub_self]

end AgdaMirror.ValuationLemmas
