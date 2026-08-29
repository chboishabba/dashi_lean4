import Synthesis.ExponentFibre

/-!
# Synthesis layer 2''''''''': the order numeral and the base

Obligation 1 of the dependency map reads: *nothing links `SSP` to the Monster
group itself; define `M`, prove that the prime divisors of `|M|` are exactly
`toNat '' SSP`, and derive `maskProduct fullMaskSSP = rad |M|`.*  Mathlib has no
Monster group, and this file does **not** construct one.

What it does is discharge the *arithmetic half* of that obligation, so that what
remains is exactly the group-theoretic input and nothing else.  The numeral

```
2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

is recorded in the literature as the order of the Monster; **that reading is
provenance, not a theorem here**, and nothing below depends on it.  Everything
proved is a statement about this natural number and the fifteen-element base:

* `monsterOrderNumeral_value` — the exponent vector over the base evaluates to
  `808017424794512875886459904961710757005754368000000000`;
* `monsterOrderNumeral_primeFactors` — its prime factors are exactly the fifteen
  primes of the base, `toNat '' SSP`;
* `radical_monsterOrderNumeral` — its radical is `maskProduct fullMaskSSP`, the
  full mask product of `Synthesis.MoonshineBase`;
* `repDim_dvd_monsterOrderNumeral` — the supplied numeral `repDim = 196883`
  divides it, since it is the product of three of the base primes.

Remaining for obligation 1: exhibit a group `M` and prove `Nat.card M` equals
this numeral.  That is the only missing step, and no part of the spine assumes it.
-/

namespace Synthesis.MonsterOrder

open AgdaMirror.MonsterOntos (SSP toNat)
open Synthesis.MonsterFibre
open Synthesis.MoonshineBase
open Synthesis.ExponentFibre

/-- The exponent vector over the base recorded in the literature for `|M|`. -/
def monsterOrderExponents : SSP → Nat
  | .p2 => 46 | .p3 => 20 | .p5 => 9 | .p7 => 6 | .p11 => 2 | .p13 => 3
  | .p17 => 1 | .p19 => 1 | .p23 => 1 | .p29 => 1 | .p31 => 1 | .p41 => 1
  | .p47 => 1 | .p59 => 1 | .p71 => 1

/-- The number that exponent vector denotes. -/
def monsterOrderNumeral : Nat := exponentProduct monsterOrderExponents

/-- Every exponent is positive: all fifteen primes really occur. -/
theorem monsterOrderExponents_ne_zero (p : SSP) : monsterOrderExponents p ≠ 0 := by
  cases p <;> decide

theorem monsterOrderNumeral_value :
    monsterOrderNumeral = 808017424794512875886459904961710757005754368000000000 := by
  rw [monsterOrderNumeral, exponentProduct, prod_over_base]
  show (2:Nat)^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17^1 * 19^1 * 23^1 * 29^1 * 31^1
      * 41^1 * 47^1 * 59^1 * 71^1 = _
  norm_num

/-- **The prime factors of the numeral are exactly the fifteen primes of the
base.** -/
theorem monsterOrderNumeral_primeFactors :
    monsterOrderNumeral.primeFactors = Finset.univ.image AgdaMirror.MonsterOntos.toNat :=
  exponentProduct_primeFactors monsterOrderExponents_ne_zero

/-- **Its radical is the full mask product**: the squarefree kernel of the
numeral is the product of the fifteen supersingular primes. -/
theorem radical_monsterOrderNumeral :
    ∏ q ∈ monsterOrderNumeral.primeFactors, q = maskProduct fullMaskSSP := by
  rw [monsterOrderNumeral_primeFactors, maskProduct]
  rw [Finset.prod_image (fun p _ q _ h => toNat_injective h)]
  exact Finset.prod_congr (by ext p; simp [fullMaskSSP]) fun _ _ => rfl

/-- The supplied moonshine numeral divides it, being a product of three of the
base primes. -/
theorem repDim_dvd_monsterOrderNumeral :
    AgdaMirror.Moonshine.repDim ∣ monsterOrderNumeral := by
  rw [← maskProduct_trivector, ← exponentProduct_indicator]
  refine exponentProduct_dvd_of_le fun p => ?_
  cases p <;> decide

end Synthesis.MonsterOrder
