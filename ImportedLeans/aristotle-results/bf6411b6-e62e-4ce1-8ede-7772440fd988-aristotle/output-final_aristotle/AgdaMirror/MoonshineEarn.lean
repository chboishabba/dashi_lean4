-- MoonshineEarn: proof that perf primes (7,11,23) earn moonshine (47,59,71)
-- via FRACTRAN fractions 47/23, 59/7, 71/11 in exactly 3 steps.

namespace MoonshineEarn

-- The three earning fractions
-- f1: 47/23  (clock → ConsCount)
-- f2: 59/7   (cache-misses → SymStrRatio)
-- f3: 71/11  (branch-misses → TotalMod23)

-- FRACTRAN step: if n divisible by den, result is n/den * num
def fstep (n num den : Nat) : Option Nat :=
  if n % den = 0 then some (n / den * num) else none

-- The three-step earning chain
-- Start: 7 × 11 × 23 = 1771
-- Step 1: 47/23 fires → 7 × 11 × 47 = 3619
-- Step 2: 59/7  fires → 11 × 47 × 59 = 30503
-- Step 3: 71/11 fires → 47 × 59 × 71 = 196883

theorem perf_product : 7 * 11 * 23 = 1771 := by native_decide
theorem moonshine_product : 47 * 59 * 71 = 196883 := by native_decide

-- Step 1: apply 47/23 to 1771
theorem step1_fires : 1771 % 23 = 0 := by native_decide
theorem step1_result : 1771 / 23 * 47 = 3619 := by native_decide
theorem step1_factors : 3619 = 7 * 11 * 47 := by native_decide

-- Step 2: apply 59/7 to 3619
theorem step2_fires : 3619 % 7 = 0 := by native_decide
theorem step2_result : 3619 / 7 * 59 = 30503 := by native_decide
theorem step2_factors : 30503 = 11 * 47 * 59 := by native_decide

-- Step 3: apply 71/11 to 30503
theorem step3_fires : 30503 % 11 = 0 := by native_decide
theorem step3_result : 30503 / 11 * 71 = 196883 := by native_decide
theorem step3_factors : 196883 = 47 * 59 * 71 := by native_decide

-- The full chain: 7×11×23 →₃ 47×59×71
theorem earning_chain :
    let s0 := 7 * 11 * 23
    let s1 := s0 / 23 * 47
    let s2 := s1 / 7 * 59
    let s3 := s2 / 11 * 71
    s0 = 1771 ∧ s3 = 196883 := by native_decide

-- The observer: +1 completes the j-invariant
theorem moonshine_observed : 47 * 59 * 71 + 1 = 196884 := by native_decide

-- Observer residue: 196884 mod each earning prime = 1
-- Observer residue mod the source primes (consumed, not clean)
theorem residue_7  : 196884 % 7  = 2 := by native_decide
theorem residue_11 : 196884 % 11 = 6 := by native_decide
theorem residue_23 : 196884 % 23 = 4 := by native_decide

-- But mod the EARNED primes: always 1
theorem residue_47 : 196884 % 47 = 1 := by native_decide
theorem residue_59 : 196884 % 59 = 1 := by native_decide
theorem residue_71 : 196884 % 71 = 1 := by native_decide

-- The earning is a bijection on prime slots:
-- 23 ↦ 47, 7 ↦ 59, 11 ↦ 71
-- Product is preserved: 7×11×23 = 1771, 47×59×71 = 196883
-- Ratio: 196883/1771 = 111.17... (not integer — the fractions CREATE information)
theorem ratio_not_integer : 196883 % 1771 ≠ 0 := by native_decide

-- But the earning is exact: each fraction fires exactly once
theorem each_fires_once :
    1771 % 23 = 0 ∧ 3619 % 7 = 0 ∧ 30503 % 11 = 0 := by
  constructor; native_decide
  constructor; native_decide; native_decide

-- After earning, the fractions become inert (47,59,71 not in any denominator)
theorem f1_inert : 196883 % 23 ≠ 0 := by native_decide
theorem f2_inert : 196883 % 7 ≠ 0 := by native_decide
theorem f3_inert : 196883 % 11 ≠ 0 := by native_decide

-- Full perf state: 2²×3³×7×11×23 earns 2²×3³×47×59×71
theorem full_perf_earn :
    let s0 := 4 * 27 * 7 * 11 * 23
    let s1 := s0 / 23 * 47
    let s2 := s1 / 7 * 59
    let s3 := s2 / 11 * 71
    s3 = 4 * 27 * 47 * 59 * 71 := by native_decide

-- The small primes (2²×3³) pass through unchanged
theorem observer_preserved :
    4 * 27 * 47 * 59 * 71 = 108 * 196883 := by native_decide

end MoonshineEarn

-- ══════════════════════════════════════════════════════════
-- 1729 → 196883: Ramanujan's taxi number earns moonshine
-- ══════════════════════════════════════════════════════════

theorem taxi_is_1729 : 7 * 13 * 19 = 1729 := by native_decide
theorem taxi_step1 : 1729 / 7 * 47 = 11609 := by native_decide
theorem taxi_step2 : 11609 / 13 * 59 = 52687 := by native_decide
theorem taxi_step3 : 52687 / 19 * 71 = 196883 := by native_decide
theorem taxi_div7  : 1729 % 7 = 0 := by native_decide
theorem taxi_div13 : 11609 % 13 = 0 := by native_decide
theorem taxi_div19 : 52687 % 19 = 0 := by native_decide
theorem taxi_earns_moonshine : (((1729 / 7 * 47) / 13 * 59) / 19 * 71) = 196883 := by native_decide

-- Universal earning: the eigenvalue
-- (196883 / 1729 is not exact in ℕ: 196883 = 1729 × 113 + 1106)
theorem earning_quotient : 196883 / 1729 = 113 := by native_decide
theorem earning_remainder : 196883 % 1729 = 1506 := by native_decide
theorem earning_decomp : 1729 * 113 + 1506 = 196883 := by native_decide

-- Taxicab property
theorem taxicab_sum1 : 1 ^ 3 + 12 ^ 3 = 1729 := by native_decide
theorem taxicab_sum2 : 9 ^ 3 + 10 ^ 3 = 1729 := by native_decide
