import Mathlib
import RequestProject.Tesla369

/-!
# The Fibonacci vortex: digital roots of the Fibonacci numbers

The other standard claim of "vortex mathematics" is about the Fibonacci sequence: its digital
roots are said to repeat with period `24`, and the trinity `3, 6, 9` is said to appear at
regular intervals inside that cycle.  Both claims are true, and both have short proofs.

* `fib_add_24_modEq` : `F (n+24) ≡ F n [MOD 9]`, because `F 23 ≡ 1` and `F 24 ≡ 0 (mod 9)`.
* `digitalRoot_fib_period_24` : hence the digital roots of `F 1, F 2, …` have period `24`.
  (The restriction `n > 0` is necessary: `dr (F 0) = 0` but `dr (F 24) = 9`.)
* `digitalRoot_fib_cycle` : the explicit cycle
  `1,1,2,3,5,8,4,3,7,1,8,9,8,8,7,6,4,1,5,6,2,8,1,9`.
* `digitalRoot_fib_period_24_minimal` : `24` is the *minimal* period.
* `three_dvd_fib_iff` : `3 ∣ F n ↔ 4 ∣ n` (because `3 = F 4` and `gcd (F m) (F n) = F (gcd m n)`).
* `digitalRoot_fib_mem_trinity_iff` : so the trinity appears in the Fibonacci digital roots
  exactly at the positions divisible by four — six times in every cycle of twenty-four.
-/

namespace Tesla369

/-- `F 23 = 28657 ≡ 1` and `F 24 = 46368 ≡ 0` modulo `9`, so the Fibonacci sequence is periodic
mod `9` with period `24` (its Pisano period). -/
theorem fib_add_24_modEq (n : ℕ) : Nat.fib (n + 24) ≡ Nat.fib n [MOD 9] := by
  have h := Nat.fib_add 23 n
  have e : 23 + n + 1 = n + 24 := by ring
  rw [e] at h
  have h23 : Nat.fib 23 ≡ 1 [MOD 9] := by decide
  have h24 : Nat.fib 24 ≡ 0 [MOD 9] := by decide
  calc Nat.fib (n + 24) = Nat.fib 23 * Nat.fib n + Nat.fib 24 * Nat.fib (n + 1) := h
    _ ≡ 1 * Nat.fib n + 0 * Nat.fib (n + 1) [MOD 9] :=
        Nat.ModEq.add (h23.mul_right _) (h24.mul_right _)
    _ = Nat.fib n := by ring

/-- **The Fibonacci digital roots repeat with period 24.**  Positivity matters: `dr (F 0) = 0`
while `dr (F 24) = 9`, so the cycle starts at `n = 1`. -/
theorem digitalRoot_fib_period_24 {n : ℕ} (hn : 0 < n) :
    digitalRoot (Nat.fib (n + 24)) = digitalRoot (Nat.fib n) := by
  refine digitalRoot_congr (fib_add_24_modEq n) ?_
  have h1 : 0 < Nat.fib n := Nat.fib_pos.mpr hn
  have h2 : 0 < Nat.fib (n + 24) := Nat.fib_pos.mpr (by omega)
  omega

/-- The explicit twenty-four step Fibonacci cycle of digital roots. -/
theorem digitalRoot_fib_cycle :
    (List.range 24).map (fun n => digitalRoot (Nat.fib (n + 1))) =
      [1, 1, 2, 3, 5, 8, 4, 3, 7, 1, 8, 9, 8, 8, 7, 6, 4, 1, 5, 6, 2, 8, 1, 9] := by
  decide

/-- **Twenty-four is the minimal period.**  Any period of the Fibonacci digital roots (on the
positive indices) is a multiple of `24`. -/
theorem digitalRoot_fib_period_24_minimal {d : ℕ}
    (h : ∀ n : ℕ, 0 < n → digitalRoot (Nat.fib (n + d)) = digitalRoot (Nat.fib n)) : 24 ∣ d := by
  -- reduce `d` modulo 24 using the period
  have hred : ∀ n : ℕ, 0 < n →
      digitalRoot (Nat.fib (n + d % 24)) = digitalRoot (Nat.fib n) := by
    intro n hn
    have key : ∀ q r : ℕ, ∀ m : ℕ, 0 < m →
        digitalRoot (Nat.fib (m + (24 * q + r))) = digitalRoot (Nat.fib (m + r)) := by
      intro q
      induction q with
      | zero => intro r m _; simp
      | succ k ih =>
          intro r m hm
          have e : m + (24 * (k + 1) + r) = (m + (24 * k + r)) + 24 := by ring
          rw [e, digitalRoot_fib_period_24 (by omega), ih r m hm]
    have hd : d = 24 * (d / 24) + d % 24 := by omega
    calc digitalRoot (Nat.fib (n + d % 24))
        = digitalRoot (Nat.fib (n + (24 * (d / 24) + d % 24))) := (key _ _ n hn).symm
      _ = digitalRoot (Nat.fib (n + d)) := by rw [← hd]
      _ = digitalRoot (Nat.fib n) := h n hn
  -- and check that no smaller shift can be a period
  have h1 := hred 1 (by norm_num)
  have h2 := hred 2 (by norm_num)
  have hlt : d % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hzero : d % 24 = 0 := by
    set r := d % 24 with hr
    clear_value r
    interval_cases r <;> revert h1 h2 <;> decide
  omega

/-- **`3 ∣ F n` exactly when `4 ∣ n`**, since `3 = F 4` and `gcd (F m) (F n) = F (gcd m n)`. -/
theorem three_dvd_fib_iff (n : ℕ) : 3 ∣ Nat.fib n ↔ 4 ∣ n := by
  have hg : Nat.gcd 3 (Nat.fib n) = Nat.fib (Nat.gcd 4 n) := by
    rw [Nat.fib_gcd]
    norm_num
  constructor
  · intro hd
    have h3 : Nat.gcd 3 (Nat.fib n) = 3 := Nat.gcd_eq_left hd
    rw [h3] at hg
    have hdvd : Nat.gcd 4 n ∣ 4 := Nat.gcd_dvd_left 4 n
    have hpos : 0 < Nat.gcd 4 n := Nat.gcd_pos_of_pos_left n (by norm_num)
    have hle : Nat.gcd 4 n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : Nat.gcd 4 n = 1 ∨ Nat.gcd 4 n = 2 ∨ Nat.gcd 4 n = 4 := by
      interval_cases h : (Nat.gcd 4 n) <;> omega
    have hg4 : Nat.gcd 4 n = 4 := by
      rcases hcases with h | h | h
      · rw [h] at hg; exact absurd hg (by decide)
      · rw [h] at hg; exact absurd hg (by decide)
      · exact h
    exact hg4 ▸ Nat.gcd_dvd_right 4 n
  · intro hd
    have : Nat.fib 4 ∣ Nat.fib n := Nat.fib_dvd 4 n hd
    simpa using this

/-- **The trinity in the Fibonacci vortex.**  For `n > 0` the digital root of `F n` lies in
`{3, 6, 9}` exactly when `4 ∣ n`: six times in each cycle of twenty-four, at
`n ≡ 4, 8, 12, 16, 20, 0 (mod 24)`. -/
theorem digitalRoot_fib_mem_trinity_iff {n : ℕ} (hn : 0 < n) :
    digitalRoot (Nat.fib n) ∈ trinity ↔ 4 ∣ n := by
  rw [digitalRoot_mem_trinity_iff (Nat.fib_pos.mpr hn), three_dvd_fib_iff]

/-- A closing curiosity, also a consequence of casting out nines: the twenty-four digital roots
of one Fibonacci cycle sum to `117 = 9 · 13`. -/
theorem digitalRoot_fib_cycle_sum :
    ((List.range 24).map (fun n => digitalRoot (Nat.fib (n + 1)))).sum = 117 := by
  decide

end Tesla369
