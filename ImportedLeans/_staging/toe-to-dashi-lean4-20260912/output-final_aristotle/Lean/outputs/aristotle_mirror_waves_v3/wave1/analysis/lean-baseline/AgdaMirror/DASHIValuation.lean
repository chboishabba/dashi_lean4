import Mathlib

/-!
# Lean mirror of `DASHI/Arithmetic/VpDepth.agda` and `NatBoolEquality.agda`
(genuine number theory, fully proved)

Faithful transcription of the DASHI bounded `p`-adic valuation core:

* `DASHI.Arithmetic.NatBoolEquality`: a boolean equality test `natEq` on `ℕ`,
  with `natEq n n = true` and the soundness of a `false` result.
* `DASHI.Arithmetic.VpDepth`: a total, *fuel-bounded* `p`-adic depth valuation
  `vpDepth fuel p n` (treating `0` and `1` as non-prime addresses so the
  recursion cannot stutter), its monotonicity and plateau-stability in the fuel
  parameter, and the key **ultrametric valuation theorem**

  > if `v_p(x) ≠ v_p(y)` then `v_p(x + y) = min (v_p(x), v_p(y))`

  (`vpDepth_add_min_unequal`).

Everything here is genuinely provable and is proved with no `sorry` and no extra
axioms (the Agda originals are likewise postulate-free).
-/

namespace AgdaMirror.DASHIValuation

/-! ## `NatBoolEquality`: boolean equality on `ℕ` -/

/-- Boolean equality test on `ℕ` (Agda `natEq`). -/
def natEq : Nat → Nat → Bool
  | 0,     0     => true
  | 0,     _ + 1 => false
  | _ + 1, 0     => false
  | m + 1, n + 1 => natEq m n

/-- `natEq n n = true`. -/
theorem natEq_self (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => simpa [natEq] using ih

/-- A `false` equality test means the numbers really differ. -/
theorem natEq_false_neq : ∀ x y : Nat, natEq x y = false → x ≠ y := by
  intro x y h
  induction x generalizing y with
  | zero => cases y with
    | zero => simp [natEq] at h
    | succ n => exact fun e => Nat.succ_ne_zero n e.symm
  | succ m ih =>
    cases y with
    | zero => exact Nat.succ_ne_zero m
    | succ n =>
      simp only [natEq] at h
      exact fun e => ih n h (Nat.succ.inj e)

/-! ## `VpDepth`: bounded `p`-adic valuation -/

/-- `minNat` (Agda's explicit minimum). -/
def minNat : Nat → Nat → Nat
  | 0,     _     => 0
  | _ + 1, 0     => 0
  | m + 1, n + 1 => minNat m n + 1

/-- Bounded-depth `p`-adic valuation: `0` and `1` are treated as non-prime so the
recursion cannot stutter on degenerate divisors. Structurally recursive on the
fuel argument. -/
def vpDepth : Nat → Nat → Nat → Nat
  | 0,        _, _ => 0
  | fuel + 1, p, n =>
    match p with
    | 0     => 0
    | 1     => 0
    | q + 2 => if (q + 2) ∣ n then vpDepth fuel (q + 2) (n / (q + 2)) + 1 else 0

/-- `minNat` agrees with `Nat.min`. -/
theorem minNat_eq_min (m n : Nat) : minNat m n = min m n := by
  induction m generalizing n with
  | zero => simp [minNat]
  | succ a ih =>
    cases n with
    | zero => simp [minNat]
    | succ b => simp [minNat, ih, Nat.succ_min_succ]

/-- The valuation is monotone under one extra unit of fuel. -/
theorem vpDepth_monotone_step (fuel p n : Nat) :
    vpDepth fuel p n ≤ vpDepth (fuel + 1) p n := by
  induction fuel generalizing p n with
  | zero => exact Nat.zero_le _
  | succ f ih =>
    match p with
    | 0 => simp [vpDepth]
    | 1 => simp [vpDepth]
    | q + 2 =>
      simp only [vpDepth]
      by_cases h : (q + 2) ∣ n
      · simp only [h, if_true]
        exact Nat.succ_le_succ (ih (q + 2) (n / (q + 2)))
      · simp [h]

/-- Monotonicity of the valuation in arbitrary added fuel. -/
theorem vpDepth_monotone (fuel extra p n : Nat) :
    vpDepth fuel p n ≤ vpDepth (fuel + extra) p n := by
  induction extra with
  | zero => simp
  | succ e ih =>
    calc vpDepth fuel p n ≤ vpDepth (fuel + e) p n := ih
      _ ≤ vpDepth (fuel + e + 1) p n := vpDepth_monotone_step (fuel + e) p n
      _ = vpDepth (fuel + (e + 1)) p n := by ring_nf

/-- Plateau stability: once one extra unit of fuel stops changing the value, the
next unit does not change it either. -/
theorem vpDepth_stable_step (fuel p n : Nat)
    (h : vpDepth fuel p n = vpDepth (fuel + 1) p n) :
    vpDepth (fuel + 1) p n = vpDepth (fuel + 1 + 1) p n := by
  induction fuel generalizing p n with
  | zero =>
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 =>
      simp only [vpDepth] at *
      by_cases hd : (q + 2) ∣ n
      · simp only [hd, if_true] at h ⊢
        exact absurd h.symm (Nat.succ_ne_zero _)
      · simp [hd]
  | succ f ih =>
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 =>
      simp only [vpDepth] at *
      by_cases hd : (q + 2) ∣ n
      · simp only [hd, if_true] at h ⊢
        exact congrArg (· + 1) (ih (q + 2) (n / (q + 2)) (Nat.succ.inj h))
      · simp [hd]

/-- The depth-level ultrametric valuation theorem: if the valuations of `x` and
`y` differ, the valuation of their sum is the minimum of the two. -/
theorem vpDepth_add_min_unequal (fuel p x y : Nat)
    (hneq : vpDepth fuel p x ≠ vpDepth fuel p y) :
    vpDepth fuel p (x + y) = minNat (vpDepth fuel p x) (vpDepth fuel p y) := by
  induction' fuel with fuel fuel_ih generalizing x y p;
  · contradiction;
  · rcases p with ( _ | _ | p ) <;> simp_all +arith +decide [ vpDepth ];
    split_ifs at * <;> simp_all +decide [ Nat.dvd_add_right, Nat.dvd_add_left ];
    · convert congr_arg ( · + 1 ) ( fuel_ih ( p + 2 ) ( x / ( p + 2 ) ) ( y / ( p + 2 ) ) hneq ) using 1;
      rw [ Nat.add_div_of_dvd_left ‹_› ];
    · rfl
    · simp [minNat]

end AgdaMirror.DASHIValuation