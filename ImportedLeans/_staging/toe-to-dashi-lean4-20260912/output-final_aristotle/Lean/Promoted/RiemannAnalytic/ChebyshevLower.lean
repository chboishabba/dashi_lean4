import Mathlib

/-!
# A Chebyshev lower bound for `ψ`, and a top-block prime mass bound

Mathlib provides the Chebyshev *upper* bounds `Chebyshev.psi_le` and
`Chebyshev.psi_le_const_mul_self`, but no lower bound.  The literal twisted prime
moment estimates of `RiemannAnalytic.TwistedPrimeMoments` need a two-sided
Chebyshev input, so the lower bound is proved here from the central binomial
coefficient.

Main results.

* `RiemannAnalytic.log_centralBinom_le_psi` :
  `log (centralBinom n) ≤ ψ (2n)`, because every prime power dividing
  `centralBinom n` is at most `2n`, and `∑_{d ∣ m} Λ d = log m`.
* `RiemannAnalytic.psi_lower` : for `x ≥ 2`,
  `x * log 2 - log x - 2 * log 2 ≤ ψ x`  (Chebyshev's lower bound).
* `RiemannAnalytic.psi_block_lower` : for `x ≥ 10 ^ 8`,
  `x / 4 ≤ ψ x - ψ (x / 4)`, i.e. the top block `(x/4, x]` carries a positive
  proportion of the prime mass.  This is the two-sided density input that the
  tilted (twisted) prime measure needs; no such statement follows from an upper
  bound alone.

None of these results uses any axiom beyond `propext`, `Classical.choice`,
`Quot.sound`.
-/

open Finset Real ArithmeticFunction Chebyshev

namespace RiemannAnalytic

/-- Every prime power dividing the central binomial coefficient `binom(2n, n)` is at
most `2n`; since `∑_{d ∣ m} Λ d = log m`, this gives `log (centralBinom n) ≤ ψ (2n)`. -/
theorem log_centralBinom_le_psi {n : ℕ} (hn : 0 < n) :
    Real.log (n.centralBinom) ≤ ψ ((2 * n : ℕ) : ℝ) := by
  classical
  have hC : n.centralBinom ≠ 0 := (Nat.centralBinom_pos n).ne'
  have key : ∀ d ∈ (n.centralBinom).divisors, Λ d ≠ 0 → d ≤ 2 * n := by
    intro d hd hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hdvd : p ^ k ∣ n.centralBinom := (Nat.mem_divisors.mp hd).1
    have hle : k ≤ (n.centralBinom).factorization p :=
      (hp.pow_dvd_iff_le_factorization hC).mp hdvd
    calc p ^ k ≤ p ^ ((n.centralBinom).factorization p) := Nat.pow_le_pow_right hp.pos hle
      _ ≤ 2 * n := by
          rw [Nat.centralBinom_eq_two_mul_choose]
          exact Nat.pow_factorization_choose_le (by omega)
  have h1 : Real.log (n.centralBinom) = ∑ d ∈ (n.centralBinom).divisors, Λ d :=
    vonMangoldt_sum.symm
  rw [h1, psi_eq_sum_Icc]
  have hfloor : ⌊((2 * n : ℕ) : ℝ)⌋₊ = 2 * n := Nat.floor_natCast _
  rw [hfloor]
  have h2 : ∑ d ∈ (n.centralBinom).divisors, Λ d
      = ∑ d ∈ (n.centralBinom).divisors with d ≤ 2 * n, Λ d := by
    rw [Finset.sum_filter_of_ne]
    intro d hd h
    exact key d hd h
  rw [h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => vonMangoldt_nonneg)
  intro d hd
  simp only [Finset.mem_filter] at hd
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hd.2⟩

/-- Chebyshev's lower bound at even integers: `ψ (2n) ≥ 2n log 2 - log (2n)`. -/
theorem psi_two_mul_lower {n : ℕ} (hn : 0 < n) :
    (2 * n : ℝ) * Real.log 2 - Real.log (2 * n) ≤ ψ ((2 * n : ℕ) : ℝ) := by
  have hbin : (4 : ℕ) ^ n ≤ 2 * n * n.centralBinom :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have hCpos : (0 : ℝ) < (n.centralBinom : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  have hlog : Real.log ((4 : ℝ) ^ n) ≤ Real.log ((2 * n : ℝ) * n.centralBinom) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hbin
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [h4] at hlog
  have := log_centralBinom_le_psi hn
  push_cast at this ⊢
  nlinarith [this]

/-- Chebyshev's lower bound: `ψ x ≥ x log 2 - log x - 2 log 2` for `x ≥ 2`. -/
theorem psi_lower {x : ℝ} (hx : 2 ≤ x) :
    x * Real.log 2 - Real.log x - 2 * Real.log 2 ≤ ψ x := by
  set n : ℕ := ⌊x / 2⌋₊ with hn_def
  have hx0 : (0 : ℝ) < x := by linarith
  have hn_pos : 0 < n := by
    have : (1 : ℝ) ≤ x / 2 := by linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hle : ((2 * n : ℕ) : ℝ) ≤ x := by
    push_cast
    have := Nat.floor_le (le_of_lt (by positivity : (0:ℝ) < x / 2))
    rw [← hn_def] at this
    linarith
  have hge : x - 2 ≤ ((2 * n : ℕ) : ℝ) := by
    push_cast
    have := Nat.lt_floor_add_one (x / 2)
    rw [← hn_def] at this
    linarith
  have hmono : ψ ((2 * n : ℕ) : ℝ) ≤ ψ x := psi_mono hle
  have hbase := psi_two_mul_lower hn_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hloglt : Real.log ((2 * n : ℕ) : ℝ) ≤ Real.log x := by
    apply Real.log_le_log _ hle
    have : (0:ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
    exact this
  push_cast at hbase hge hle hloglt hmono
  have hstep : (x - 2) * Real.log 2 ≤ (2 * (n : ℝ)) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hge hlog2.le
  nlinarith [hbase, hmono, hloglt, hstep]

private lemma log_le_four_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * x ^ ((1:ℝ)/4) := by
  calc Real.log x ≤ x ^ ((1:ℝ)/4) / (1/4) := by
        simpa using Real.log_le_rpow_div (le_of_lt hx) (by norm_num : (0:ℝ) < 1/4)
    _ = 4 * x ^ ((1:ℝ)/4) := by ring

/-- The top block `(x/4, x]` carries at least `x/4` of the prime mass, for `x ≥ 10^8`.
This is the two-sided Chebyshev input for the tilted prime measure. -/
theorem psi_block_lower {x : ℝ} (hx : (10:ℝ) ^ 8 ≤ x) : x / 4 ≤ ψ x - ψ (x / 4) := by
  have hx0 : (0:ℝ) < x := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set t : ℝ := x ^ ((1:ℝ)/4) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have ht4 : t ^ (4:ℕ) = x := by
    rw [ht, ← Real.rpow_natCast (x ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hx0.le]; norm_num
  have ht100 : (100:ℝ) ≤ t := by
    have h1 : ((100:ℝ)^(4:ℕ)) ^ ((1:ℝ)/4) = 100 := by
      rw [← Real.rpow_natCast (100:ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (100:ℝ) = ((100:ℝ)^(4:ℕ)) ^ ((1:ℝ)/4) := h1.symm
      _ ≤ t := by
          rw [ht]; exact Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have hsqrt : Real.sqrt (x/4) ≤ t ^ (2:ℕ) / 2 := by
    have h1 : x / 4 = (t ^ (2:ℕ) / 2) ^ 2 := by rw [← ht4]; ring
    rw [h1, Real.sqrt_sq (by positivity)]
  have hlow := psi_lower (by nlinarith : (2:ℝ) ≤ x)
  have hup := Chebyshev.psi_le (x := x/4) (by nlinarith)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
  have hlogx : Real.log x ≤ 4 * t := log_le_four_rpow hx0
  have hlogx4 : Real.log (x/4) ≤ 4 * t :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) hlogx
  have hlogx4pos : 0 ≤ Real.log (x/4) := Real.log_nonneg (by nlinarith)
  have hA : 2 * Real.sqrt (x/4) * Real.log (x/4) ≤ 4 * t^3 := by
    calc 2 * Real.sqrt (x/4) * Real.log (x/4) ≤ 2 * (t^(2:ℕ)/2) * (4*t) := by
          apply mul_le_mul (by linarith) hlogx4 hlogx4pos (by positivity)
      _ = 4 * t^3 := by ring
  have hlog2' := Real.log_two_gt_d9
  rw [hlog4] at hup
  have hB : ψ (x/4) ≤ Real.log 2 / 2 * x + 4 * t^3 := by linarith
  have hC : Real.log 2 * x - 4*t - 2*Real.log 2 ≤ ψ x := by linarith
  have hx4 : x = t^4 := ht4.symm
  have h3 : (10:ℝ)^6 ≤ t^3 := by nlinarith
  have h43 : 100 * t^3 ≤ t^4 := by nlinarith [pow_pos ht0 3]
  nlinarith [hB, hC, hx4, h3, h43, hlog2', ht100]

end RiemannAnalytic
