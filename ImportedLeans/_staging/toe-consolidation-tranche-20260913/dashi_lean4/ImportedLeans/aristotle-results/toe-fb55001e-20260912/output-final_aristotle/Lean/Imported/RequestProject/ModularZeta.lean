/-
# The zeta function of the modular form

The Riemann zeta function is the Dirichlet series of the constant function `1`,

```
ζ(s) = ∑_{n ≥ 1} n^{-s} = ∏_p (1 - p^{-s})⁻¹ .
```

The *zeta function of the modular form* `Δ = η²⁴ = ∑ τ(n) qⁿ` is the Dirichlet series of its
q-expansion coefficients, in the Deligne-normalised (analytic) form

```
L(Δ, s) = ∑_{n ≥ 1} (τ(n) / n^{11/2}) n^{-s} = ∏_p (1 - (τ(p)/p^{11/2}) p^{-s} + p^{-2s})⁻¹ .
```

Only the partial sums `∑_{n ≤ N}` are used here, because the project's τ is a *computed*
q-expansion coefficient and the arithmetic facts about it (Deligne's bound, the Hecke
recursion) are established over the displayed range `n ≤ 256`.  Over that range everything the
picture `visualization/modular-zeta.svg` shows is proved:

* `ModularZeta.abs_deltaLPartial_le_divisorPartial` — Deligne's bound makes the modular
  Dirichlet series dominated termwise by the divisor series `∑ d(n) n^{-s}`;
* `ModularZeta.divisorPartial_le_zetaPartial_sq` — the divisor series is at most the square of
  the zeta series, so `|L_N(Δ, s)| ≤ ζ(s)²` (`ModularZeta.abs_deltaLPartial_le_zeta_sq`),
  the *modular zeta lies inside the square of the Riemann zeta*;
* `ModularZeta.abs_deltaLPartial_sub_one_le` — its distance from `1` is controlled by
  `ζ_N(s)² - 1`, which is why the plotted curve falls onto `1` so quickly;
* `ModularZeta.localPartial_mul_modularLocalInv` — the Hecke recursion is exactly the statement
  that the local Dirichlet polynomial of the fiber of `p` is the expansion of the *quadratic*
  local factor `(1 - y_p x + x²)⁻¹`, in contrast with zeta's *linear* factor `(1 - x)⁻¹`;
* `ModularZeta.modularLocalFactor_le_eulerFactor_sq` /
  `ModularZeta.eulerFactor_sq_inv_le_modularLocalFactor` — the local factor of the modular zeta
  is squeezed between `(1 + p^{-s})⁻²` and the square of zeta's local factor.
-/
import RequestProject.FiberSums
import RequestProject.MonsterZeta

namespace ModularZeta

open Finset FiberSums PrimeFibers RamanujanTau

set_option autoImplicit false
set_option maxRecDepth 40000

variable {s : ℝ} {N : ℕ}

/-! ## The three Dirichlet series, truncated at `N` -/

/-- The partial sum of the zeta function, `∑_{n ≤ N} n^{-s}`. -/
noncomputable def zetaPartial (N : ℕ) (s : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s)

/-- The partial sum of the zeta function of the modular form `Δ`, in Deligne-normalised form:
`L_N(Δ, s) = ∑_{n ≤ N} (τ(n)/n^{11/2}) n^{-s}`. -/
noncomputable def deltaLPartial (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, normTau n * (n : ℝ) ^ (-s)

/-- The partial sum of the divisor series `∑_{n ≤ N} d(n) n^{-s}`, the Deligne envelope of the
modular series. -/
noncomputable def divisorPartial (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s)

theorem zetaPartial_nonneg (N : ℕ) (s : ℝ) : 0 ≤ zetaPartial N s :=
  Finset.sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- The zeta partial sums stay below `ζ(s)` for `s > 1`. -/
theorem zetaPartial_le_zetaR (hs : 1 < s) (N : ℕ) : zetaPartial N s ≤ Sporadic.zetaR s :=
  Sporadic.sum_le_zetaR hs _

/-! ## Deligne's bound: the modular series inside the divisor series -/

/-- **Termwise domination.** On the range where Deligne's bound is available, the modular
Dirichlet series is dominated by the divisor series. -/
theorem abs_deltaLPartial_le_divisorPartial {N : ℕ} (hN : N ≤ 256) (s : ℝ) :
    |deltaLPartial N s| ≤ divisorPartial N s := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hn2 : n ≤ 256 := le_trans (Finset.mem_Icc.1 hn).2 hN
  have hx : (0 : ℝ) ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [abs_mul, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_right (abs_normTau_le_divisors hn1 hn2) hx

/-! ## The divisor series inside the square of the zeta series -/

/-- The square of a zeta partial sum, expanded over pairs. -/
theorem zetaPartial_sq (N : ℕ) (s : ℝ) :
    zetaPartial N s ^ 2 =
      ∑ q ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s) := by
  rw [zetaPartial, sq, Finset.sum_mul_sum, Finset.sum_product]

/-- **The divisor series is at most the square of the zeta series.** -/
theorem divisorPartial_le_zetaPartial_sq (N : ℕ) (s : ℝ) :
    divisorPartial N s ≤ zetaPartial N s ^ 2 := by
  classical
  have hkey : divisorPartial N s
      = ∑ q ∈ (Finset.Icc 1 N).biUnion (fun n => n.divisorsAntidiagonal),
          (q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s) := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
      have hterm : ∀ q ∈ n.divisorsAntidiagonal,
          (q.1 : ℝ) ^ (-s) * (q.2 : ℝ) ^ (-s) = (n : ℝ) ^ (-s) := by
        rintro ⟨a, b⟩ hq
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.1 hq
        have ha : a ≠ 0 := by rintro rfl; simp at hab; omega
        have hb : b ≠ 0 := by rintro rfl; simp at hab; omega
        rw [← Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b), ← Nat.cast_mul, hab]
      have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
        rw [← Nat.map_div_right_divisors, Finset.card_map]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]
    · intro a _ b _ hab
      simp only [Finset.disjoint_left]
      rintro ⟨u, v⟩ hu hv
      have h1 := (Nat.mem_divisorsAntidiagonal.1 hu).1
      have h2 := (Nat.mem_divisorsAntidiagonal.1 hv).1
      exact hab (by rw [← h1, ← h2])
  rw [hkey, zetaPartial_sq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by positivity)
  intro q hq
  simp only [Finset.mem_biUnion] at hq
  obtain ⟨n, hn, hqn⟩ := hq
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hqn
  have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
  have h1 : q.1 ≠ 0 := by rintro h; exact hn0 (by rw [← hprod, h, zero_mul])
  have h2 : q.2 ≠ 0 := by rintro h; exact hn0 (by rw [← hprod, h, mul_zero])
  have hle1 : q.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨q.2, hprod.symm⟩
  have hle2 : q.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨q.1, by rw [← hprod]; ring⟩
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega

/-- **The modular zeta lies inside the square of the Riemann zeta.** For `s > 1`, every partial
sum of the Dirichlet series of `Δ` (Deligne-normalised) is bounded in absolute value by
`ζ(s)²`. -/
theorem abs_deltaLPartial_le_zeta_sq (hs : 1 < s) {N : ℕ} (hN : N ≤ 256) :
    |deltaLPartial N s| ≤ Sporadic.zetaR s ^ 2 := by
  refine le_trans (abs_deltaLPartial_le_divisorPartial (N := N) hN s) ?_
  refine le_trans (divisorPartial_le_zetaPartial_sq N s) ?_
  have h0 := zetaPartial_nonneg N s
  have h := zetaPartial_le_zetaR hs N
  nlinarith

/-- The Deligne envelope of the modular series is itself at most `ζ(s)²`. -/
theorem divisorPartial_le_zeta_sq (hs : 1 < s) (N : ℕ) :
    divisorPartial N s ≤ Sporadic.zetaR s ^ 2 := by
  refine le_trans (divisorPartial_le_zetaPartial_sq N s) ?_
  have h0 := zetaPartial_nonneg N s
  have h := zetaPartial_le_zetaR hs N
  nlinarith

/-! ## The leading term -/

theorem normTau_one : normTau 1 = 1 := by
  rw [normTau, tau_one]
  norm_num

/-- The `n = 1` term of the modular series is `1`. -/
theorem deltaLPartial_split {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    deltaLPartial N s = 1 + ∑ n ∈ Finset.Icc 2 N, normTau n * (n : ℝ) ^ (-s) := by
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [deltaLPartial, hsplit, Finset.sum_insert (by simp)]
  norm_num [normTau_one]

theorem divisorPartial_split {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    divisorPartial N s = 1 + ∑ n ∈ Finset.Icc 2 N, (n.divisors.card : ℝ) * (n : ℝ) ^ (-s) := by
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [divisorPartial, hsplit, Finset.sum_insert (by simp)]
  norm_num

/-- **Why the plotted curve collapses onto `1`.** The modular zeta differs from `1` by at most
`ζ_N(s)² - 1`, which tends to `0` as `s` grows. -/
theorem abs_deltaLPartial_sub_one_le {N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 256) (s : ℝ) :
    |deltaLPartial N s - 1| ≤ zetaPartial N s ^ 2 - 1 := by
  have hstep : |deltaLPartial N s - 1| ≤ divisorPartial N s - 1 := by
    rw [deltaLPartial_split hN, divisorPartial_split hN]
    simp only [add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn1 : 1 ≤ n := le_trans (by norm_num) (Finset.mem_Icc.1 hn).1
    have hn2 : n ≤ 256 := le_trans (Finset.mem_Icc.1 hn).2 hN'
    have hx : (0 : ℝ) ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right (abs_normTau_le_divisors hn1 hn2) hx
  have := divisorPartial_le_zetaPartial_sq N s
  linarith

/-! ## The local factors: quadratic for the modular form, linear for zeta -/

/-- The reciprocal of the local factor of the modular zeta at `p`:
`1 - (τ(p)/p^{11/2}) p^{-s} + p^{-2s}`.  Zeta's is the linear `1 - p^{-s}`. -/
noncomputable def modularLocalInv (p : ℕ) (s : ℝ) : ℝ :=
  1 - normTau p * (p : ℝ) ^ (-s) + ((p : ℝ) ^ (-s)) ^ 2

/-- The local factor of the modular zeta at `p`. -/
noncomputable def modularLocalFactor (p : ℕ) (s : ℝ) : ℝ := (modularLocalInv p s)⁻¹

/-- The local Dirichlet polynomial of the fiber of `p`, truncated at `p^K`:
`∑_{k ≤ K} (τ(p^k)/p^{11k/2}) p^{-ks}`. -/
noncomputable def localPartial (p K : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), normTau (p ^ k) * ((p : ℝ) ^ (-s)) ^ k

/-- **The Hecke recursion is the quadratic local factor.** Multiplying the local Dirichlet
polynomial of the fiber of `p` by `1 - y_p x + x²` (`x = p^{-s}`) leaves only `1` and the two
boundary terms — the exact analogue, for the modular form, of the geometric series
`(1 - x) ∑_{k ≤ K} x^k = 1 - x^{K+1}` behind zeta's Euler factor. -/
theorem localPartial_mul_modularLocalInv {p : ℕ} (hp : p ∈ first20Primes) (s : ℝ) :
    ∀ K : ℕ, p ^ (K + 1) ≤ 256 →
      modularLocalInv p s * localPartial p K s
        = 1 - normTau (p ^ (K + 1)) * ((p : ℝ) ^ (-s)) ^ (K + 1)
            + normTau (p ^ K) * ((p : ℝ) ^ (-s)) ^ (K + 2) := by
  intro K
  induction K with
  | zero =>
      intro _
      have h0 : localPartial p 0 s = 1 := by simp [localPartial, normTau_one]
      rw [h0, modularLocalInv]
      norm_num [normTau_one]
  | succ K ih =>
      intro hK
      have hprev : p ^ (K + 1) ≤ 256 := by
        refine le_trans (Nat.pow_le_pow_right ?_ (by omega)) hK
        exact (prime_of_mem_first20Primes hp).one_lt.le
      have hrec : normTau (p ^ (K + 2)) = normTau p * normTau (p ^ (K + 1)) - normTau (p ^ K) :=
        normTau_hecke hp (by simpa using hK)
      have hsplit : localPartial p (K + 1) s
          = localPartial p K s + normTau (p ^ (K + 1)) * ((p : ℝ) ^ (-s)) ^ (K + 1) := by
        rw [localPartial, localPartial, Finset.sum_range_succ]
      rw [hsplit, mul_add, ih hprev, modularLocalInv]
      have hK2 : K + 1 + 1 = K + 2 := rfl
      rw [hK2, hrec]
      ring

/-! ## The modular local factor against zeta's -/

theorem rpow_neg_mem_Ioo {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) : (p : ℝ) ^ (-s) ∈ Set.Ioo 0 1 :=
  Sporadic.rpow_neg_mem_Ioo hp hs

/-- Deligne's bound at a prime: `|τ(p)/p^{11/2}| ≤ 2`. -/
theorem abs_normTau_prime_le_two {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256) : |normTau p| ≤ 2 := by
  have h := abs_normTau_pow_le (p := p) (k := 1) hp (by simpa using hp')
  simp only [pow_one, Nat.cast_one] at h
  linarith

/-- The local factor of the modular zeta is squeezed between the two Rankin factors: with
`x = p^{-s}`, `(1 - x)² ≤ 1 - y_p x + x² ≤ (1 + x)²`. -/
theorem modularLocalInv_bounds {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256) (hs : 0 < s) :
    (1 - (p : ℝ) ^ (-s)) ^ 2 ≤ modularLocalInv p s ∧
      modularLocalInv p s ≤ (1 + (p : ℝ) ^ (-s)) ^ 2 := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp.two_le hs
  have hy := abs_normTau_prime_le_two hp hp'
  rw [abs_le] at hy
  constructor
  · rw [modularLocalInv]
    nlinarith [hy.2]
  · rw [modularLocalInv]
    nlinarith [hy.1]

theorem modularLocalInv_pos {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256) (hs : 0 < s) :
    0 < modularLocalInv p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp.two_le hs
  have h := (modularLocalInv_bounds hp hp' hs).1
  nlinarith

/-- **The modular local factor is at most the square of zeta's local factor.** -/
theorem modularLocalFactor_le_eulerFactor_sq {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256)
    (hs : 0 < s) : modularLocalFactor p s ≤ Sporadic.eulerFactor p s ^ 2 := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp.two_le hs
  have hlow := (modularLocalInv_bounds hp hp' hs).1
  have hpos := modularLocalInv_pos hp hp' hs
  have hsq : (0 : ℝ) < (1 - (p : ℝ) ^ (-s)) ^ 2 := pow_pos (by linarith) 2
  rw [modularLocalFactor, Sporadic.eulerFactor, inv_pow]
  exact (inv_le_inv₀ hpos hsq).2 hlow

/-- ... and at least the reciprocal square of the "wrong-sign" factor. -/
theorem eulerFactor_sq_inv_le_modularLocalFactor {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256)
    (hs : 0 < s) : ((1 + (p : ℝ) ^ (-s)) ^ 2)⁻¹ ≤ modularLocalFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp.two_le hs
  have hhigh := (modularLocalInv_bounds hp hp' hs).2
  have hpos := modularLocalInv_pos hp hp' hs
  have hsq : (0 : ℝ) < (1 + (p : ℝ) ^ (-s)) ^ 2 := by positivity
  rw [modularLocalFactor]
  exact inv_anti₀ hpos hhigh

/-- **The local factor of the modular zeta, squeezed between two zeta-type factors.** This is
the grey band drawn behind each prime in the second panel of
`visualization/modular-zeta.svg`. -/
theorem modularLocalFactor_mem_Icc {p : ℕ} (hp : p.Prime) (hp' : p ≤ 256) (hs : 0 < s) :
    modularLocalFactor p s ∈
      Set.Icc (((1 + (p : ℝ) ^ (-s)) ^ 2)⁻¹) (Sporadic.eulerFactor p s ^ 2) :=
  ⟨eulerFactor_sq_inv_le_modularLocalFactor hp hp' hs,
    modularLocalFactor_le_eulerFactor_sq hp hp' hs⟩

end ModularZeta
