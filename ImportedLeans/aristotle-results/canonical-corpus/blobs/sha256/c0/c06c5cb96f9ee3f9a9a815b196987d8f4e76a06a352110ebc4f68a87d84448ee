import RiemannAnalytic.ChebyshevLower

/-!
# Uniform twisted von Mangoldt moments and the twisted prime log-variance

This module carries out the "twisted prime moment" package at the literal prime
side: the weights are the actual von Mangoldt weights `Λ n`, the log-frequencies
are the actual `λ n = log n`, and the twist is the actual functional-equation
`cosh` twist `cosh (2α log n)` produced by pairing `n^{2α}` with `n^{-2α}`.

The abstract-weight analysis of `TiltedLogVariance` proved that for *arbitrary*
positive weights the quantity `α² Var` is unbounded, so no contraction can come
from the hyperbolic algebra alone.  The theorems here show that the *arithmetic*
weights are not arbitrary: the von Mangoldt measure has multiplicative density,
so the exponential tilt always concentrates the mass in the top log-window and
the log-variance stays bounded by an absolute constant, uniformly in the twist.

Main results.

* `tiltedCentered_le` (master Laplace/partial-summation estimate): for every
  `v ≥ -1/2`,
  `∑_{n ≤ N} Λ n · n^v · (log N - log n)^2 ≤ 800 · N^{1+v}`.
  The proof is a genuine scale decomposition: the block `log N - log n ∈ [2k, 2k+2)`
  has von Mangoldt mass at most `(log 4 + 4)·N e^{-2k}` (Chebyshev's upper bound),
  and the tilt can inflate it by at most `e^{k+1}`, leaving a summable `2^{-k}(k+1)²`.
* `tiltedMass_lower`: for `N ≥ 10^8` and `|v| ≤ 1`,
  `N^{1+v}/16 ≤ ∑_{n ≤ N} Λ n · n^v` — the two-sided Chebyshev input
  (`RiemannAnalytic.psi_block_lower`).
* `vonMangoldt_twistedCentered_le_mass`: the two combine into the uniform bound
  `∑ w_α(n)(log n - log N)² ≤ 13000 · ∑ w_α(n)` for the cosh weights
  `w_α(n) = Λ n · cosh (2α log n)`, for every `|α| < 1/2`.
* `zetaTwistedPrimeCenteredVariance`: consequently
  `S₀S₂ - S₁² ≤ 13000 · S₀²`, uniformly for `0 < |α| < 1/2` and `N ≥ 10^8`,
  and `alphaSq_twistedPrimeVariance_le`: `α²(S₀S₂ - S₁²) ≤ 3250 · S₀²`.
* `twistedPrimeVariance_littleO_L6`: in the source normalization `L = log N`, the
  normalized variance is `o(L⁶)`: `α²(S₀S₂ - S₁²) ≤ δ(N)² L⁶ S₀²` with
  `δ(N) = 58/L³ → 0`.

What is **not** proved here: the identification of the literal anchored defect
`D_{ρ,H}` with these moments (`literalCompensatedAnchorIdentity`) and the literal
explicit-formula representation (`literalTwistedPrimeRepresentation`).  The
statements below are about the actual prime weights, but the normalization that
converts `S₀S₂ - S₁² ≤ C S₀²` into a bound against the source floor `c L⁶ α²`
requires those two identifications, which remain open.
-/

open Finset Real ArithmeticFunction Chebyshev

namespace RiemannAnalytic

/-- The tilted von Mangoldt mass `∑_{n ≤ N} Λ n · n^v`. -/
noncomputable def tiltedMass (N : ℕ) (v : ℝ) : ℝ := ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ v

/-- The tilted von Mangoldt second moment about the top log-frequency `log N`. -/
noncomputable def tiltedCentered (N : ℕ) (v : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ v * (Real.log N - Real.log n) ^ 2

/-- The literal cosh-twisted von Mangoldt weight
`w_α(n) = Λ n · cosh (2α log n) = ½ (Λ n · n^{2α} + Λ n · n^{-2α})`. -/
noncomputable def coshVonMangoldt (α : ℝ) (n : ℕ) : ℝ :=
  Λ n * Real.cosh (2 * α * Real.log n)

/-- The twisted prime moments `S_r(α) = ∑_{n ≤ N} w_α(n) (log n)^r`. -/
noncomputable def twistedMoment (N : ℕ) (α : ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n) ^ r

/-! ### A summable geometric input -/

/-- Exact evaluation of the partial sums of `(k+1)² 2^{-k}`. -/
theorem sum_sq_half_pow_eq (K : ℕ) :
    ∑ k ∈ range K, ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k
      = 12 - (2 * (K : ℝ) ^ 2 + 8 * K + 12) * (1 / 2 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

/-- `∑_{k < K} (k+1)² 2^{-k} ≤ 12`. -/
theorem sum_sq_half_pow_le (K : ℕ) :
    ∑ k ∈ range K, ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k ≤ 12 := by
  rw [sum_sq_half_pow_eq]
  have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  nlinarith [sq_nonneg (K : ℝ), Nat.cast_nonneg (α := ℝ) K]

/-! ### The master tilted second moment estimate -/

/-- The scale index of `n ≤ N`: the block `log N - log n ∈ [2k, 2k+2)`. -/
noncomputable def blockIndex (N n : ℕ) : ℕ := ⌊(Real.log N - Real.log n) / 2⌋₊

/-- Chebyshev's upper bound applied to a single scale block: the von Mangoldt mass of
`{n : log N - log n ∈ [2k, 2k+2)}` is at most `(log 4 + 4) N e^{-2k}`. -/
theorem block_mass_le {N : ℕ} (k : ℕ) :
    ∑ n ∈ Icc 1 N with blockIndex N n = k, Λ n
      ≤ (Real.log 4 + 4) * ((N : ℝ) * Real.exp (-(2 * k))) := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  set y : ℝ := (N:ℝ) * Real.exp (-(2*k)) with hy
  have hy0 : 0 < y := by positivity
  have hsub : (Icc 1 N).filter (fun n => blockIndex N n = k) ⊆ Ioc 0 ⌊y⌋₊ := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hk⟩ := hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn2)
    have hs : 0 ≤ (Real.log N - Real.log n)/2 := by linarith
    have hkle : (k:ℝ) ≤ (Real.log N - Real.log n)/2 := by
      rw [← hk]; exact Nat.floor_le hs
    have hlogle : Real.log n ≤ Real.log N - 2*k := by linarith
    have hny : (n:ℝ) ≤ y := by
      have h1 : Real.log (n:ℝ) ≤ Real.log y := by
        rw [hy, Real.log_mul (ne_of_gt hN0) (Real.exp_ne_zero _), Real.log_exp]
        linarith
      exact (Real.log_le_log_iff hn0 hy0).mp h1
    exact Finset.mem_Ioc.mpr ⟨by omega, Nat.le_floor (by exact_mod_cast hny)⟩
  calc ∑ n ∈ Icc 1 N with blockIndex N n = k, Λ n ≤ ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => vonMangoldt_nonneg)
    _ = ψ y := by rw [Chebyshev.psi]
    _ ≤ (Real.log 4 + 4) * y := Chebyshev.psi_le_const_mul_self hy0.le

/-- Inside one scale block the tilt inflates the weight by at most `e^{k+1}` (this is
where `v ≥ -1/2` is used) and the centered log-frequency is at most `2(k+1)`. -/
theorem block_term_le {N : ℕ} {v : ℝ} (hv : -(1/2:ℝ) ≤ v) (k n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ N) (hk : blockIndex N n = k) :
    Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2
      ≤ ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) * Λ n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le hn0 (by exact_mod_cast hn2)
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hle : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn2)
  set s : ℝ := Real.log N - Real.log n with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; linarith
  have hfl : (k:ℝ) ≤ s/2 ∧ s/2 < (k:ℝ)+1 := by
    constructor
    · rw [← hk]; exact Nat.floor_le (by linarith)
    · rw [← hk]; exact Nat.lt_floor_add_one _
  have hs2 : s ≤ 2*((k:ℝ)+1) := by linarith [hfl.2]
  have hnv : (n:ℝ)^v ≤ (N:ℝ)^v * Real.exp ((k:ℝ)+1) := by
    have h1 : (n:ℝ)^v = Real.exp (v * Real.log n) := by
      rw [Real.rpow_def_of_pos hn0]; ring_nf
    have h2 : (N:ℝ)^v = Real.exp (v * Real.log N) := by
      rw [Real.rpow_def_of_pos hN0]; ring_nf
    rw [h1, h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hvs : -v * s ≤ s/2 := by nlinarith
    have hrw : v * Real.log n = v * Real.log N - v * s := by rw [hs_def]; ring
    rw [hrw]
    linarith [hfl.2]
  have hsq : s^2 ≤ 4*((k:ℝ)+1)^2 := by nlinarith
  have hΛ := vonMangoldt_nonneg (n := n)
  have hnvpos : (0:ℝ) ≤ (n:ℝ)^v := Real.rpow_nonneg hn0.le v
  have hprod : (n:ℝ)^v * s^2 ≤ ((N:ℝ)^v * Real.exp ((k:ℝ)+1)) * (4*((k:ℝ)+1)^2) :=
    mul_le_mul hnv hsq (by positivity) (by positivity)
  calc Λ n * (n:ℝ)^v * s^2 = Λ n * ((n:ℝ)^v * s^2) := by ring
    _ ≤ Λ n * (((N:ℝ)^v * Real.exp ((k:ℝ)+1)) * (4*((k:ℝ)+1)^2)) :=
        mul_le_mul_of_nonneg_left hprod hΛ
    _ = ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) * Λ n := by ring

private lemma exp_neg_le_half_pow (k : ℕ) : Real.exp (-(k:ℝ)) ≤ (1/2:ℝ)^k := by
  rw [show ((1:ℝ)/2)^k = Real.exp (Real.log (1/2) * k) by
    rw [Real.exp_mul, Real.exp_log (by norm_num)]
    exact (Real.rpow_natCast _ k).symm]
  apply Real.exp_le_exp.mpr
  rw [show Real.log (1/2) = -Real.log 2 by rw [one_div, Real.log_inv]]
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Real.log_two_lt_d9]

/-- **Master tilted second-moment estimate.**  For every tilt `v ≥ -1/2`,
`∑_{n ≤ N} Λ n · n^v · (log N - log n)² ≤ 800 · N^{1+v}`.
The estimate is uniform in the tilt: the exponential inflation `e^{k+1}` of the tilt is
beaten by the Chebyshev decay `e^{-2k}` of the von Mangoldt mass at scale `k`. -/
theorem tiltedCentered_le {N : ℕ} {v : ℝ} (hv : -(1 / 2 : ℝ) ≤ v) :
    tiltedCentered N v ≤ 800 * (N : ℝ) ^ (1 + v) := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [tiltedCentered, Nat.Icc_eq_range']
    simp only [Nat.sub_self]
    norm_num
    exact Real.rpow_nonneg le_rfl _
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hNv : (0:ℝ) < (N:ℝ)^v := Real.rpow_pos_of_pos hN0 v
  set K : ℕ := ⌊Real.log N / 2⌋₊ with hK
  have hmaps : ∀ n ∈ Icc 1 N, blockIndex N n ∈ range (K+1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : blockIndex N n ≤ K := by
      rw [blockIndex, hK]
      exact Nat.floor_le_floor (by linarith)
    simpa using Nat.lt_succ_of_le hle
  have hsplit : tiltedCentered N v
      = ∑ k ∈ range (K+1), ∑ n ∈ Icc 1 N with blockIndex N n = k,
          Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2 := by
    rw [tiltedCentered, ← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ k ∈ range (K+1),
      (∑ n ∈ Icc 1 N with blockIndex N n = k, Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2)
        ≤ (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) *
            (((k:ℝ)+1)^2 * (1/2:ℝ)^k) := by
    intro k _
    have h1 : (∑ n ∈ Icc 1 N with blockIndex N n = k,
          Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2)
        ≤ ∑ n ∈ Icc 1 N with blockIndex N n = k,
            ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) * Λ n := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      exact block_term_le hv k n hn.1.1 hn.1.2 hn.2
    have h2 : (∑ n ∈ Icc 1 N with blockIndex N n = k,
            ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) * Λ n)
        = ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) *
            ∑ n ∈ Icc 1 N with blockIndex N n = k, Λ n := by
      rw [Finset.mul_sum]
    have hcoef : (0:ℝ) ≤ (N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2) := by positivity
    have h4 : (∑ n ∈ Icc 1 N with blockIndex N n = k,
          Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2)
        ≤ ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) *
            ((Real.log 4 + 4) * ((N:ℝ) * Real.exp (-(2*k)))) := by
      calc _ ≤ _ := h1
        _ = _ := h2
        _ ≤ _ := mul_le_mul_of_nonneg_left (block_mass_le k) hcoef
    refine h4.trans ?_
    have hexp : Real.exp ((k:ℝ)+1) * Real.exp (-(2*k)) = Real.exp 1 * Real.exp (-(k:ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hpos : (0:ℝ) ≤ (N:ℝ)^v * (N:ℝ) * (4*((k:ℝ)+1)^2) * (Real.log 4 + 4) := by
      have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      positivity
    calc ((N:ℝ)^v * Real.exp ((k:ℝ)+1) * (4*((k:ℝ)+1)^2)) *
            ((Real.log 4 + 4) * ((N:ℝ) * Real.exp (-(2*k))))
        = ((N:ℝ)^v * (N:ℝ) * (4*((k:ℝ)+1)^2) * (Real.log 4 + 4)) *
            (Real.exp ((k:ℝ)+1) * Real.exp (-(2*k))) := by ring
      _ = ((N:ℝ)^v * (N:ℝ) * (4*((k:ℝ)+1)^2) * (Real.log 4 + 4)) *
            (Real.exp 1 * Real.exp (-(k:ℝ))) := by rw [hexp]
      _ ≤ ((N:ℝ)^v * (N:ℝ) * (4*((k:ℝ)+1)^2) * (Real.log 4 + 4)) *
            (Real.exp 1 * (1/2:ℝ)^k) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          nlinarith [exp_neg_le_half_pow k, Real.exp_pos 1]
      _ = (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) *
            (((k:ℝ)+1)^2 * (1/2:ℝ)^k) := by ring
  have hCpos : (0:ℝ) ≤ (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) := by
    have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hchain : tiltedCentered N v
      ≤ (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) * 12 := by
    calc tiltedCentered N v = _ := hsplit
      _ ≤ ∑ k ∈ range (K+1), (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) *
            (((k:ℝ)+1)^2 * (1/2:ℝ)^k) := Finset.sum_le_sum hblock
      _ = (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) *
            ∑ k ∈ range (K+1), ((k:ℝ)+1)^2 * (1/2:ℝ)^k := by rw [Finset.mul_sum]
      _ ≤ (4 * Real.exp 1 * (Real.log 4 + 4)) * ((N:ℝ)^v * (N:ℝ)) * 12 :=
          mul_le_mul_of_nonneg_left (sum_sq_half_pow_le (K+1)) hCpos
  have hNpow : (N:ℝ)^(1+v) = (N:ℝ)^v * (N:ℝ) := by
    rw [Real.rpow_add hN0, Real.rpow_one]; ring
  have hconst : (4 * Real.exp 1 * (Real.log 4 + 4)) * 12 ≤ 800 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
    nlinarith [Real.exp_one_lt_d9, Real.log_two_lt_d9, Real.exp_pos 1]
  rw [hNpow]
  nlinarith [hchain, hNv, hN0, mul_pos hNv hN0]

/-! ### The tilted mass lower bound -/

theorem tiltedMass_lower {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {v : ℝ} (hv : |v| ≤ 1) :
    (N : ℝ) ^ (1 + v) / 16 ≤ tiltedMass N v := by
  have hX0 : (0:ℝ) < (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set M : ℕ := ⌊(N:ℝ)/4⌋₊ with hM
  have hMN : M ≤ N := by
    have h1 : M ≤ ⌊(N:ℝ)⌋₊ := Nat.floor_le_floor (by linarith)
    simpa using h1
  have hblock : (N:ℝ)/4 ≤ ∑ n ∈ Ioc M N, Λ n := by
    have h1 : ψ (N:ℝ) = ∑ n ∈ Ioc 0 N, Λ n := by rw [Chebyshev.psi, Nat.floor_natCast]
    have h2 : ψ ((N:ℝ)/4) = ∑ n ∈ Ioc 0 M, Λ n := by rw [Chebyshev.psi]
    have h3 : ∑ n ∈ Ioc 0 M, Λ n + ∑ n ∈ Ioc M N, Λ n = ∑ n ∈ Ioc 0 N, Λ n :=
      Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN
    have h4 := psi_block_lower (x := (N:ℝ)) hN
    rw [h1, h2] at h4
    linarith
  have hstep1 : ∑ n ∈ Ioc M N, Λ n * ((N:ℝ) ^ v / 4) ≤ ∑ n ∈ Ioc M N, Λ n * (n:ℝ)^v := by
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnX : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn.2
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hlow : (N:ℝ)/4 ≤ (n:ℝ) := by
      have hfl : (N:ℝ)/4 < (M:ℝ) + 1 := Nat.lt_floor_add_one _
      have h5 : (M:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hn.1
      linarith
    have hcmp : (N:ℝ) ^ v / 4 ≤ (n:ℝ) ^ v := by
      rcases le_or_gt 0 v with hv0 | hv0
      · have h1 : ((N:ℝ)/4) ^ v ≤ (n:ℝ) ^ v := Real.rpow_le_rpow (by positivity) hlow hv0
        have h2 : (N:ℝ) ^ v / 4 ≤ ((N:ℝ)/4) ^ v := by
          rw [Real.div_rpow hX0.le (by norm_num)]
          have h3 : (4:ℝ) ^ v ≤ 4 := by
            calc (4:ℝ)^v ≤ (4:ℝ)^(1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by cases abs_le.mp hv; linarith)
              _ = 4 := Real.rpow_one 4
          have h4 : (0:ℝ) < (4:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) v
          gcongr
        linarith
      · have h1 : (N:ℝ) ^ v ≤ (n:ℝ) ^ v := Real.rpow_le_rpow_of_nonpos hnpos hnX hv0.le
        have h2 : (0:ℝ) < (N:ℝ) ^ v := Real.rpow_pos_of_pos hX0 v
        linarith
    have hΛ := vonMangoldt_nonneg (n := n)
    nlinarith
  have hstep2 : ∑ n ∈ Ioc M N, Λ n * (n:ℝ)^v ≤ tiltedMass N v := by
    rw [tiltedMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩
    · intro i _ _
      have := vonMangoldt_nonneg (n := i)
      positivity
  have hXv : (0:ℝ) < (N:ℝ) ^ v := Real.rpow_pos_of_pos hX0 v
  have hsum : ∑ n ∈ Ioc M N, Λ n * ((N:ℝ) ^ v / 4) = (∑ n ∈ Ioc M N, Λ n) * ((N:ℝ)^v/4) := by
    rw [← Finset.sum_mul]
  have hfinal : (N:ℝ) ^ (1+v) / 16 ≤ (∑ n ∈ Ioc M N, Λ n) * ((N:ℝ)^v/4) := by
    have hxx : (N:ℝ) ^ (1+v) = (N:ℝ) * (N:ℝ) ^ v := by rw [Real.rpow_add hX0, Real.rpow_one]
    rw [hxx]
    nlinarith [hblock, hXv]
  rw [hsum] at hstep1
  linarith

/-! ### Variance is dominated by any centered second moment -/

theorem variance_le_centered (s : Finset ℕ) (w l : ℕ → ℝ) (hw : ∀ n ∈ s, 0 ≤ w n) (c : ℝ) :
    (∑ n ∈ s, w n) * (∑ n ∈ s, w n * (l n) ^ 2) - (∑ n ∈ s, w n * l n) ^ 2
      ≤ (∑ n ∈ s, w n) * (∑ n ∈ s, w n * (l n - c) ^ 2) := by
  have hexp : ∑ n ∈ s, w n * (l n - c) ^ 2
      = (∑ n ∈ s, w n * (l n)^2) - 2*c*(∑ n ∈ s, w n * l n) + c^2 * (∑ n ∈ s, w n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hS0 : 0 ≤ ∑ n ∈ s, w n := Finset.sum_nonneg hw
  rw [hexp]
  nlinarith [sq_nonneg ((∑ n ∈ s, w n * l n) - c * (∑ n ∈ s, w n)), hS0]

/-! ### The literal cosh-twisted statements -/

private lemma icc_eq_ioc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext m; simp [Nat.lt_iff_add_one_le]

/-- Nonnegativity of the twisted weights. -/
theorem coshVonMangoldt_nonneg (α : ℝ) (n : ℕ) : 0 ≤ coshVonMangoldt α n :=
  mul_nonneg vonMangoldt_nonneg (Real.cosh_pos _).le

theorem tiltedMass_nonneg (N : ℕ) (v : ℝ) : 0 ≤ tiltedMass N v :=
  Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) v)

/-- The functional-equation pair: the cosh twist is the average of the two tilts. -/
theorem cosh_split (α : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    coshVonMangoldt α n = (Λ n * (n:ℝ)^(2*α) + Λ n * (n:ℝ)^(-(2*α)))/2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [coshVonMangoldt, Real.cosh_eq, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  ring_nf

theorem coshVonMangoldt_abs (α : ℝ) (n : ℕ) : coshVonMangoldt α n = coshVonMangoldt |α| n := by
  rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [coshVonMangoldt, coshVonMangoldt, show 2 * -α * Real.log n = -(2*α*Real.log n) by ring,
    Real.cosh_neg]

theorem coshMass_eq (N : ℕ) (α : ℝ) :
    ∑ n ∈ Icc 1 N, coshVonMangoldt α n = (tiltedMass N (2*α) + tiltedMass N (-(2*α)))/2 := by
  rw [tiltedMass, tiltedMass, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun n hn => cosh_split α (Finset.mem_Icc.mp hn).1

theorem coshCentered_eq (N : ℕ) (α : ℝ) :
    ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n - Real.log N)^2
      = (tiltedCentered N (2*α) + tiltedCentered N (-(2*α)))/2 := by
  rw [tiltedCentered, tiltedCentered, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [cosh_split α (Finset.mem_Icc.mp hn).1,
    show (Real.log n - Real.log N)^2 = (Real.log N - Real.log n)^2 by ring]
  ring

/-- The crude bound for a strongly negative tilt: there the tilted measure is no longer
concentrated, but its total mass is negligible compared with the positive tilt. -/
theorem tiltedCentered_crude {N : ℕ} {v : ℝ} (hv : v ≤ 0) :
    tiltedCentered N v ≤ (Real.log N)^2 * ((Real.log 4 + 4) * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp [tiltedCentered]
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : tiltedCentered N v ≤ ∑ n ∈ Icc 1 N, Λ n * (Real.log N)^2 := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn2)
    have hnv : (n:ℝ)^v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) hv
    have hΛ := vonMangoldt_nonneg (n := n)
    have hsq : (Real.log N - Real.log n)^2 ≤ (Real.log N)^2 := by nlinarith
    calc Λ n * (n:ℝ)^v * (Real.log N - Real.log n)^2
        ≤ (Λ n * 1) * (Real.log N)^2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hnv hΛ) hsq (sq_nonneg _) (by positivity)
      _ = Λ n * (Real.log N)^2 := by ring
  have h2 : ∑ n ∈ Icc 1 N, Λ n * (Real.log N)^2 = (∑ n ∈ Icc 1 N, Λ n) * (Real.log N)^2 := by
    rw [← Finset.sum_mul]
  have h3 : ∑ n ∈ Icc 1 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have h4 : ∑ n ∈ Icc 1 N, Λ n = ψ (N:ℝ) := by
      rw [Chebyshev.psi, Nat.floor_natCast, icc_eq_ioc]
    rw [h4]
    exact Chebyshev.psi_le_const_mul_self hN0.le
  nlinarith [h1, h2, h3, sq_nonneg (Real.log N)]

/-- **Uniform twisted concentration for the literal von Mangoldt weights.**  For every
off-line displacement `|α| < 1/2` the cosh-twisted prime measure has centered second
moment (about the top log-frequency `log N`) bounded by an absolute multiple of its mass. -/
theorem vonMangoldt_twistedCentered_le_mass {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) :
    ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n - Real.log N) ^ 2
      ≤ 15000 * ∑ n ∈ Icc 1 N, coshVonMangoldt α n := by
  have hN0 : (0:ℝ) < (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hrw1 : ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n - Real.log N)^2
      = ∑ n ∈ Icc 1 N, coshVonMangoldt |α| n * (Real.log n - Real.log N)^2 :=
    Finset.sum_congr rfl fun n _ => by rw [coshVonMangoldt_abs α n]
  have hrw2 : ∑ n ∈ Icc 1 N, coshVonMangoldt α n = ∑ n ∈ Icc 1 N, coshVonMangoldt |α| n :=
    Finset.sum_congr rfl fun n _ => coshVonMangoldt_abs α n
  rw [hrw1, hrw2]
  set β : ℝ := |α| with hβdef
  have hβ0 : 0 ≤ β := abs_nonneg α
  have hβ : β < 1/2 := hα
  rw [coshCentered_eq, coshMass_eq]
  set A := tiltedCentered N (2*β)
  set B := tiltedCentered N (-(2*β))
  set a := tiltedMass N (2*β)
  set b := tiltedMass N (-(2*β))
  have hA : A ≤ 800 * (N:ℝ)^(1+2*β) := tiltedCentered_le (by linarith)
  have ha : (N:ℝ)^(1+2*β)/16 ≤ a := tiltedMass_lower hN (by rw [abs_le]; constructor <;> linarith)
  have hb : (N:ℝ)^(1+ -(2*β))/16 ≤ b :=
    tiltedMass_lower hN (by rw [abs_neg, abs_le]; constructor <;> linarith)
  have hbnn : 0 ≤ b := tiltedMass_nonneg _ _
  have hann : 0 ≤ a := tiltedMass_nonneg _ _
  rcases le_or_gt β (1/4) with hcase | hcase
  · have hB : B ≤ 800 * (N:ℝ)^(1 + -(2*β)) := tiltedCentered_le (by linarith)
    linarith
  · have hlogsq : (Real.log N)^2 ≤ 16 * (N:ℝ)^((1:ℝ)/2) := by
      have h1 : Real.log N ≤ 4 * (N:ℝ)^((1:ℝ)/4) := by
        calc Real.log N ≤ (N:ℝ) ^ ((1:ℝ)/4) / (1/4) := by
              simpa using Real.log_le_rpow_div hN0.le (by norm_num : (0:ℝ) < 1/4)
          _ = 4 * (N:ℝ) ^ ((1:ℝ)/4) := by ring
      have h2 : ((N:ℝ)^((1:ℝ)/4))^(2:ℕ) = (N:ℝ)^((1:ℝ)/2) := by
        rw [← Real.rpow_natCast ((N:ℝ)^((1:ℝ)/4)) 2, ← Real.rpow_mul hN0.le]; norm_num
      have h3 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      nlinarith [h1, h2, Real.rpow_nonneg hN0.le ((1:ℝ)/4)]
    have hhalf : (N:ℝ)^((1:ℝ)/2) * (N:ℝ) = (N:ℝ)^((3:ℝ)/2) := by
      have h : (N:ℝ)^((3:ℝ)/2) = (N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ) := by
        rw [← Real.rpow_add hN0]; norm_num
      rw [h, Real.rpow_one]
    have hexp : (N:ℝ)^((3:ℝ)/2) ≤ (N:ℝ)^(1+2*β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hBc : B ≤ (Real.log N)^2 * ((Real.log 4 + 4) * N) := tiltedCentered_crude (by linarith)
    have hlog4 : Real.log 4 + 4 ≤ 5.4 := by
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
      nlinarith [Real.log_two_lt_d9]
    have hB : B ≤ 87 * (N:ℝ)^(1+2*β) := by
      have h5 : (Real.log N)^2 * ((Real.log 4 + 4) * N) ≤ (16 * (N:ℝ)^((1:ℝ)/2)) * (5.4 * N) := by
        apply mul_le_mul hlogsq _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hlog4 hN0.le
      have h6 : (16 * (N:ℝ)^((1:ℝ)/2)) * (5.4 * N) = 86.4 * ((N:ℝ)^((1:ℝ)/2) * N) := by ring
      rw [h6, hhalf] at h5
      nlinarith [h5, hBc, hexp]
    nlinarith [hA, hB, ha, hbnn, hann]

theorem twistedMoment_zero (N : ℕ) (α : ℝ) :
    twistedMoment N α 0 = ∑ n ∈ Icc 1 N, coshVonMangoldt α n := by
  simp [twistedMoment]

theorem twistedMoment_one (N : ℕ) (α : ℝ) :
    twistedMoment N α 1 = ∑ n ∈ Icc 1 N, coshVonMangoldt α n * Real.log n := by
  simp [twistedMoment]

/-- **The twisted prime centered variance theorem.**  For the literal von Mangoldt
weights with the literal functional-equation `cosh` twist, the log-frequency variance
`S₀S₂ - S₁²` is at most an absolute constant times `S₀²`, uniformly for every off-line
displacement `0 < |α| < 1/2` and every `N ≥ 10^8`.  This is the arithmetic input that the
arbitrary-weight counterexamples of `TiltedLogVariance` cannot see: the von Mangoldt
measure has multiplicative density, so the tilt concentrates it in the top log-window. -/
theorem zetaTwistedPrimeCenteredVariance {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) :
    twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2
      ≤ 15000 * (twistedMoment N α 0) ^ 2 := by
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, coshVonMangoldt α n :=
    Finset.sum_nonneg fun n _ => coshVonMangoldt_nonneg α n
  have hvar := variance_le_centered (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n)
    (fun n _ => coshVonMangoldt_nonneg α n) (Real.log N)
  have hmass := vonMangoldt_twistedCentered_le_mass hN hα
  rw [twistedMoment_zero, twistedMoment_one]
  have h2 : twistedMoment N α 2 = ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n) ^ 2 := rfl
  rw [h2]
  nlinarith [hvar, hmass, hS0]

/-- The `α²`-carrying form of the twisted prime variance theorem. -/
theorem alphaSq_twistedPrimeVariance_le {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) :
    α ^ 2 * (twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2)
      ≤ 3750 * (twistedMoment N α 0) ^ 2 := by
  have hmain := zetaTwistedPrimeCenteredVariance hN hα
  have habs : α^2 ≤ 1/4 := by
    have h1 : |α| < 1/2 := hα
    nlinarith [abs_nonneg α, sq_abs α]
  have hsq : (0:ℝ) ≤ (twistedMoment N α 0)^2 := sq_nonneg _
  rcases le_or_gt 0 (twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2)
    with hV | hV
  · nlinarith [hmain, habs, hV, sq_nonneg α]
  · nlinarith [sq_nonneg α, hsq]

/-! ### The `o(L⁶)` form in the source normalization -/

/-- In the source normalization `L = log N` the twisted prime variance is `o(L⁶)`
relative to the twisted mass: for every `ε > 0`, eventually in `N`,
`α²(S₀S₂ - S₁²) ≤ ε L⁶ S₀²` uniformly for `0 < |α| < 1/2`. -/
theorem twistedPrimeVariance_isLittleO_L6 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ α : ℝ, |α| < 1/2 →
      α ^ 2 * (twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2)
        ≤ ε * (Real.log N) ^ 6 * (twistedMoment N α 0) ^ 2 := by
  have hlog : Filter.Tendsto (fun N : ℕ => ε * (Real.log N) ^ 6) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.const_mul_atTop hε
    exact (Filter.tendsto_pow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, (3750:ℝ) ≤ ε * (Real.log N) ^ 6 := hlog.eventually_ge_atTop _
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, (10:ℝ) ^ 8 ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [h1, h2] with N hN1 hN2 α hα
  have hmain := alphaSq_twistedPrimeVariance_le hN2 hα
  nlinarith [hmain, sq_nonneg (twistedMoment N α 0)]

end RiemannAnalytic
