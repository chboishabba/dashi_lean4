import RiemannAnalytic.TwistedPrimeMoments

/-!
# The matching lower bound: the twisted prime log-variance is not small

`RiemannAnalytic.zetaTwistedPrimeCenteredVariance` bounds the twisted prime
log-variance above by an absolute multiple of `S₀²`.  This module proves the
matching lower bound: the variance is also at least an absolute *positive*
multiple of `S₀²`, uniformly for `|α| < 1/2`.

Consequently the relative twisted prime variance is `Θ(1)`: it does **not** tend
to `0`.  This is a quantitative answer to the question of whether the twisted
prime measure can supply a vanishing relative budget by itself.  It cannot: the
cosh tilt concentrates the von Mangoldt measure in the top log-window, but the
window still has width `Θ(1)` in log-frequency, because the prime mass in the
blocks `(N/4, N]` and `(N/32, N/8]` is comparable and those blocks are `log 2`
apart in log-frequency.  Any gain therefore has to come from the source
normalization of `S₀` against `L³`, not from the shape of the twisted prime
measure.

Main results.

* `varForm_eq_double` : the exact identity
  `S₀S₂ - S₁² = ½ ∑∑ wₙwₘ(λₙ - λₘ)²`.
* `varForm_ge_blocks` : the two-block lower bound for that form.
* `zetaTwistedPrimeVariance_lower` : `10⁻⁷ S₀² ≤ S₀S₂ - S₁²` for `N ≥ 10⁹` and
  `|α| < 1/2`, with the literal von Mangoldt cosh weights.
-/

open Finset Real ArithmeticFunction Chebyshev

namespace RiemannAnalytic

private lemma icc_one_eq_ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N :=
  Finset.val_inj.mp rfl

/-- The exact second-difference form of the weighted log-variance. -/
theorem varForm_eq_double (s : Finset ℕ) (w l : ℕ → ℝ) :
    (∑ n ∈ s, w n) * (∑ n ∈ s, w n * (l n) ^ 2) - (∑ n ∈ s, w n * l n) ^ 2
      = (1 / 2) * ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
  have key : ∀ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2
      = (w n * (l n) ^ 2) * (∑ m ∈ s, w m) - (w n * l n) * (2 * ∑ m ∈ s, w m * l m)
        + (w n) * (∑ m ∈ s, w m * (l m) ^ 2) := by
    intro n _
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Two blocks of the index set that are `d` apart in log-frequency force the weighted
log-variance to be at least half the product of their masses times `d²`. -/
theorem varForm_ge_blocks {s t₁ t₂ : Finset ℕ} (h₁ : t₁ ⊆ s) (h₂ : t₂ ⊆ s) (w l : ℕ → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) {d : ℝ} (hd : 0 ≤ d)
    (hsep : ∀ n ∈ t₁, ∀ m ∈ t₂, d ≤ |l n - l m|) :
    (1 / 2) * ((∑ n ∈ t₁, w n) * (∑ m ∈ t₂, w m) * d ^ 2)
      ≤ (∑ n ∈ s, w n) * (∑ n ∈ s, w n * (l n) ^ 2) - (∑ n ∈ s, w n * l n) ^ 2 := by
  rw [varForm_eq_double]
  have hTnn : ∀ n ∈ s, ∀ m ∈ s, 0 ≤ w n * w m * (l n - l m) ^ 2 := by
    intro n hn m hm
    exact mul_nonneg (mul_nonneg (hw n hn) (hw m hm)) (sq_nonneg _)
  have step1 : ∑ n ∈ t₁, ∑ m ∈ t₂, w n * w m * (l n - l m) ^ 2
      ≤ ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
    calc ∑ n ∈ t₁, ∑ m ∈ t₂, w n * w m * (l n - l m) ^ 2
        ≤ ∑ n ∈ t₁, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg h₂
            (fun m hm _ => hTnn n (h₁ hn) m hm)
      _ ≤ ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg h₁ fun n hn _ => ?_
          exact Finset.sum_nonneg fun m hm => hTnn n hn m hm
  have step2 : (∑ n ∈ t₁, w n) * (∑ m ∈ t₂, w m) * d ^ 2
      ≤ ∑ n ∈ t₁, ∑ m ∈ t₂, w n * w m * (l n - l m) ^ 2 := by
    have expand : (∑ n ∈ t₁, w n) * (∑ m ∈ t₂, w m) * d ^ 2
        = ∑ n ∈ t₁, ∑ m ∈ t₂, w n * w m * d ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [expand]
    refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
    have hsq : d ^ 2 ≤ (l n - l m) ^ 2 := by
      have h := hsep n hn m hm
      nlinarith [abs_nonneg (l n - l m), sq_abs (l n - l m)]
    exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (hw n (h₁ hn)) (hw m (h₂ hm)))
  linarith

private lemma cosh_ge_half_rpow {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 * |α|) / 2 ≤ Real.cosh (2 * α * Real.log n) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have habs : Real.cosh (2 * α * Real.log n) = Real.cosh (2 * |α| * Real.log n) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -α * Real.log n = -(2 * α * Real.log n) by ring, Real.cosh_neg]
  rw [habs, Real.cosh_eq, Real.rpow_def_of_pos hn0]
  have := Real.exp_pos (-(2 * |α| * Real.log n))
  have heq : Real.exp (Real.log n * (2 * |α|)) = Real.exp (2 * |α| * Real.log n) := by
    rw [mul_comm]
  rw [heq]
  linarith

private lemma cosh_le_rpow {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    Real.cosh (2 * α * Real.log n) ≤ (n : ℝ) ^ (2 * |α|) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have habs : Real.cosh (2 * α * Real.log n) = Real.cosh (2 * |α| * Real.log n) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -α * Real.log n = -(2 * α * Real.log n) by ring, Real.cosh_neg]
  rw [habs, Real.cosh_eq, Real.rpow_def_of_pos hn0, show Real.log n * (2 * |α|)
    = 2 * |α| * Real.log n by ring]
  have hx : 0 ≤ 2 * |α| * Real.log n := by positivity
  have h1 : Real.exp (-(2 * |α| * Real.log n)) ≤ Real.exp (2 * |α| * Real.log n) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **The twisted prime log-variance is bounded below**, uniformly in the twist:
`10⁻⁷ S₀² ≤ S₀S₂ - S₁²`.  Together with `zetaTwistedPrimeCenteredVariance` this shows the
relative twisted prime variance is `Θ(1)`, so it cannot itself provide a vanishing
relative budget. -/
theorem zetaTwistedPrimeVariance_lower {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) :
    (1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2
      ≤ twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2 := by
  have h10 : (0:ℝ) < 10 ^ 9 := by positivity
  have hX0 : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le h10 hN
  have hX1 : (1:ℝ) ≤ (N:ℝ) := by nlinarith
  set β : ℝ := |α| with hβ_def
  have hβ0 : 0 ≤ β := abs_nonneg α
  have hβ : β < 1/2 := hα
  obtain ⟨P, hP_def⟩ : ∃ P : ℝ, P = (N:ℝ) ^ (2*β) * (N:ℝ) := ⟨_, rfl⟩
  have hXb : (0:ℝ) < (N:ℝ) ^ (2*β) := Real.rpow_pos_of_pos hX0 _
  have hP0 : 0 < P := by rw [hP_def]; positivity
  -- the two blocks
  set M₁ : ℕ := ⌊(N:ℝ)/4⌋₊ with hM₁
  set M₂ : ℕ := ⌊(N:ℝ)/8⌋₊ with hM₂
  set M₃ : ℕ := ⌊(N:ℝ)/32⌋₊ with hM₃
  have hM₁N : M₁ ≤ N := by
    have : M₁ ≤ ⌊(N:ℝ)⌋₊ := Nat.floor_le_floor (by linarith)
    simpa using this
  have hM₂N : M₂ ≤ N := by
    have : M₂ ≤ ⌊(N:ℝ)⌋₊ := Nat.floor_le_floor (by linarith)
    simpa using this
  have hM₃₂ : M₃ ≤ M₂ := Nat.floor_le_floor (by linarith)
  -- prime mass in the two blocks
  have hmass₁ : (N:ℝ)/4 ≤ ∑ n ∈ Ioc M₁ N, Λ n := by
    have h1 : ψ (N:ℝ) = ∑ n ∈ Ioc 0 N, Λ n := by rw [Chebyshev.psi, Nat.floor_natCast]
    have h2 : ψ ((N:ℝ)/4) = ∑ n ∈ Ioc 0 M₁, Λ n := by rw [Chebyshev.psi]
    have h3 : ∑ n ∈ Ioc 0 M₁, Λ n + ∑ n ∈ Ioc M₁ N, Λ n = ∑ n ∈ Ioc 0 N, Λ n :=
      Finset.sum_Ioc_consecutive _ (Nat.zero_le M₁) hM₁N
    have h4 := psi_block_lower (x := (N:ℝ)) (by nlinarith)
    rw [h1, h2] at h4
    linarith
  have hmass₂ : (N:ℝ)/32 ≤ ∑ n ∈ Ioc M₃ M₂, Λ n := by
    have h1 : ψ ((N:ℝ)/8) = ∑ n ∈ Ioc 0 M₂, Λ n := by rw [Chebyshev.psi]
    have h2 : ψ ((N:ℝ)/8/4) = ∑ n ∈ Ioc 0 M₃, Λ n := by
      rw [Chebyshev.psi, show (N:ℝ)/8/4 = (N:ℝ)/32 by ring]
    have h3 : ∑ n ∈ Ioc 0 M₃, Λ n + ∑ n ∈ Ioc M₃ M₂, Λ n = ∑ n ∈ Ioc 0 M₂, Λ n :=
      Finset.sum_Ioc_consecutive _ (Nat.zero_le M₃) hM₃₂
    have h4 := psi_block_lower (x := (N:ℝ)/8) (by nlinarith)
    rw [h1, h2] at h4
    linarith
  -- weights on the blocks
  have hblock₁ : P / 32 ≤ ∑ n ∈ Ioc M₁ N, coshVonMangoldt α n := by
    have hterm : ∀ n ∈ Ioc M₁ N, Λ n * ((N:ℝ) ^ (2*β) / 8) ≤ coshVonMangoldt α n := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have hn1' : 1 ≤ n := by omega
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn1'
      have hlow : (N:ℝ)/4 ≤ (n:ℝ) := by
        have hfl : (N:ℝ)/4 < (M₁:ℝ) + 1 := Nat.lt_floor_add_one _
        have h5 : (M₁:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hn1
        linarith
      have hrpow : (N:ℝ) ^ (2*β) / 4 ≤ (n:ℝ) ^ (2*β) := by
        have h1 : ((N:ℝ)/4) ^ (2*β) ≤ (n:ℝ) ^ (2*β) :=
          Real.rpow_le_rpow (by positivity) hlow (by linarith)
        have h2 : (N:ℝ) ^ (2*β) / 4 ≤ ((N:ℝ)/4) ^ (2*β) := by
          rw [Real.div_rpow hX0.le (by norm_num)]
          have h3 : (4:ℝ) ^ (2*β) ≤ 4 := by
            calc (4:ℝ) ^ (2*β) ≤ (4:ℝ) ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 4 := Real.rpow_one 4
          have h4 : (0:ℝ) < (4:ℝ) ^ (2*β) := Real.rpow_pos_of_pos (by norm_num) _
          gcongr
        linarith
      have hcosh : (n:ℝ) ^ (2*β) / 2 ≤ Real.cosh (2 * α * Real.log n) := by
        have := cosh_ge_half_rpow (α := α) (n := n) hn1'
        rwa [← hβ_def] at this
      have hΛ := vonMangoldt_nonneg (n := n)
      rw [coshVonMangoldt]
      have hstep : (N:ℝ) ^ (2*β) / 8 ≤ Real.cosh (2 * α * Real.log n) := by linarith
      exact mul_le_mul_of_nonneg_left hstep hΛ
    calc P / 32 = ((N:ℝ) ^ (2*β) / 8) * ((N:ℝ)/4) := by rw [hP_def]; ring
      _ ≤ ((N:ℝ) ^ (2*β) / 8) * (∑ n ∈ Ioc M₁ N, Λ n) := by
          apply mul_le_mul_of_nonneg_left hmass₁ (by positivity)
      _ = ∑ n ∈ Ioc M₁ N, Λ n * ((N:ℝ) ^ (2*β) / 8) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ ∑ n ∈ Ioc M₁ N, coshVonMangoldt α n := Finset.sum_le_sum hterm
  have hblock₂ : P / 2048 ≤ ∑ n ∈ Ioc M₃ M₂, coshVonMangoldt α n := by
    have hterm : ∀ n ∈ Ioc M₃ M₂, Λ n * ((N:ℝ) ^ (2*β) / 64) ≤ coshVonMangoldt α n := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have hn1' : 1 ≤ n := by omega
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn1'
      have hlow : (N:ℝ)/32 ≤ (n:ℝ) := by
        have hfl : (N:ℝ)/32 < (M₃:ℝ) + 1 := Nat.lt_floor_add_one _
        have h5 : (M₃:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hn1
        linarith
      have hrpow : (N:ℝ) ^ (2*β) / 32 ≤ (n:ℝ) ^ (2*β) := by
        have h1 : ((N:ℝ)/32) ^ (2*β) ≤ (n:ℝ) ^ (2*β) :=
          Real.rpow_le_rpow (by positivity) hlow (by linarith)
        have h2 : (N:ℝ) ^ (2*β) / 32 ≤ ((N:ℝ)/32) ^ (2*β) := by
          rw [Real.div_rpow hX0.le (by norm_num)]
          have h3 : (32:ℝ) ^ (2*β) ≤ 32 := by
            calc (32:ℝ) ^ (2*β) ≤ (32:ℝ) ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 32 := Real.rpow_one 32
          have h4 : (0:ℝ) < (32:ℝ) ^ (2*β) := Real.rpow_pos_of_pos (by norm_num) _
          gcongr
        linarith
      have hcosh : (n:ℝ) ^ (2*β) / 2 ≤ Real.cosh (2 * α * Real.log n) := by
        have := cosh_ge_half_rpow (α := α) (n := n) hn1'
        rwa [← hβ_def] at this
      have hΛ := vonMangoldt_nonneg (n := n)
      rw [coshVonMangoldt]
      have hstep : (N:ℝ) ^ (2*β) / 64 ≤ Real.cosh (2 * α * Real.log n) := by linarith
      exact mul_le_mul_of_nonneg_left hstep hΛ
    calc P / 2048 = ((N:ℝ) ^ (2*β) / 64) * ((N:ℝ)/32) := by rw [hP_def]; ring
      _ ≤ ((N:ℝ) ^ (2*β) / 64) * (∑ n ∈ Ioc M₃ M₂, Λ n) := by
          apply mul_le_mul_of_nonneg_left hmass₂ (by positivity)
      _ = ∑ n ∈ Ioc M₃ M₂, Λ n * ((N:ℝ) ^ (2*β) / 64) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ ∑ n ∈ Ioc M₃ M₂, coshVonMangoldt α n := Finset.sum_le_sum hterm
  -- the upper bound on the total mass
  have hS0up : twistedMoment N α 0 ≤ 5.4 * P := by
    rw [twistedMoment_zero]
    have hterm : ∀ n ∈ Icc 1 N, coshVonMangoldt α n ≤ Λ n * (N:ℝ) ^ (2*β) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
      have hnX : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn2
      have h1 : Real.cosh (2 * α * Real.log n) ≤ (n:ℝ) ^ (2*β) := by
        have := cosh_le_rpow (α := α) (n := n) hn1
        rwa [← hβ_def] at this
      have h2 : (n:ℝ) ^ (2*β) ≤ (N:ℝ) ^ (2*β) :=
        Real.rpow_le_rpow hn0.le hnX (by linarith)
      rw [coshVonMangoldt]
      exact mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg
    calc ∑ n ∈ Icc 1 N, coshVonMangoldt α n ≤ ∑ n ∈ Icc 1 N, Λ n * (N:ℝ) ^ (2*β) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Icc 1 N, Λ n) * (N:ℝ) ^ (2*β) := by rw [← Finset.sum_mul]
      _ ≤ ((Real.log 4 + 4) * (N:ℝ)) * (N:ℝ) ^ (2*β) := by
          apply mul_le_mul_of_nonneg_right _ hXb.le
          have h4 : ∑ n ∈ Icc 1 N, Λ n = ψ (N:ℝ) := by
            rw [Chebyshev.psi, Nat.floor_natCast, icc_one_eq_ioc_zero]
          rw [h4]
          exact Chebyshev.psi_le_const_mul_self hX0.le
      _ ≤ 5.4 * P := by
          have hlog4 : Real.log 4 + 4 ≤ 5.4 := by
            have h : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
            nlinarith [Real.log_two_lt_d9]
          rw [hP_def]
          nlinarith [hXb, hX0]
  -- separation of the two blocks in log-frequency
  have hsep : ∀ n ∈ Ioc M₁ N, ∀ m ∈ Ioc M₃ M₂, Real.log 2 ≤ |Real.log n - Real.log m| := by
    intro n hn m hm
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    have hn1' : 1 ≤ n := by omega
    have hm1' : 1 ≤ m := by omega
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1'
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm1'
    have hnlow : (N:ℝ)/4 ≤ (n:ℝ) := by
      have hfl : (N:ℝ)/4 < (M₁:ℝ) + 1 := Nat.lt_floor_add_one _
      have h5 : (M₁:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith
    have hmup : (m:ℝ) ≤ (N:ℝ)/8 := by
      have h5 : (m:ℝ) ≤ (M₂:ℝ) := by exact_mod_cast hm2
      have h6 : (M₂:ℝ) ≤ (N:ℝ)/8 := Nat.floor_le (by positivity)
      linarith
    have hlogn : Real.log ((N:ℝ)/4) ≤ Real.log n := Real.log_le_log (by positivity) hnlow
    have hlogm : Real.log m ≤ Real.log ((N:ℝ)/8) := Real.log_le_log hm0 hmup
    have hdiff : Real.log ((N:ℝ)/4) - Real.log ((N:ℝ)/8) = Real.log 2 := by
      rw [Real.log_div (ne_of_gt hX0) (by norm_num), Real.log_div (ne_of_gt hX0) (by norm_num),
        show (8:ℝ) = 4 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have : Real.log 2 ≤ Real.log n - Real.log m := by linarith
    calc Real.log 2 ≤ Real.log n - Real.log m := this
      _ ≤ |Real.log n - Real.log m| := le_abs_self _
  -- assemble
  have hsub₁ : Ioc M₁ N ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn2⟩
  have hsub₂ : Ioc M₃ M₂ ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hM₂N⟩
  have hlow := varForm_ge_blocks hsub₁ hsub₂ (coshVonMangoldt α) (fun n => Real.log n)
    (fun n _ => coshVonMangoldt_nonneg α n) (Real.log_nonneg (by norm_num)) hsep
  have hlog2 := Real.log_two_gt_d9
  have hlog2sq : (0.48 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
  have hV : (1/2) * ((P/32) * (P/2048) * 0.48) ≤
      twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2 := by
    have h2 : twistedMoment N α 2 = ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n) ^ 2 := rfl
    rw [twistedMoment_zero, twistedMoment_one, h2]
    refine le_trans ?_ hlow
    have hb₁ : 0 ≤ ∑ n ∈ Ioc M₁ N, coshVonMangoldt α n :=
      Finset.sum_nonneg fun n _ => coshVonMangoldt_nonneg α n
    have hb₂ : 0 ≤ ∑ n ∈ Ioc M₃ M₂, coshVonMangoldt α n :=
      Finset.sum_nonneg fun n _ => coshVonMangoldt_nonneg α n
    have hstep : (P/32) * (P/2048) * 0.48
        ≤ (∑ n ∈ Ioc M₁ N, coshVonMangoldt α n) * (∑ m ∈ Ioc M₃ M₂, coshVonMangoldt α m)
            * (Real.log 2) ^ 2 := by
      have hmul : (P/32) * (P/2048)
          ≤ (∑ n ∈ Ioc M₁ N, coshVonMangoldt α n) * (∑ m ∈ Ioc M₃ M₂, coshVonMangoldt α m) :=
        mul_le_mul hblock₁ hblock₂ (by positivity) hb₁
      calc (P/32) * (P/2048) * 0.48
          ≤ ((∑ n ∈ Ioc M₁ N, coshVonMangoldt α n)
              * (∑ m ∈ Ioc M₃ M₂, coshVonMangoldt α m)) * 0.48 :=
            mul_le_mul_of_nonneg_right hmul (by norm_num)
        _ ≤ ((∑ n ∈ Ioc M₁ N, coshVonMangoldt α n)
              * (∑ m ∈ Ioc M₃ M₂, coshVonMangoldt α m)) * (Real.log 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hlog2sq (mul_nonneg hb₁ hb₂)
    linarith
  have hS0nn : 0 ≤ twistedMoment N α 0 := by
    rw [twistedMoment_zero]
    exact Finset.sum_nonneg fun n _ => coshVonMangoldt_nonneg α n
  have hid : (1/2 : ℝ) * ((P/32) * (P/2048) * 0.48) = (0.48/131072) * P ^ 2 := by ring
  have hVQ : (3.6e-6 : ℝ) * P ^ 2 ≤
      twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2 := by
    have hstep : (3.6e-6 : ℝ) * P ^ 2 ≤ (0.48/131072) * P ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg P)
    linarith [hV, hid]
  have hsq : (twistedMoment N α 0) ^ 2 ≤ 29.16 * P ^ 2 := by
    calc (twistedMoment N α 0) ^ 2 = twistedMoment N α 0 * twistedMoment N α 0 := by ring
      _ ≤ (5.4 * P) * (5.4 * P) := mul_self_le_mul_self hS0nn hS0up
      _ = 29.16 * P ^ 2 := by ring
  linarith [hVQ, hsq, sq_nonneg P]

end RiemannAnalytic
