import RiemannAnalytic.TwistedPrimeMoments

/-!
# Twisted prime mass and mean log-frequency

This module supplies the two remaining moment estimates of the twisted prime
package, both uniform in the twist parameter over the whole off-line range
`|α| < 1/2` and stated for the literal von Mangoldt weights.

* `tiltedMass_upper` : `∑_{n ≤ N} Λ n · n^v ≤ 5.4 · N^{1+v}` for `v ≥ 0`.
* `vonMangoldt_uniformExponentialTilt` : the two-sided master tilt estimate
  `N^{1+v}/16 ≤ ∑_{n ≤ N} Λ n · n^v ≤ 5.4 · N^{1+v}` for `0 ≤ v ≤ 1`, `N ≥ 10⁸`.
* `twistedPrimeMass` : the corresponding two-sided estimate for the literal
  cosh-twisted mass `S₀(α)`, namely `N^{1+2|α|}/32 ≤ S₀(α) ≤ 5.4 · N^{1+2|α|}`.
* `twistedPrimeMeanLog` : the first-moment theorem
  `|S₁(α) - (log N)·S₀(α)| ≤ 123 · S₀(α)`, i.e. the mean log-frequency of the
  twisted prime measure is `log N + O(1)`, uniformly in `α`.

Together with `zetaTwistedPrimeCenteredVariance` (upper bound on the centered
second moment) and `zetaTwistedPrimeVariance_lower` these pin down the twisted
prime measure at the level of its first three moments: it is a measure of total
mass `≍ N^{1+2|α|}` supported in a log-window of width `Θ(1)` about `log N`.
-/

open Finset Real ArithmeticFunction Chebyshev

namespace RiemannAnalytic

private lemma icc_one_eq_ioc_zero'' (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N :=
  Finset.val_inj.mp rfl

private lemma psi_sum_eq (N : ℕ) : ∑ n ∈ Icc 1 N, Λ n = ψ (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast, icc_one_eq_ioc_zero'']

/-- The upper half of the master tilt estimate: for a nonnegative tilt the mass is at
most an absolute constant times `N^{1+v}`. -/
theorem tiltedMass_upper {N : ℕ} (hN : (0 : ℝ) < (N : ℝ)) {v : ℝ} (hv : 0 ≤ v) :
    tiltedMass N v ≤ 5.4 * (N : ℝ) ^ (1 + v) := by
  have hterm : ∀ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ v ≤ Λ n * (N : ℝ) ^ v := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hnN : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn2
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0 hnN hv) vonMangoldt_nonneg
  have hV : (0:ℝ) < (N:ℝ) ^ v := Real.rpow_pos_of_pos hN v
  have hsplit : (N:ℝ) ^ (1 + v) = (N:ℝ) * (N:ℝ) ^ v := by
    rw [Real.rpow_add hN, Real.rpow_one]
  calc tiltedMass N v ≤ ∑ n ∈ Icc 1 N, Λ n * (N : ℝ) ^ v := Finset.sum_le_sum hterm
    _ = (∑ n ∈ Icc 1 N, Λ n) * (N : ℝ) ^ v := by rw [← Finset.sum_mul]
    _ ≤ ((Real.log 4 + 4) * (N:ℝ)) * (N:ℝ) ^ v := by
        refine mul_le_mul_of_nonneg_right ?_ hV.le
        rw [psi_sum_eq]
        exact Chebyshev.psi_le_const_mul_self hN.le
    _ ≤ 5.4 * ((N:ℝ) * (N:ℝ) ^ v) := by
        have hlog4 : Real.log 4 + 4 ≤ 5.4 := by
          have h : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
          nlinarith [Real.log_two_lt_d9]
        have hprod : (0:ℝ) ≤ (N:ℝ) * (N:ℝ) ^ v := (mul_pos hN hV).le
        calc (Real.log 4 + 4) * (N:ℝ) * (N:ℝ) ^ v
            = (Real.log 4 + 4) * ((N:ℝ) * (N:ℝ) ^ v) := by ring
          _ ≤ 5.4 * ((N:ℝ) * (N:ℝ) ^ v) := mul_le_mul_of_nonneg_right hlog4 hprod
    _ = 5.4 * (N : ℝ) ^ (1 + v) := by rw [hsplit]

/-- **The uniform exponential-tilt master estimate for von Mangoldt weights.**
For every tilt `0 ≤ v ≤ 1` and every `N ≥ 10⁸`, the tilted prime mass is comparable to
`N^{1+v}`, with absolute constants and no dependence on `v`. -/
theorem vonMangoldt_uniformExponentialTilt {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (N : ℝ) ^ (1 + v) / 16 ≤ tiltedMass N v ∧ tiltedMass N v ≤ 5.4 * (N : ℝ) ^ (1 + v) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  exact ⟨tiltedMass_lower hN (by rw [abs_of_nonneg hv0]; exact hv1),
    tiltedMass_upper hN0 hv0⟩

private lemma cosh_le_rpow_abs {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    Real.cosh (2 * α * Real.log n) ≤ (n : ℝ) ^ (2 * |α|) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have habs : Real.cosh (2 * α * Real.log n) = Real.cosh (2 * |α| * Real.log n) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -α * Real.log n = -(2 * α * Real.log n) by ring, Real.cosh_neg]
  rw [habs, Real.cosh_eq, Real.rpow_def_of_pos hn0,
    show Real.log n * (2 * |α|) = 2 * |α| * Real.log n by ring]
  have h1 : Real.exp (-(2 * |α| * Real.log n)) ≤ Real.exp (2 * |α| * Real.log n) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg α])
  linarith

private lemma cosh_ge_half_rpow_abs {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 * |α|) / 2 ≤ Real.cosh (2 * α * Real.log n) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have habs : Real.cosh (2 * α * Real.log n) = Real.cosh (2 * |α| * Real.log n) := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * -α * Real.log n = -(2 * α * Real.log n) by ring, Real.cosh_neg]
  rw [habs, Real.cosh_eq, Real.rpow_def_of_pos hn0,
    show Real.log n * (2 * |α|) = 2 * |α| * Real.log n by ring]
  have := Real.exp_pos (-(2 * |α| * Real.log n))
  linarith

/-- **The twisted prime mass estimate** (`S₀`), uniform over the whole off-line range.
For every `N ≥ 10⁸` and every `|α| < 1/2` the literal cosh-twisted von Mangoldt mass
satisfies `N^{1+2|α|}/32 ≤ S₀(α) ≤ 5.4 · N^{1+2|α|}`. -/
theorem twistedPrimeMass {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {α : ℝ} (hα : |α| < 1 / 2) :
    (N : ℝ) ^ (1 + 2 * |α|) / 32 ≤ twistedMoment N α 0 ∧
      twistedMoment N α 0 ≤ 5.4 * (N : ℝ) ^ (1 + 2 * |α|) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hβ0 : (0:ℝ) ≤ 2 * |α| := by positivity
  have hβ1 : 2 * |α| ≤ 1 := by linarith [hα]
  rw [twistedMoment_zero]
  constructor
  · -- lower bound: keep only the positive tilt, which is at least half the cosh
    have hterm : ∀ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (2 * |α|) / 2 ≤ coshVonMangoldt α n := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have := cosh_ge_half_rpow_abs (α := α) (n := n) hn1
      have hΛ : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
      rw [coshVonMangoldt]
      nlinarith [this, hΛ]
    have hsum : tiltedMass N (2 * |α|) / 2 ≤ ∑ n ∈ Icc 1 N, coshVonMangoldt α n := by
      rw [tiltedMass, Finset.sum_div]
      exact Finset.sum_le_sum hterm
    have hlow := tiltedMass_lower hN (v := 2 * |α|) (by rw [abs_of_nonneg hβ0]; exact hβ1)
    linarith
  · have hterm : ∀ n ∈ Icc 1 N, coshVonMangoldt α n ≤ Λ n * (n : ℝ) ^ (2 * |α|) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact mul_le_mul_of_nonneg_left (cosh_le_rpow_abs (α := α) (n := n) hn1) vonMangoldt_nonneg
    calc ∑ n ∈ Icc 1 N, coshVonMangoldt α n ≤ tiltedMass N (2 * |α|) :=
          Finset.sum_le_sum hterm
      _ ≤ 5.4 * (N : ℝ) ^ (1 + 2 * |α|) := tiltedMass_upper hN0 hβ0

/-- **The twisted prime first-moment theorem.**  The mean log-frequency of the literal
cosh-twisted von Mangoldt measure is `log N` up to an absolute additive constant,
uniformly for every off-line displacement `|α| < 1/2` and every `N ≥ 10⁸`:
`|S₁(α) - (log N)·S₀(α)| ≤ 123 · S₀(α)`. -/
theorem twistedPrimeMeanLog {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {α : ℝ} (hα : |α| < 1 / 2) :
    |twistedMoment N α 1 - Real.log N * twistedMoment N α 0| ≤ 123 * twistedMoment N α 0 := by
  have hS0nn : 0 ≤ ∑ n ∈ Icc 1 N, coshVonMangoldt α n :=
    Finset.sum_nonneg fun n _ => coshVonMangoldt_nonneg α n
  have hcent := vonMangoldt_twistedCentered_le_mass hN hα
  have hdiff : twistedMoment N α 1 - Real.log N * twistedMoment N α 0
      = ∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n - Real.log N) := by
    rw [twistedMoment_one, twistedMoment_zero, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- pointwise AM-GM with the optimal scale `t = 123`
  have hpt : ∀ n ∈ Icc 1 N, |coshVonMangoldt α n * (Real.log n - Real.log N)|
      ≤ coshVonMangoldt α n * (Real.log n - Real.log N) ^ 2 / 246
        + coshVonMangoldt α n * (123 / 2) := by
    intro n _
    set w : ℝ := coshVonMangoldt α n with hw
    set d : ℝ := Real.log n - Real.log N with hd
    have hwnn : 0 ≤ w := coshVonMangoldt_nonneg α n
    have habs : |w * d| = w * |d| := by
      rw [abs_mul, abs_of_nonneg hwnn]
    rw [habs]
    have hkey : |d| ≤ d ^ 2 / 246 + 123 / 2 := by
      nlinarith [sq_nonneg (|d| - 123), sq_abs d, abs_nonneg d]
    nlinarith [hkey, hwnn]
  have hbound : |∑ n ∈ Icc 1 N, coshVonMangoldt α n * (Real.log n - Real.log N)|
      ≤ ∑ n ∈ Icc 1 N, (coshVonMangoldt α n * (Real.log n - Real.log N) ^ 2 / 246
          + coshVonMangoldt α n * (123 / 2)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hpt)
  rw [hdiff]
  refine le_trans hbound ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  rw [twistedMoment_zero]
  linarith [hcent]

end RiemannAnalytic
