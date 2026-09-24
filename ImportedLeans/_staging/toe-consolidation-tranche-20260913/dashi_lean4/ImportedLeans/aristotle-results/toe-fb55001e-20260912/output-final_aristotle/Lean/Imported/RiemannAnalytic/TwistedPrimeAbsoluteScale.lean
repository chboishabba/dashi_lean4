import RiemannAnalytic.TwistedPrimeVarianceLower
import RiemannAnalytic.TwistedPrimeMassMean

/-!
# The absolute scale of the twisted prime variance

The relative results of `TwistedPrimeMoments` and `TwistedPrimeVarianceLower` say that
`S₀S₂ - S₁²` is comparable to `S₀²` with absolute constants.  Combined with the mass
estimate `twistedPrimeMass` (`S₀ ≍ N^{1+2|α|}`) this determines the *absolute* size of
the twisted prime variance, and that answer is decisive for the programme:

`α²(S₀S₂ - S₁²) ≍ α² N^{2+4|α|}`,

which is polynomially large in `N` and therefore **not** `o((log N)⁶)` on the nose.

The consequence recorded here is `alphaSq_twistedPrimeVariance_not_littleO`: for any
fixed off-line displacement `α ≠ 0` and any constant `C`, eventually in `N`

`C·(log N)⁶ ≤ α²(S₀S₂ - S₁²)`.

So the target `α² V_prime ≤ δ(T,H)² L⁶` cannot hold for the *unnormalized* literal
von Mangoldt moments.  It can only be reached after the source normalization that
divides the prime term by the twisted mass (or an equivalent factor of size `S₀²`); it
is exactly the relative statement `zetaTwistedPrimeCenteredVariance` that survives, and
`zetaTwistedPrimeVariance_lower` shows that even the relative constant cannot be made to
tend to zero.  Any contraction therefore has to be supplied by the source normalization
of `S₀` against `L³`, and not by the shape of the twisted prime measure.

Main results.

* `alphaSq_twistedPrimeVariance_ge` : `α²N²/(10⁷·1024) ≤ α²(S₀S₂ - S₁²)`.
* `alphaSq_twistedPrimeVariance_not_littleO` : the `o(L⁶)` target fails at absolute scale.
-/

open Finset Real ArithmeticFunction Chebyshev

namespace RiemannAnalytic

/-- The twisted prime variance is at least a fixed multiple of `N²`, uniformly in the
twist. -/
theorem alphaSq_twistedPrimeVariance_ge {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) :
    α ^ 2 * ((N : ℝ) ^ 2 / (10 ^ 7 * 1024))
      ≤ α ^ 2 * (twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2) := by
  have hN8 : (10 : ℝ) ^ 8 ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hmass := (twistedPrimeMass hN8 hα).1
  have hpow : (N:ℝ) ≤ (N:ℝ) ^ (1 + 2 * |α|) := by
    have h1 : (N:ℝ) ^ (1:ℝ) ≤ (N:ℝ) ^ (1 + 2 * |α|) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg α])
    rwa [Real.rpow_one] at h1
  have hS0 : (N:ℝ) / 32 ≤ twistedMoment N α 0 := by linarith
  have hS0nn : (0:ℝ) ≤ (N:ℝ) / 32 := by linarith
  have hsq : (N:ℝ) ^ 2 / 1024 ≤ (twistedMoment N α 0) ^ 2 := by
    calc (N:ℝ) ^ 2 / 1024 = ((N:ℝ) / 32) * ((N:ℝ) / 32) := by ring
      _ ≤ twistedMoment N α 0 * twistedMoment N α 0 := mul_self_le_mul_self hS0nn hS0
      _ = (twistedMoment N α 0) ^ 2 := by ring
  have hlow := zetaTwistedPrimeVariance_lower hN hα
  have hstep : (N:ℝ) ^ 2 / (10 ^ 7 * 1024)
      ≤ twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2 := by
    have : (N:ℝ) ^ 2 / (10 ^ 7 * 1024) ≤ (1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 7)
      calc (N:ℝ) ^ 2 / (10 ^ 7 * 1024) = (1 / 10 ^ 7 : ℝ) * ((N:ℝ) ^ 2 / 1024) := by ring
        _ ≤ (1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2 := h
    linarith
  exact mul_le_mul_of_nonneg_left hstep (sq_nonneg α)

/-- **The `o(L⁶)` target fails at absolute scale.**  For every fixed off-line displacement
`α ≠ 0` and every constant `C`, eventually in `N` we have
`C(log N)⁶ ≤ α²(S₀S₂ - S₁²)` for the unnormalized literal von Mangoldt moments.  Hence the
source-scale statement `α² V_prime ≤ δ(T,H)² L⁶` is only available in the normalized
(relative-to-`S₀²`) form. -/
theorem alphaSq_twistedPrimeVariance_not_littleO {α : ℝ} (hα0 : α ≠ 0) (hα : |α| < 1 / 2)
    (C : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      C * (Real.log N) ^ 6
        ≤ α ^ 2 * (twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2) := by
  set κ : ℝ := α ^ 2 / (10 ^ 7 * 1024) with hκ
  have hκ0 : 0 < κ := by
    have : 0 < α ^ 2 := by positivity
    rw [hκ]; positivity
  have hC0 : (0:ℝ) < |C| + 1 := by positivity
  -- `(log x)⁶ = o(x)`
  have hlim : Filter.Tendsto (fun x : ℝ => Real.log x ^ 6 / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hlim' : Filter.Tendsto (fun N : ℕ => Real.log N ^ 6 / (1 * (N:ℝ) + 0))
      Filter.atTop (nhds 0) := hlim.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      Real.log N ^ 6 / (1 * (N:ℝ) + 0) < κ / (|C| + 1) := by
    have := hlim'.eventually (eventually_lt_nhds (show (0:ℝ) < κ / (|C| + 1) by positivity))
    simpa using this
  have hbig : ∀ᶠ N : ℕ in Filter.atTop, (10:ℝ) ^ 9 ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev, hbig] with N hev hbig
  have hN0 : (0:ℝ) < (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 9]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 9]
  have hlogpow : (0:ℝ) ≤ Real.log N ^ 6 := by positivity
  -- turn the eventual bound into a linear statement
  have hlin : Real.log N ^ 6 < (κ / (|C| + 1)) * (N:ℝ) := by
    have h1 : Real.log N ^ 6 / (N:ℝ) < κ / (|C| + 1) := by
      simpa using hev
    have := (div_lt_iff₀ hN0).mp h1
    linarith
  have hCle : C * Real.log N ^ 6 ≤ (|C| + 1) * Real.log N ^ 6 := by
    have : C ≤ |C| + 1 := by linarith [le_abs_self C]
    exact mul_le_mul_of_nonneg_right this hlogpow
  have hkey : (|C| + 1) * Real.log N ^ 6 < κ * (N:ℝ) := by
    have := mul_lt_mul_of_pos_left hlin hC0
    calc (|C| + 1) * Real.log N ^ 6 < (|C| + 1) * ((κ / (|C| + 1)) * (N:ℝ)) := this
      _ = κ * (N:ℝ) := by field_simp
  have hNN : κ * (N:ℝ) ≤ κ * (N:ℝ) ^ 2 := by
    have : (N:ℝ) ≤ (N:ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hκ0.le
  have hmain := alphaSq_twistedPrimeVariance_ge hbig hα
  have hid : α ^ 2 * ((N : ℝ) ^ 2 / (10 ^ 7 * 1024)) = κ * (N:ℝ) ^ 2 := by
    rw [hκ]; ring
  linarith [hmain, hid.symm.le, hid.le]

end RiemannAnalytic
