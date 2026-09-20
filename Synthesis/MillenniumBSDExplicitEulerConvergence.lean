import Synthesis.MillenniumBSDExplicitLocalRecurrence
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Absolute convergence of the explicit Euler perturbation for Re(s) > 2

For every good odd prime the direct point-count Euler denominator is

  1 - a_p p^{-s} + p p^{-2s}.

The previous file proves the literal bound |a_p| <= p.  Therefore the norm of
the nonconstant part is bounded by

  p^(1-Re(s)) + p^(1-2 Re(s)).

Both prime sums converge whenever Re(s) > 2.  We set the bad p=2 perturbation
to zero, matching the additive local factor 1 for E : y² = x³ - x.

This gives an actual absolute-convergence theorem for the primewise Euler
perturbations, without assuming Hasse or CM normalization.
-/

namespace Synthesis.Millennium.BSD

def explicitEulerPerturbation
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  if hp2 : p.1 = 2 then
    0
  else
    letI : Fact p.1.Prime := ⟨p.2⟩
    - (frobeniusCoefficient p.1 : ℂ) * (p.1 : ℂ) ^ (-s)
      + (p.1 : ℂ) * (p.1 : ℂ) ^ (-(2 : ℂ) * s)

def explicitEulerDenominator
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 + explicitEulerPerturbation p s

theorem explicitEulerDenominator_eq_pointCountFactor
    (p : Nat.Primes) (s : ℂ)
    (hp2 : p.1 ≠ 2) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    explicitEulerDenominator p s =
      1
      - (frobeniusCoefficient p.1 : ℂ) * (p.1 : ℂ) ^ (-s)
      + (p.1 : ℂ) * (p.1 : ℂ) ^ (-(2 : ℂ) * s) := by
  simp [explicitEulerDenominator, explicitEulerPerturbation, hp2]
  ring

theorem explicitEulerMajorant_summable
    {s : ℂ} (hs : 2 < s.re) :
    Summable fun p : Nat.Primes =>
      (p.1 : ℝ) ^ (1 - s.re)
      + (p.1 : ℝ) ^ (1 - 2 * s.re) := by
  apply Summable.add
  · exact Nat.Primes.summable_rpow.mpr (by linarith)
  · exact Nat.Primes.summable_rpow.mpr (by linarith)

theorem explicitEulerPerturbation_norm_le_majorant
    {s : ℂ} (hs : 2 < s.re)
    (p : Nat.Primes) :
    ‖explicitEulerPerturbation p s‖
      ≤ (p.1 : ℝ) ^ (1 - s.re)
        + (p.1 : ℝ) ^ (1 - 2 * s.re) := by
  by_cases hp2 : p.1 = 2
  · simp [explicitEulerPerturbation, hp2]
    positivity
  · letI : Fact p.1.Prime := ⟨p.2⟩
    have hpR : 0 < (p.1 : ℝ) := by positivity
    have hcoefZ :
        |frobeniusCoefficient p.1| ≤ (p.1 : ℤ) :=
      frobeniusCoefficient_abs_le_prime hp2
    have hcoef :
        ‖(frobeniusCoefficient p.1 : ℂ)‖ ≤ (p.1 : ℝ) := by
      rw [Complex.norm_intCast]
      exact_mod_cast hcoefZ
    have hpow1 :
        ‖(p.1 : ℂ) ^ (-s)‖ =
          (p.1 : ℝ) ^ (-s.re) := by
      simpa using
        (norm_natCast_cpow_of_pos p.2.pos (-s))
    have hpow2 :
        ‖(p.1 : ℂ) ^ (-(2 : ℂ) * s)‖ =
          (p.1 : ℝ) ^ (-2 * s.re) := by
      simpa using
        (norm_natCast_cpow_of_pos p.2.pos (-(2 : ℂ) * s))
    have hrpow1 :
        (p.1 : ℝ) * (p.1 : ℝ) ^ (-s.re)
          = (p.1 : ℝ) ^ (1 - s.re) := by
      calc
        (p.1 : ℝ) * (p.1 : ℝ) ^ (-s.re)
            = (p.1 : ℝ) ^ (1 : ℝ)
                * (p.1 : ℝ) ^ (-s.re) := by
                  rw [Real.rpow_one]
        _ = (p.1 : ℝ) ^ ((1 : ℝ) + (-s.re)) := by
              rw [← Real.rpow_add hpR]
        _ = (p.1 : ℝ) ^ (1 - s.re) := by ring_nf
    have hrpow2 :
        (p.1 : ℝ) * (p.1 : ℝ) ^ (-2 * s.re)
          = (p.1 : ℝ) ^ (1 - 2 * s.re) := by
      calc
        (p.1 : ℝ) * (p.1 : ℝ) ^ (-2 * s.re)
            = (p.1 : ℝ) ^ (1 : ℝ)
                * (p.1 : ℝ) ^ (-2 * s.re) := by
                  rw [Real.rpow_one]
        _ = (p.1 : ℝ) ^ ((1 : ℝ) + (-2 * s.re)) := by
              rw [← Real.rpow_add hpR]
        _ = (p.1 : ℝ) ^ (1 - 2 * s.re) := by ring_nf
    rw [explicitEulerPerturbation, dif_neg hp2]
    calc
      ‖-(frobeniusCoefficient p.1 : ℂ) * (p.1 : ℂ) ^ (-s)
          + (p.1 : ℂ) * (p.1 : ℂ) ^ (-(2 : ℂ) * s)‖
          ≤ ‖(frobeniusCoefficient p.1 : ℂ)‖
              * ‖(p.1 : ℂ) ^ (-s)‖
            + ‖(p.1 : ℂ)‖
              * ‖(p.1 : ℂ) ^ (-(2 : ℂ) * s)‖ := by
                simpa [norm_mul] using
                  norm_add_le
                    (-(frobeniusCoefficient p.1 : ℂ)
                      * (p.1 : ℂ) ^ (-s))
                    ((p.1 : ℂ)
                      * (p.1 : ℂ) ^ (-(2 : ℂ) * s))
      _ ≤ (p.1 : ℝ) * ‖(p.1 : ℂ) ^ (-s)‖
            + (p.1 : ℝ)
              * ‖(p.1 : ℂ) ^ (-(2 : ℂ) * s)‖ := by
              gcongr
      _ = (p.1 : ℝ) ^ (1 - s.re)
            + (p.1 : ℝ) ^ (1 - 2 * s.re) := by
              rw [hpow1, hpow2, hrpow1, hrpow2]

theorem explicitEulerPerturbation_summable
    {s : ℂ} (hs : 2 < s.re) :
    Summable fun p : Nat.Primes =>
      explicitEulerPerturbation p s := by
  have hmajor := explicitEulerMajorant_summable hs
  exact
    (hmajor.of_nonneg_of_le
      (fun p => norm_nonneg (explicitEulerPerturbation p s))
      (explicitEulerPerturbation_norm_le_majorant hs)).of_norm

end Synthesis.Millennium.BSD
