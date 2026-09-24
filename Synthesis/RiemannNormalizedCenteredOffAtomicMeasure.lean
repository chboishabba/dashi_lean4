import Synthesis.RiemannNormalizedCenteredOffOscillatoryDecay
import Synthesis.RiemannQuantitativeGammaDeficit
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-!
# Literal normalized atomic spectral representation of the centered Off channel

This file turns the normalized per-pair theorem into an exact aggregate object on
the actual zeta zero carrier.

For t>0 and an actual zero rho, define the normalized spectral atom

  A_t(rho)
    = m_rho * integral
        4 H_t(v)
          cosh((a_rho/t) v)
          cos(((gamma_rho-t)/t) v) dv,

where H_t is the exact fixed-profile centered canonical taper.

Then the literal reflection-paired centered response is exactly

  Z_rho + Z_Rrho = (1/t) A_t(rho).

Consequently every finite aggregate of actual carrier points is exactly

  sum_F (Z_rho + Z_Rrho) = (1/t) sum_F A_t(rho).

This is the atomic normalized spectral-measure surface required before any
Stieltjes / summation-by-parts estimate.  Multiplicity, horizontal height and
the actual ordinate gaps are all retained.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def normalizedCenteredZeroAtom (t : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) *
    ∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v
        * Real.cosh ((heightOf rho / t) * v)
        * Real.cos ((((rho : ℂ).im - t) / t) * v)

theorem quantitativeCenteredCanonical_even
    {t : ℝ} :
    ∀ u,
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) (-u)
      =
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) u := by
  intro u
  unfold gammaCenteredTaper
  rw [quantitativeCanonicalTaper_even]
  simp [Real.cos_neg]

/--
The prize-facing range is t>=18, where all canonical taper regularity is already
owned.  This is the theorem consumed by aggregate H2.
-/
theorem literal_centered_pair_eq_one_div_t_mul_normalizedAtom_high
    {t : ℝ} (ht : 18 <= t) (rho : Zeros) :
    zeroConeValue
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        t 0 rho
      +
    zeroConeValue
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        t 0 (reflectZero rho)
      =
    (1 / t) * normalizedCenteredZeroAtom t rho := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hcenterC2 :=
    gammaCenteredTaper_contDiff
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeSampleRadius t)
  have hcenterCompact :=
    gammaCenteredTaper_hasCompactSupport
      (quantitativeCanonicalTaper_compact ht)
      (quantitativeSampleRadius t)
  have hpair :=
    zeroConeValue_add_reflect_eq_integral
      hcenterC2.continuous
      hcenterCompact
      quantitativeCenteredCanonical_even
      t 0 rho
  simp only [zero_mul, Real.cos_zero, mul_one] at hpair
  rw [hpair]
  have hnorm :=
    integral_reflectionPairWeight_centeredCanonical_normalized
      (t := t) (a := heightOf rho) (delta := (rho : ℂ).im - t) ht0
  rw [hnorm]
  unfold normalizedCenteredZeroAtom normalizedCenteredPairKernel
  have hint :
      (∫ v : ℝ,
        4 * normalizedCenteredCanonicalTaper t v
          * Real.cosh ((heightOf rho / t) * v)
          * Real.cos ((((rho : ℂ).im - t) / t) * v))
      =
      ∫ v : ℝ,
        4 * normalizedCenteredFixedProfile t v
          * Real.cosh ((heightOf rho / t) * v)
          * Real.cos ((((rho : ℂ).im - t) / t) * v) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      rw [normalizedCenteredCanonicalTaper_eq_fixedProfile ht0]
  rw [hint]
  ring

/--
Exact finite atomic spectral representation on the literal zero carrier.
No absolute value, zero-density bound, or surrogate counting measure appears.
-/
theorem sum_literal_centered_pairs_eq_normalizedAtoms
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    (∑ rho ∈ F,
      (zeroConeValue
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 rho
        +
       zeroConeValue
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 (reflectZero rho)))
      =
    (1 / t) * ∑ rho ∈ F, normalizedCenteredZeroAtom t rho := by
  classical
  calc
    (∑ rho ∈ F,
      (zeroConeValue
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 rho
        +
       zeroConeValue
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 (reflectZero rho)))
      =
      ∑ rho ∈ F, (1 / t) * normalizedCenteredZeroAtom t rho := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact literal_centered_pair_eq_one_div_t_mul_normalizedAtom_high ht rho
    _ = (1 / t) * ∑ rho ∈ F, normalizedCenteredZeroAtom t rho := by
      rw [Finset.mul_sum]

end Synthesis
