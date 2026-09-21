import Synthesis.RiemannNormalizedCanonicalFixedProfile
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-!
# Normalized atomic carrier for the radius-zero Off channel

The exact projective decomposition contains one base term

  C(0) [A0(r)-A0(2r)].

The existing normalized H2 machinery covered centered radius differences.  This
file pays the remaining radius-zero representation seam on the literal zero
carrier.

For an actual zeta zero rho define

  B_t(rho)
    = m_rho * integral
        4 G_t(v)
          cosh((a_rho/t)v)
          cos(((gamma_rho-t)/t)v) dv,

where G_t is the exact fixed normalized canonical taper.

Then for t>=18,

  Z_rho(g_t,t,0) + Z_Rrho(g_t,t,0)
    = (1/t) B_t(rho).

Consequently every finite literal radius-zero Off aggregate is exactly the
corresponding normalized atomic sum.  No absolute value or surrogate zero
measure is introduced.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def normalizedRadiusZeroZeroAtom (t : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) *
    ∫ v : ℝ,
      4 * normalizedCanonicalFixedProfile t v
        * Real.cosh ((heightOf rho / t) * v)
        * Real.cos ((((rho : ℂ).im - t) / t) * v)

theorem reflectionPairWeight_canonical_radiusZero_normalized
    {t a delta v : ℝ} (ht : 0 < t) :
    reflectionPairWeight
        (quantitativeCanonicalTaper t)
        a delta (v / t)
      =
    4 * normalizedCanonicalFixedProfile t v
      * Real.cosh ((a / t) * v)
      * Real.cos ((delta / t) * v) := by
  unfold reflectionPairWeight
  rw [normalized_cosh_argument (ne_of_gt ht),
      normalized_cos_argument (ne_of_gt ht)]
  have hg :
      quantitativeCanonicalTaper t (v / t)
        = normalizedCanonicalFixedProfile t v := by
    rw [← normalizedCanonicalTaper_eq_fixedProfile ht]
    rfl
  rw [hg]

theorem integral_reflectionPairWeight_canonical_radiusZero_normalized
    {t a delta : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      reflectionPairWeight
        (quantitativeCanonicalTaper t)
        a delta u)
      =
    (1 / t) *
      ∫ v : ℝ,
        4 * normalizedCanonicalFixedProfile t v
          * Real.cosh ((a / t) * v)
          * Real.cos ((delta / t) * v) := by
  let F : ℝ → ℝ :=
    fun v =>
      4 * normalizedCanonicalFixedProfile t v
        * Real.cosh ((a / t) * v)
        * Real.cos ((delta / t) * v)
  have hpoint :
      (fun u : ℝ =>
        reflectionPairWeight
          (quantitativeCanonicalTaper t)
          a delta u)
        =
      fun u : ℝ => F (t * u) := by
    funext u
    dsimp [F]
    have htne : t ≠ 0 := ne_of_gt ht
    have htu : (t * u) / t = u := by
      field_simp [htne]
    rw [← htu]
    exact reflectionPairWeight_canonical_radiusZero_normalized ht
  rw [hpoint]
  have hscale :=
    Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1 / t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  simpa [habs, smul_eq_mul] using hscale

theorem literal_radiusZero_pair_eq_one_div_t_mul_normalizedAtom
    {t : ℝ} (ht : 18 <= t) (rho : Zeros) :
    zeroConeValue
        (quantitativeCanonicalTaper t)
        t 0 rho
      +
    zeroConeValue
        (quantitativeCanonicalTaper t)
        t 0 (reflectZero rho)
      =
    (1 / t) * normalizedRadiusZeroZeroAtom t rho := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hpair :=
    zeroConeValue_add_reflect_eq_integral
      (quantitativeCanonicalTaper_contDiff ht).continuous
      (quantitativeCanonicalTaper_compact ht)
      (quantitativeCanonicalTaper_even (t := t))
      t 0 rho
  simp only [zero_mul, Real.cos_zero, mul_one] at hpair
  rw [hpair]
  rw [integral_reflectionPairWeight_canonical_radiusZero_normalized
    (t := t) (a := heightOf rho) (delta := (rho : ℂ).im - t) ht0]
  unfold normalizedRadiusZeroZeroAtom
  ring

theorem sum_literal_radiusZero_pairs_eq_normalizedAtoms
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    (∑ rho ∈ F,
      (zeroConeValue
          (quantitativeCanonicalTaper t)
          t 0 rho
        +
       zeroConeValue
          (quantitativeCanonicalTaper t)
          t 0 (reflectZero rho)))
      =
    (1 / t) * ∑ rho ∈ F, normalizedRadiusZeroZeroAtom t rho := by
  classical
  calc
    (∑ rho ∈ F,
      (zeroConeValue
          (quantitativeCanonicalTaper t)
          t 0 rho
        +
       zeroConeValue
          (quantitativeCanonicalTaper t)
          t 0 (reflectZero rho)))
      =
      ∑ rho ∈ F, (1 / t) * normalizedRadiusZeroZeroAtom t rho := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact literal_radiusZero_pair_eq_one_div_t_mul_normalizedAtom ht rho
    _ = (1 / t) * ∑ rho ∈ F, normalizedRadiusZeroZeroAtom t rho := by
      rw [Finset.mul_sum]

end Synthesis
