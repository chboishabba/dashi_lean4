import Synthesis.RiemannNormalizedCenteredOffAtomicMeasure
import Synthesis.RiemannNormalizedCenteredProfileSpectralGap

/-!
# Exact horizontal-height split of the normalized Off spectral atom

The normalized reflection-pair atom still depends on the horizontal zero height
through

  cosh((a_rho/t) v).

To obtain a genuine one-dimensional Stieltjes pairing in the normalized
ordinate gap q=(gamma-t)/t, split exactly

  cosh(alpha v) = 1 + (cosh(alpha v)-1).

The first term defines the common base transform

  Phi_t(q) = integral 4 H_t(v) cos(qv) dv,

which depends only on q and therefore pairs directly with the zero-counting
measure.  The second term is a horizontal-strip correction

  E_t(alpha,q)
    = integral 4 H_t(v) (cosh(alpha v)-1) cos(qv) dv.

For every actual zero,

  A_t(rho)
    = m_rho [ Phi_t(q_rho) + E_t(alpha_rho,q_rho) ].

Thus a finite literal aggregate splits exactly into a one-dimensional atomic
Stieltjes term plus a separate horizontal correction.  No estimate is used in
this file.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def normalizedCenteredBaseTransform (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfile t v * Real.cos (q * v)

def normalizedCenteredHorizontalCorrection (t alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfile t v
      * (Real.cosh (alpha * v) - 1)
      * Real.cos (q * v)

def normalizedGap (t : ℝ) (rho : Zeros) : ℝ :=
  ((rho : ℂ).im - t) / t

def normalizedHorizontalHeight (t : ℝ) (rho : Zeros) : ℝ :=
  heightOf rho / t

theorem integrable_normalizedCenteredBase
    (t q : ℝ) :
    Integrable
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v * Real.cos (q * v)) := by
  have hc : Continuous
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v * Real.cos (q * v)) := by
    exact (continuous_const.mul
      (normalizedCenteredFixedProfile_contDiff t).continuous).mul (by fun_prop)
  have hs : HasCompactSupport
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v * Real.cos (q * v)) := by
    exact (normalizedCenteredFixedProfile_compact t).mul_left.mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem integrable_normalizedCenteredHorizontalCorrection
    (t alpha q : ℝ) :
    Integrable
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)) := by
  have hc : Continuous
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)) := by
    exact ((continuous_const.mul
      (normalizedCenteredFixedProfile_contDiff t).continuous).mul
        (by fun_prop)).mul (by fun_prop)
  have hs : HasCompactSupport
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)) := by
    exact ((normalizedCenteredFixedProfile_compact t).mul_left.mul_right).mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem normalizedPairIntegral_eq_base_add_horizontal
    (t alpha q : ℝ) :
    (∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v
        * Real.cosh (alpha * v)
        * Real.cos (q * v))
      =
    normalizedCenteredBaseTransform t q
      + normalizedCenteredHorizontalCorrection t alpha q := by
  unfold normalizedCenteredBaseTransform normalizedCenteredHorizontalCorrection
  rw [← integral_add
    (integrable_normalizedCenteredBase t q)
    (integrable_normalizedCenteredHorizontalCorrection t alpha q)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by ring

theorem normalizedCenteredZeroAtom_eq_base_add_horizontal
    (t : ℝ) (rho : Zeros) :
    normalizedCenteredZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredBaseTransform t (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredHorizontalCorrection t
          (normalizedHorizontalHeight t rho)
          (normalizedGap t rho) := by
  unfold normalizedCenteredZeroAtom normalizedGap normalizedHorizontalHeight
  rw [normalizedPairIntegral_eq_base_add_horizontal]
  ring

def normalizedBaseAtomicAggregate
    (t : ℝ) (F : Finset Zeros) : ℝ :=
  ∑ rho ∈ F,
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredBaseTransform t (normalizedGap t rho)

def normalizedHorizontalAtomicAggregate
    (t : ℝ) (F : Finset Zeros) : ℝ :=
  ∑ rho ∈ F,
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredHorizontalCorrection t
          (normalizedHorizontalHeight t rho)
          (normalizedGap t rho)

theorem sum_normalizedCenteredZeroAtom_eq_base_add_horizontal
    (t : ℝ) (F : Finset Zeros) :
    (∑ rho ∈ F, normalizedCenteredZeroAtom t rho)
      =
    normalizedBaseAtomicAggregate t F
      + normalizedHorizontalAtomicAggregate t F := by
  classical
  unfold normalizedBaseAtomicAggregate normalizedHorizontalAtomicAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact normalizedCenteredZeroAtom_eq_base_add_horizontal t rho

/--
Exact finite literal centered-Off aggregate split:

  literal aggregate
    = (1/t) * [ one-dimensional q-aggregate + horizontal correction ].
-/
theorem sum_literal_centered_pairs_eq_base_plus_horizontal
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    (∑ rho ∈ F,
      (Zeta23Bridge.LiteralWeilParityBalance.zeroConeValue
          (Zeta23Bridge.LiteralWeilParityBalance.gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 rho
        +
       Zeta23Bridge.LiteralWeilParityBalance.zeroConeValue
          (Zeta23Bridge.LiteralWeilParityBalance.gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0 (reflectZero rho)))
      =
    (1 / t) *
      (normalizedBaseAtomicAggregate t F
        + normalizedHorizontalAtomicAggregate t F) := by
  rw [sum_literal_centered_pairs_eq_normalizedAtoms ht F,
      sum_normalizedCenteredZeroAtom_eq_base_add_horizontal]

end Synthesis
