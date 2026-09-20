import Synthesis.RiemannProjectiveCenteredGaugeBridge
import Synthesis.RiemannNormalizedCenteredOffTwoRadius
import Synthesis.RiemannNormalizedOffRadiusZeroAtomicMeasure

/-!
# Literal normalized projective Off atom

The reflection-pair signed cutset consumes the two-radius projective Off defect,
not a one-radius centered response.  The gauge bridge has already decomposed
that projective observable into exactly three literal pieces:

  ΔC(2r) A0(r) - ΔC(r) A0(2r)
    + C(0) (A0(r)-A0(2r)).

For the canonical taper r=t/16, all three pieces now have exact normalized
representations on the actual zeta-zero carrier.

This file packages them into one per-reflection-pair projective atom.  It does
NOT identify the resulting finite sums with the whole off-ordinate tsum; that
remaining infinite-aggregate attachment is deliberately left explicit for the
RvM/Stieltjes tranche.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-- The normalized centered reflection-pair atom at an arbitrary integer-like
scale k of the canonical radius.  k=1 is r=t/16 and k=2 is 2r=t/8. -/
def normalizedCenteredZeroAtomAtScale
    (t k : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) *
    ∫ v : ℝ,
      normalizedCenteredPairKernelAtScale
        t k (heightOf rho) ((rho : ℂ).im - t) v

theorem quantitativeCenteredCanonicalAtScale_even
    {t k : ℝ} :
    ∀ u,
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (k * quantitativeSampleRadius t) (-u)
      =
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (k * quantitativeSampleRadius t) u := by
  intro u
  unfold gammaCenteredTaper
  rw [quantitativeCanonicalTaper_even]
  simp [Real.cos_neg]

/-- Exact normalized representation of one literal centered reflection pair at
either projective sampling radius (indeed, at any scale k). -/
theorem literal_centered_pair_atScale_eq_one_div_t_mul_normalizedAtom
    {t k : ℝ} (ht : 18 <= t) (rho : Zeros) :
    zeroConeValue
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t))
        t 0 rho
      +
    zeroConeValue
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t))
        t 0 (reflectZero rho)
      =
    (1 / t) * normalizedCenteredZeroAtomAtScale t k rho := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hcenterC2 :=
    gammaCenteredTaper_contDiff
      (quantitativeCanonicalTaper_contDiff ht)
      (k * quantitativeSampleRadius t)
  have hcenterCompact :=
    gammaCenteredTaper_hasCompactSupport
      (quantitativeCanonicalTaper_compact ht)
      (k * quantitativeSampleRadius t)
  have hpair :=
    zeroConeValue_add_reflect_eq_integral
      hcenterC2.continuous
      hcenterCompact
      quantitativeCenteredCanonicalAtScale_even
      t 0 rho
  simp only [zero_mul, Real.cos_zero, mul_one] at hpair
  rw [hpair]
  rw [integral_reflectionPairWeight_centeredCanonicalAtScale_normalized
    (t := t) (k := k) (a := heightOf rho)
    (delta := (rho : ℂ).im - t) ht0]
  unfold normalizedCenteredZeroAtomAtScale
  ring

theorem normalizedCenteredZeroAtomAtScale_one
    {t : ℝ} (rho : Zeros) :
    normalizedCenteredZeroAtomAtScale t 1 rho
      = normalizedCenteredZeroAtom t rho := by
  unfold normalizedCenteredZeroAtomAtScale normalizedCenteredZeroAtom
    normalizedCenteredPairKernelAtScale
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    rw [normalizedCenteredFixedProfileAtScale_one]
    rfl

/-- Radius channel of one reflection pair. -/
def literalPairRadiusChannel
    (g : ℝ → ℝ) (t : ℝ) (rho : Zeros) : ℝ → ℝ :=
  fun s =>
    zeroConeValue g t s rho
      + zeroConeValue g t s (reflectZero rho)

/-- Projective defect of one literal reflection pair against the on-line target
profile. -/
def literalPairProjectiveDefect
    (g : ℝ → ℝ) (t r : ℝ) (rho : Zeros) : ℝ :=
  channelProjectiveDefect (literalPairRadiusChannel g t rho) g r


/-- Radius-centering identity for one literal reflection pair, on the unrestricted
actual zero carrier. -/
theorem literalPairRadiusChannel_centered
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t s : ℝ) (rho : Zeros) :
    radiusCenteredChannel (literalPairRadiusChannel g t rho) s
      =
    zeroConeValue (gammaCenteredTaper g s) t 0 rho
      + zeroConeValue (gammaCenteredTaper g s) t 0 (reflectZero rho) := by
  have hs :=
    zeroConeValue_add_reflect_eq_integral
      hgs.continuous hgc heven t s rho
  have h0 :=
    zeroConeValue_add_reflect_eq_integral
      hgs.continuous hgc heven t 0 rho
  have hc2 := gammaCenteredTaper_contDiff hgs s
  have hcc := gammaCenteredTaper_hasCompactSupport hgc s
  have hce := gammaCenteredTaper_even heven s
  have hc :=
    zeroConeValue_add_reflect_eq_integral
      hc2.continuous hcc hce t 0 rho
  unfold radiusCenteredChannel literalPairRadiusChannel
  rw [hs, h0, hc]
  simp only [zero_mul, Real.cos_zero, mul_one]
  ring_nf
  congr 2
  apply integral_congr_ae
  filter_upwards with u
  unfold reflectionPairWeight gammaCenteredTaper
  ring

/-- The exact normalized per-pair projective atom. -/
def normalizedProjectiveOffZeroAtom
    (t : ℝ) (rho : Zeros) : ℝ :=
  normalizedCenteredZeroAtomAtScale t 2 rho
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
    - normalizedCenteredZeroAtomAtScale t 1 rho
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (2 * quantitativeSampleRadius t)
    + normalizedRadiusZeroZeroAtom t rho
      * (onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
          - onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t))

/--
Exact same-object bridge for one actual reflection pair:

  projective pair defect = (1/t) * normalized projective atom.

No absolute value, zero-density estimate, or projective/centered identification
is assumed: this is just the exact two-radius centered decomposition plus the
three already-proved normalized identities.
-/
theorem literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
    {t : ℝ} (ht : 18 <= t) (rho : Zeros) :
    literalPairProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) rho
      =
    (1 / t) * normalizedProjectiveOffZeroAtom t rho := by
  let g : ℝ → ℝ := quantitativeCanonicalTaper t
  let r : ℝ := quantitativeSampleRadius t
  let C : ℝ → ℝ := literalPairRadiusChannel g t rho

  have hgs : ContDiff ℝ 2 g := quantitativeCanonicalTaper_contDiff ht
  have hgc : HasCompactSupport g := quantitativeCanonicalTaper_compact ht
  have heven : ∀ u, g (-u) = g u :=
    quantitativeCanonicalTaper_even (t := t)

  have hcenter1 :=
    literal_centered_pair_atScale_eq_one_div_t_mul_normalizedAtom
      (t := t) (k := 1) ht rho
  have hcenter2 :=
    literal_centered_pair_atScale_eq_one_div_t_mul_normalizedAtom
      (t := t) (k := 2) ht rho
  have hbase :=
    literal_radiusZero_pair_eq_one_div_t_mul_normalizedAtom ht rho

  have hdelta1 :
      radiusCenteredChannel C r
        = (1 / t) * normalizedCenteredZeroAtomAtScale t 1 rho := by
    rw [literalPairRadiusChannel_centered hgs hgc heven t r rho]
    simpa [g, r] using hcenter1

  have hdelta2 :
      radiusCenteredChannel C (2*r)
        = (1 / t) * normalizedCenteredZeroAtomAtScale t 2 rho := by
    rw [literalPairRadiusChannel_centered hgs hgc heven t (2*r) rho]
    simpa [g, r, mul_assoc] using hcenter2

  have hC0 :
      C 0 = (1 / t) * normalizedRadiusZeroZeroAtom t rho := by
    unfold C literalPairRadiusChannel
    simpa [g] using hbase

  unfold literalPairProjectiveDefect
  rw [channelProjectiveDefect_eq_centeredRadiusDecomposition]
  rw [hdelta2, hdelta1, hC0]
  unfold normalizedProjectiveOffZeroAtom
  dsimp [g, r]
  ring

/-- Finite exact projective spectral representation.  The remaining whole-tsum
attachment is intentionally separate. -/
theorem sum_literalPairProjectiveDefects_eq_normalizedAtoms
    {t : ℝ} (ht : 18 <= t) (F : Finset Zeros) :
    (∑ rho ∈ F,
      literalPairProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) rho)
      =
    (1 / t) * ∑ rho ∈ F, normalizedProjectiveOffZeroAtom t rho := by
  classical
  calc
    (∑ rho ∈ F,
      literalPairProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) rho)
      =
      ∑ rho ∈ F, (1 / t) * normalizedProjectiveOffZeroAtom t rho := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom ht rho
    _ = (1 / t) * ∑ rho ∈ F, normalizedProjectiveOffZeroAtom t rho := by
      rw [Finset.mul_sum]

end Synthesis
