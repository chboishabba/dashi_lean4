import Synthesis.RiemannCenteredClusterPoleReduction
import Synthesis.RiemannQuantitativeCanonicalTaper

/-!
# Canonical centered cluster/pole reduction

This file instantiates the exact centered cluster/pole theorem on the actual
quantitative canonical two-window taper.

First, the symmetric affine bump obeys the elementary support estimate

  quantitativeSymBump(c,R,u) != 0
    -> |u| < c + R

for c>=0 and R>0.

Consequently, for t>=18,

  quantitativeCanonicalTaper(t,u) != 0
    -> |u| < 9*pi/(4*t).

Multiplication by cos(r u)-1 can only shrink support, so the centered taper has
the same support bound.  Any height satisfying

  9*pi <= 4*t*log 2

therefore makes the centered canonical taper prime-invisible.

The canonical mixing coefficient already kills

  poleEvenResp(g,t,r)=0,

so the final centered complement is reduced exactly to

  S_h(t,0)
    = - Cluster_h(t,0) - 4 PoleEven(g,t,0).

No RvM approximation enters this identity.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance

theorem quantitativeSymBump_support_abs_lt
    {c R u : ℝ}
    (hc : 0 <= c)
    (hR : 0 < R)
    (hu : quantitativeSymBump c R u != 0) :
    |u| < c + R := by
  unfold quantitativeSymBump
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hu
  by_cases hp : scaledUnitBump c R u = 0
  · have hm : scaledUnitBump c R (-u) != 0 := by
      intro hm
      apply hu
      simp [hp, hm]
    have hs := scaledUnitBump_support hR hm
    have hcabs : |c| = c := abs_of_nonneg hc
    have htri : |u| <= |u + c| + |c| := by
      have h := abs_add (u + c) (-c)
      simpa [abs_neg] using h
    have hs' : |u + c| < R := by
      have heq : -u - c = -(u + c) := by ring
      rw [heq, abs_neg] at hs
      exact hs
    rw [hcabs] at htri
    linarith
  · have hs := scaledUnitBump_support hR hp
    have hcabs : |c| = c := abs_of_nonneg hc
    have htri : |u| <= |u - c| + |c| := by
      have h := abs_add (u - c) c
      simpa using h
    rw [hcabs] at htri
    linarith

theorem quantitativeInnerBump_support_abs_lt
    {t u : ℝ} (ht : 18 <= t)
    (hu : quantitativeInnerBump t u != 0) :
    |u| < 5 * Real.pi / (4 * t) := by
  have ht0 : 0 < t := by linarith
  have hc : 0 <= quantitativeTaperInnerCenter t := by
    unfold quantitativeTaperInnerCenter
    positivity
  have hR : 0 < quantitativeTaperR t :=
    quantitativeTaperR_pos ht0
  have h :=
    quantitativeSymBump_support_abs_lt
      hc hR hu
  unfold quantitativeInnerBump at hu
  unfold quantitativeTaperInnerCenter quantitativeTaperR at h
  field_simp [ne_of_gt ht0] at h ⊢
  nlinarith [Real.pi_pos]

theorem quantitativeOuterBump_support_abs_lt
    {t u : ℝ} (ht : 18 <= t)
    (hu : quantitativeOuterBump t u != 0) :
    |u| < 9 * Real.pi / (4 * t) := by
  have ht0 : 0 < t := by linarith
  have hc : 0 <= quantitativeTaperOuterCenter t := by
    unfold quantitativeTaperOuterCenter
    positivity
  have hR : 0 < quantitativeTaperR t :=
    quantitativeTaperR_pos ht0
  have h :=
    quantitativeSymBump_support_abs_lt
      hc hR hu
  unfold quantitativeTaperOuterCenter quantitativeTaperR at h
  field_simp [ne_of_gt ht0] at h ⊢
  nlinarith [Real.pi_pos]

theorem quantitativeCanonicalTaper_support_abs_lt
    {t u : ℝ} (ht : 18 <= t)
    (hu : quantitativeCanonicalTaper t u != 0) :
    |u| < 9 * Real.pi / (4 * t) := by
  unfold quantitativeCanonicalTaper at hu
  by_cases hi : quantitativeInnerBump t u = 0
  · have ho : quantitativeOuterBump t u != 0 := by
      intro ho
      apply hu
      simp [hi, ho]
    exact quantitativeOuterBump_support_abs_lt ht ho
  · have hinner := quantitativeInnerBump_support_abs_lt ht hi
    have ht0 : 0 < t := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hcomp :
        5 * Real.pi / (4 * t)
          <= 9 * Real.pi / (4 * t) := by
      positivity
    exact lt_of_lt_of_le hinner hcomp

theorem quantitativeCenteredCanonicalTaper_support_abs_lt
    {t u : ℝ} (ht : 18 <= t)
    (hu :
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) u != 0) :
    |u| < 9 * Real.pi / (4 * t) := by
  apply quantitativeCanonicalTaper_support_abs_lt ht
  intro hzero
  apply hu
  unfold gammaCenteredTaper
  simp [hzero]

theorem quantitativeCenteredCanonicalTaper_short
    {t : ℝ} (ht : 18 <= t)
    (hheight : 9 * Real.pi <= 4 * t * Real.log 2) :
    ∀ u,
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) u != 0
        ->
      |u| < Real.log 2 := by
  intro u hu
  have ht0 : 0 < t := by linarith
  have hs :=
    quantitativeCenteredCanonicalTaper_support_abs_lt ht hu
  have hupper :
      9 * Real.pi / (4 * t) <= Real.log 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * t)]
    exact hheight
  exact lt_of_lt_of_le hs hupper

/--
Canonical theorem-facing reduction.  At every height where the short-support
criterion holds, the entire high centered-sign problem is exactly one
same-ordinate cluster-versus-unweighted-pole inequality.
-/
theorem quantitativeCanonical_centeredComplement_nonpos_iff_clusterPole
    {t : ℝ}
    (ht : 18 <= t)
    (hheight : 9 * Real.pi <= 4 * t * Real.log 2) :
    finalLiteralComplement
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        t 0
      <= 0
      ↔
    - evenConeFunctional
        (clusterVec
          (sampleFam
            (gammaCenteredTaper
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t))
            t 0)
          t)
      <=
    4 * poleEvenResp (quantitativeCanonicalTaper t) t 0 := by
  exact centeredLiteralComplement_nonpos_iff_clusterPole
    (quantitativeCanonicalTaper_contDiff ht)
    (quantitativeCanonicalTaper_compact ht)
    (quantitativeCanonicalTaper_even (t := t))
    (quantitativeCenteredCanonicalTaper_short ht hheight)
    (quantitativeCanonicalTaper_pole_zero ht)

end Synthesis
