import Synthesis.RiemannCanonicalLeadingSignalFloor
import Synthesis.RiemannSelectedRadiusClusterReduction
import Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-!
# Canonical quantitative taper as literal GateData

The quantitative canonical taper already owns smoothness, compact support,
evenness, nonnegativity, short support, and exact pole annihilation.  This file
pays the two remaining GateData receipts directly:

* doubled-radius radial admissibility;
* two distinct positive modulus points, the inner and outer bump centres.

Hence the exact taper used by the canonical signal-floor theorem is also an
inhabitant of the literal projective GateData interface.
-/

noncomputable section

open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

theorem quantitativeCanonicalTaper_pos_at_outerCenter
    {t : ℝ} (ht : 18 <= t) :
    0 <
      quantitativeCanonicalTaper t
        (quantitativeTaperOuterCenter t) := by
  unfold quantitativeCanonicalTaper
  have hi :
      0 <=
      quantitativeInnerBump t
        (quantitativeTaperOuterCenter t) := by
    unfold quantitativeInnerBump
    exact quantitativeSymBump_nonneg _ _ _
  have ho : 0 <
      quantitativeOuterBump t
        (quantitativeTaperOuterCenter t) := by
    unfold quantitativeOuterBump quantitativeSymBump
      Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    have ht0 : 0 < t := by linarith
    have hR := quantitativeTaperR_pos ht0
    rw [scaledUnitBump_at_center hR.ne']
    have hother :
        0 <=
        scaledUnitBump
          (quantitativeTaperOuterCenter t)
          (quantitativeTaperR t)
          (-quantitativeTaperOuterCenter t) :=
      scaledUnitBump_nonneg _ _ _
    linarith
  have hlam : 0 < quantitativeLambda t := quantitativeLambda_pos ht
  nlinarith [mul_pos hlam ho]

theorem quantitativeCanonicalTaper_twoPoint
    {t : ℝ} (ht : 18 <= t) :
    ∃ u v : ℝ,
      0 < quantitativeCanonicalTaper t u
      ∧ 0 < quantitativeCanonicalTaper t v
      ∧ |u| ≠ |v| := by
  refine ⟨quantitativeTaperInnerCenter t,
    quantitativeTaperOuterCenter t,
    quantitativeCanonicalTaper_pos_at_innerCenter ht,
    quantitativeCanonicalTaper_pos_at_outerCenter ht,
    ?_⟩
  have ht0 : 0 < t := by linarith
  have hinner : 0 < quantitativeTaperInnerCenter t := by
    unfold quantitativeTaperInnerCenter
    positivity
  have houter : 0 < quantitativeTaperOuterCenter t := by
    unfold quantitativeTaperOuterCenter
    positivity
  rw [abs_of_pos hinner, abs_of_pos houter]
  unfold quantitativeTaperInnerCenter quantitativeTaperOuterCenter
  intro h
  have hpi := Real.pi_pos
  field_simp [ne_of_gt ht0] at h
  nlinarith

theorem quantitativeCanonicalTaper_radial_twoRadius
    {t : ℝ} (ht : 18 <= t) :
    ∀ u, quantitativeCanonicalTaper t u ≠ 0 ->
      2 * quantitativeSampleRadius t * |u| < Real.pi / 2 := by
  intro u hu
  have ht0 : 0 < t := by linarith
  have hs := quantitativeCanonicalTaper_support_abs_lt ht hu
  unfold quantitativeSampleRadius
  have hmul :=
    mul_lt_mul_of_pos_left hs (by positivity : 0 < t / 8)
  have hscaled :
      (t / 8) * |u| < 9 * Real.pi / 32 := by
    field_simp [ne_of_gt ht0] at hmul ⊢
    nlinarith [Real.pi_pos]
  have hconst : 9 * Real.pi / 32 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have heq : 2 * (t / 16) * |u| = (t / 8) * |u| := by ring
  rw [heq]
  exact lt_trans hscaled hconst

def quantitativeCanonicalGateData
    {t : ℝ} (ht : 18 <= t) :
    GateData
      (quantitativeCanonicalTaper t)
      t
      (quantitativeSampleRadius t)
      (9 * Real.pi / (4 * t)) where
  smooth := quantitativeCanonicalTaper_contDiff ht
  compactSupport := quantitativeCanonicalTaper_compact ht
  isEven := quantitativeCanonicalTaper_even (t := t)
  nonneg := quantitativeCanonicalTaper_nonneg ht
  radiusPos := by
    unfold quantitativeSampleRadius
    positivity
  radial := quantitativeCanonicalTaper_radial_twoRadius ht
  supportRadius := by
    intro u hu
    exact (quantitativeCanonicalTaper_support_abs_lt ht hu).le
  lambdaNonneg := by
    positivity
  short := quantitativeCanonicalTaper_short_high ht
  poleKilled := quantitativeCanonicalTaper_pole_zero ht
  twoPoint := quantitativeCanonicalTaper_twoPoint ht

end Synthesis
