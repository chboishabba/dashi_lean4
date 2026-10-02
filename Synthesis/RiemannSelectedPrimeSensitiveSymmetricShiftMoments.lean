import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTargetMoment

/-!
# Symmetric-shift moment transport for the RH deformation lane

The terminal local budget must be recomputed on the translated detector.
This module provides the reusable exact transport layer: arbitrary raw moments
under each translation, the exact three-tap moment decomposition, and the
symmetric even-power polynomials through order eight.

The polynomial identities are shared by the one-scale and two-scale operators.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real BigOperators

def rawMoment (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, u^k * g u

def shiftedMinusMoment (g : ℝ → ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, u^k * g (u-L)

def shiftedPlusMoment (g : ℝ → ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, u^k * g (u+L)

def symmetricShiftPairMoment (g : ℝ → ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  shiftedMinusMoment g L k + shiftedPlusMoment g L k

def threeTapRawMoment (g : ℝ → ℝ) (eps L : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, u^k * detectorThreeTap g eps L u

theorem shiftedMinusMoment_eq
    (g : ℝ → ℝ) (L : ℝ) (k : ℕ) :
    shiftedMinusMoment g L k
      = ∫ v : ℝ, (v+L)^k * g v := by
  have h :=
    integral_add_right_eq_self
      (fun v : ℝ => (v+L)^k * g v) (-L)
  unfold shiftedMinusMoment
  simpa [sub_eq_add_neg, add_assoc] using h

theorem shiftedPlusMoment_eq
    (g : ℝ → ℝ) (L : ℝ) (k : ℕ) :
    shiftedPlusMoment g L k
      = ∫ v : ℝ, (v-L)^k * g v := by
  have h :=
    integral_add_right_eq_self
      (fun v : ℝ => (v-L)^k * g v) L
  unfold shiftedPlusMoment
  simpa [sub_eq_add_neg, add_assoc] using h

theorem integrable_pow_mul_of_continuous_compact
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (k : ℕ) :
    Integrable (fun u : ℝ => u^k * g u) := by
  exact
    ((continuous_id.pow k).mul hg).integrable_of_hasCompactSupport
      hgc.mul_left

theorem threeTapRawMoment_eq_base_add_pair
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L : ℝ) (k : ℕ) :
    threeTapRawMoment g eps L k
      =
    rawMoment g k + eps * symmetricShiftPairMoment g L k := by
  have h0 := integrable_pow_mul_of_continuous_compact hg hgc k
  have hminusC : Continuous (fun u : ℝ => g (u-L)) := by fun_prop
  have hplusC : Continuous (fun u : ℝ => g (u+L)) := by fun_prop
  have hminusK : HasCompactSupport (fun u : ℝ => g (u-L)) := by
    have heq : (fun u : ℝ => g (u-L))
        = g ∘ (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ) := by
      funext u
      simp [Function.comp_def, sub_eq_add_neg]
    rw [heq]
    exact hgc.comp_homeomorph _
  have hplusK : HasCompactSupport (fun u : ℝ => g (u+L)) := by
    have heq : (fun u : ℝ => g (u+L))
        = g ∘ (Homeomorph.addRight L : ℝ ≃ₜ ℝ) := by
      rfl
    rw [heq]
    exact hgc.comp_homeomorph _
  have hm := integrable_pow_mul_of_continuous_compact hminusC hminusK k
  have hp := integrable_pow_mul_of_continuous_compact hplusC hplusK k
  unfold threeTapRawMoment rawMoment symmetricShiftPairMoment
    shiftedMinusMoment shiftedPlusMoment detectorThreeTap
  rw [show
      (fun u : ℝ =>
        u^k * (g u + eps*g (u-L) + eps*g (u+L)))
      =
      fun u =>
        u^k*g u + eps*(u^k*g (u-L)) + eps*(u^k*g (u+L)) by
      funext u
      ring]
  rw [integral_add (h0.add (hm.const_mul eps)) (hp.const_mul eps),
      integral_add h0 (hm.const_mul eps),
      integral_const_mul, integral_const_mul]
  ring

def symmetricShiftPower (k : ℕ) (L u : ℝ) : ℝ :=
  (u+L)^k + (u-L)^k

theorem symmetricShiftPower_zero (L u : ℝ) :
    symmetricShiftPower 0 L u = 2 := by
  unfold symmetricShiftPower
  norm_num

theorem symmetricShiftPower_two (L u : ℝ) :
    symmetricShiftPower 2 L u
      = 2*u^2 + 2*L^2 := by
  unfold symmetricShiftPower
  ring

theorem symmetricShiftPower_four (L u : ℝ) :
    symmetricShiftPower 4 L u
      = 2*u^4 + 12*L^2*u^2 + 2*L^4 := by
  unfold symmetricShiftPower
  ring

theorem symmetricShiftPower_six (L u : ℝ) :
    symmetricShiftPower 6 L u
      = 2*u^6 + 30*L^2*u^4 + 30*L^4*u^2 + 2*L^6 := by
  unfold symmetricShiftPower
  ring

theorem symmetricShiftPower_eight (L u : ℝ) :
    symmetricShiftPower 8 L u
      =
    2*u^8 + 56*L^2*u^6 + 140*L^4*u^4
      + 56*L^6*u^2 + 2*L^8 := by
  unfold symmetricShiftPower
  ring

theorem symmetricShiftPairMoment_eq_integral
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (L : ℝ) (k : ℕ) :
    symmetricShiftPairMoment g L k
      =
    ∫ u : ℝ, symmetricShiftPower k L u * g u := by
  rw [show symmetricShiftPairMoment g L k
      = shiftedMinusMoment g L k + shiftedPlusMoment g L k by rfl,
    shiftedMinusMoment_eq, shiftedPlusMoment_eq]
  have hm :
      Integrable (fun u : ℝ => (u+L)^k * g u) := by
    exact
      (((continuous_id.add continuous_const).pow k).mul hg)
        .integrable_of_hasCompactSupport hgc.mul_left
  have hp :
      Integrable (fun u : ℝ => (u-L)^k * g u) := by
    exact
      (((continuous_id.sub continuous_const).pow k).mul hg)
        .integrable_of_hasCompactSupport hgc.mul_left
  rw [← integral_add hm hp]
  apply integral_congr_ae
  filter_upwards with u
  unfold symmetricShiftPower
  ring

/-- The exact sixth transformed moment, before any sign estimate. -/
theorem threeTapRawMoment_six_exact
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L : ℝ) :
    threeTapRawMoment g eps L 6
      =
    rawMoment g 6
      + eps *
        ∫ u : ℝ,
          (2*u^6 + 30*L^2*u^4 + 30*L^4*u^2 + 2*L^6) * g u := by
  rw [threeTapRawMoment_eq_base_add_pair hg hgc,
      symmetricShiftPairMoment_eq_integral hg hgc]
  apply congrArg (fun x : ℝ => rawMoment g 6 + eps*x)
  apply integral_congr_ae
  filter_upwards with u
  rw [symmetricShiftPower_six]

/-- The exact eighth transformed moment, before conversion to an absolute
remainder envelope. -/
theorem threeTapRawMoment_eight_exact
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L : ℝ) :
    threeTapRawMoment g eps L 8
      =
    rawMoment g 8
      + eps *
        ∫ u : ℝ,
          (2*u^8 + 56*L^2*u^6 + 140*L^4*u^4
            + 56*L^6*u^2 + 2*L^8) * g u := by
  rw [threeTapRawMoment_eq_base_add_pair hg hgc,
      symmetricShiftPairMoment_eq_integral hg hgc]
  apply congrArg (fun x : ℝ => rawMoment g 8 + eps*x)
  apply integral_congr_ae
  filter_upwards with u
  rw [symmetricShiftPower_eight]

/-! ## Exact normalized-coordinate representation -/

theorem detectorThreeTap_projectiveRescaleProfile
    (G : ℝ → ℝ) (r eps L : ℝ) :
    detectorThreeTap (projectiveRescaleProfile G r) eps L
      =
    projectiveRescaleProfile
      (detectorThreeTap G eps (r*L)) r := by
  funext u
  unfold detectorThreeTap projectiveRescaleProfile
  congr 1 <;> ring

theorem quarticFourPhysicalDetector_threeTap_eq_normalized
    (R lam mu t eps L : ℝ) :
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t) eps L
      =
    projectiveRescaleProfile
      (detectorThreeTap
        (quarticFourWindowProfile R lam mu)
        eps ((t/16)*L))
      (t/16) := by
  unfold quarticFourPhysicalDetector
  exact detectorThreeTap_projectiveRescaleProfile
    (quarticFourWindowProfile R lam mu) (t/16) eps L

/-- The physical log-2 tap is therefore a normalized translation by
B(t)=(t/16)log2.  This is the object whose M2/M4/M6/M8 data must feed any
translated local Taylor budget. -/
theorem quarticFourPhysicalDetector_threeTap_logTwo_eq_normalized
    (R lam mu t eps : ℝ) :
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t)
      eps (Real.log 2)
      =
    projectiveRescaleProfile
      (detectorThreeTap
        (quarticFourWindowProfile R lam mu)
        eps (threeTapNormalizedShift t (Real.log 2)))
      (t/16) := by
  rw [quarticFourPhysicalDetector_threeTap_eq_normalized]
  rfl

end Synthesis
