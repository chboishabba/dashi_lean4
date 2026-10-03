import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseMassCollapse

/-!
# Same-object L1 envelope for the canonical three-tap mass

This file attacks the finite side of the final one-scale scalar directly.
The transformed normalized support grows like O(t), but translation does not
increase L1 mass.  More importantly, the projective bracket at radius 1 is
quadratic in the detector L1 mass:

  ||P_g||_1 <= 8 ||g||_1^2.

Hence the canonical M0 does not inherit the O(t) support radius provided the
unshifted endpoint profiles and the two signed pole coefficients are uniformly
bounded.  The resulting theorem is same-object: projectivization is performed
after the actual three-tap translation, with no commutation assumption.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real BigOperators
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper

/-- Translation leaves absolute L1 mass unchanged. -/
theorem taperMass_translate_sub_eq
    (g : ℝ → ℝ) (L : ℝ) :
    taperMass (fun u => g (u-L)) = taperMass g := by
  unfold taperMass
  have h := MeasureTheory.integral_add_right_eq_self
    (fun v : ℝ => |g v|) (-L)
  simpa [sub_eq_add_neg, add_assoc] using h

/-- Translation in the opposite direction likewise preserves absolute mass. -/
theorem taperMass_translate_add_eq
    (g : ℝ → ℝ) (L : ℝ) :
    taperMass (fun u => g (u+L)) = taperMass g := by
  unfold taperMass
  simpa using
    (MeasureTheory.integral_add_right_eq_self
      (fun v : ℝ => |g v|) L)

/-- Absolute L1 mass of the actual symmetric three-tap. -/
theorem taperMass_detectorThreeTap_le
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L : ℝ) :
    taperMass (detectorThreeTap g eps L)
      <= (1 + 2*|eps|) * taperMass g := by
  have h0 : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have hm : Integrable (fun u : ℝ => |g (u-L)|) := by
    exact (hg.comp (continuous_id.sub continuous_const)).abs
      |>.integrable_of_hasCompactSupport
        (hgc.comp_homeomorph (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ)).abs
  have hp : Integrable (fun u : ℝ => |g (u+L)|) := by
    exact (hg.comp (continuous_id.add continuous_const)).abs
      |>.integrable_of_hasCompactSupport
        (hgc.comp_homeomorph (Homeomorph.addRight L : ℝ ≃ₜ ℝ)).abs
  have hmaj : ∀ u : ℝ,
      |detectorThreeTap g eps L u|
        <= |g u| + |eps|*|g (u-L)| + |eps|*|g (u+L)| := by
    intro u
    unfold detectorThreeTap
    calc
      |g u + eps*g (u-L) + eps*g (u+L)|
        <= |g u + eps*g (u-L)| + |eps*g (u+L)| := abs_add _ _
      _ <= (|g u| + |eps*g (u-L)|) + |eps|*|g (u+L)| := by
        gcongr
        · exact abs_add _ _
        · rw [abs_mul]
      _ = _ := by rw [abs_mul]
  unfold taperMass
  have hdet : Integrable (fun u : ℝ => |detectorThreeTap g eps L u|) :=
    (detectorThreeTap_contDiff hg.contDiff eps L).continuous.abs
      |>.integrable_of_hasCompactSupport
        (detectorThreeTap_compact hgc eps L).abs
  have hrhs : Integrable (fun u : ℝ =>
      |g u| + |eps|*|g (u-L)| + |eps|*|g (u+L)|) :=
    (h0.add (hm.const_mul |eps|)).add (hp.const_mul |eps|)
  have hi := integral_mono hdet hrhs hmaj
  rw [show
      (∫ u : ℝ, |g u| + |eps|*|g (u-L)| + |eps|*|g (u+L)|)
        = (∫ u : ℝ, |g u|)
          + |eps|*(∫ u : ℝ, |g (u-L)|)
          + |eps|*(∫ u : ℝ, |g (u+L)|) by
      rw [integral_add (h0.add (hm.const_mul |eps|)) (hp.const_mul |eps|),
          integral_add h0 (hm.const_mul |eps|),
          integral_const_mul, integral_const_mul]] at hi
  rw [taperMass_translate_sub_eq g L,
      taperMass_translate_add_eq g L] at hi
  nlinarith

/-- At hyperbolic parameter zero every even response is controlled by L1 mass. -/
theorem abs_evenResp_zero_le_taperMass
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    |evenResp g 0 r| <= taperMass g := by
  have hi : Integrable (fun u : ℝ => g u * Real.cos (r*u)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have habsi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  unfold evenResp taperMass
  simp only [zero_mul, Real.cosh_zero, one_mul]
  calc
    |∫ u : ℝ, g u * Real.cos (r*u)|
      <= ∫ u : ℝ, |g u * Real.cos (r*u)| :=
        abs_integral_le_integral_abs
    _ <= ∫ u : ℝ, |g u| := by
      apply integral_mono hi.abs habsi
      intro u
      rw [abs_mul]
      have hc : |Real.cos (r*u)| <= 1 := by
        rw [abs_le]
        exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      nlinarith [abs_nonneg (g u)]

/-- The radius-one projective bracket is pointwise bounded by twice the source
L1 mass. -/
theorem abs_twoRadiusBracket_one_le_two_taperMass
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (u : ℝ) :
    |twoRadiusBracket g 1 u| <= 2 * taperMass g := by
  have h1 := abs_evenResp_zero_le_taperMass hg hgc 1
  have h2 := abs_evenResp_zero_le_taperMass hg hgc 2
  unfold twoRadiusBracket
  have hc1 : |Real.cos (2*u)| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hc2 : |Real.cos u| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc
    |evenResp g 0 1 * Real.cos (2*1*u)
        - evenResp g 0 (2*1) * Real.cos (1*u)|
      <= |evenResp g 0 1 * Real.cos (2*u)|
          + |evenResp g 0 2 * Real.cos u| := by
        simpa using abs_sub
          (evenResp g 0 1 * Real.cos (2*u))
          (evenResp g 0 2 * Real.cos u)
    _ = |evenResp g 0 1| * |Real.cos (2*u)|
          + |evenResp g 0 2| * |Real.cos u| := by
        rw [abs_mul, abs_mul]
    _ <= taperMass g + taperMass g := by
        gcongr
        · exact mul_le_of_le_one_right (abs_nonneg _) hc1
        · exact mul_le_of_le_one_right (abs_nonneg _) hc2
    _ = 2 * taperMass g := by ring

/-- Radius-one projectivization has an explicit quadratic L1 envelope. -/
theorem taperMass_genericProjectivePhysicalProfile_one_le
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    taperMass (genericProjectivePhysicalProfile g 1)
      <= 8 * (taperMass g)^2 := by
  have hmass : 0 <= taperMass g := by
    unfold taperMass
    positivity
  have hP : Continuous (genericProjectivePhysicalProfile g 1) :=
    genericProjectivePhysicalProfile_continuous hg 1
  have hPc : HasCompactSupport (genericProjectivePhysicalProfile g 1) :=
    genericProjectivePhysicalProfile_compact hgc 1
  have hgi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  unfold taperMass
  have hmaj : ∀ u : ℝ,
      |genericProjectivePhysicalProfile g 1 u|
        <= 8 * (taperMass g) * |g u| := by
    intro u
    unfold genericProjectivePhysicalProfile
    rw [abs_mul, abs_mul]
    have hb := abs_twoRadiusBracket_one_le_two_taperMass hg hgc u
    norm_num
    nlinarith [abs_nonneg (g u)]
  have hi := integral_mono
    hP.abs.integrable_of_hasCompactSupport hPc.abs
    (hgi.const_mul (8 * taperMass g)) hmaj
  rw [integral_const_mul] at hi
  simpa [pow_two] using hi

/-- Endpoint channel projective mass after the actual translated detector. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf_absMass_le
    {t eps B : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hB : taperMass (quarticFourWindowProfile W.R (1/2) W.muHalf) <= B)
    (hB0 : 0 <= B) :
    compactProfileAbsMoment (W.threeTapNormalizedProjectiveHalf eps) 0
      <= 8 * ((1 + 2*|eps|) * B)^2 := by
  let g := quarticFourWindowProfile W.R (1/2) W.muHalf
  have hg : Continuous g := quarticFourWindowProfile_continuous W.Rpos
  have hgc : HasCompactSupport g := quarticFourWindowProfile_compact W.Rpos
  have htap := taperMass_detectorThreeTap_le hg hgc eps
    (threeTapNormalizedShift t (Real.log 2))
  have hfac : 0 <= 1 + 2*|eps| := by positivity
  have hmass :
      taperMass (W.threeTapNormalizedHalf eps)
        <= (1 + 2*|eps|) * B := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedHalf
    exact htap.trans (mul_le_mul_of_nonneg_left hB hfac)
  have hmass0 : 0 <= taperMass (W.threeTapNormalizedHalf eps) := by
    unfold taperMass
    positivity
  have hproj := taperMass_genericProjectivePhysicalProfile_one_le
    (detectorThreeTap_contDiff hg.contDiff eps
      (threeTapNormalizedShift t (Real.log 2))).continuous
    (detectorThreeTap_compact hgc eps
      (threeTapNormalizedShift t (Real.log 2)))
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    compactProfileAbsMoment at hproj ⊢
  simp only [pow_zero, mul_one]
  exact hproj.trans (by
    have hsquare := sq_le_sq₀ hmass0
      (mul_nonneg hfac hB0) hmass
    nlinarith)

/-- The second endpoint channel obeys the same same-object bound. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo_absMass_le
    {t eps B : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hB : taperMass (quarticFourWindowProfile W.R (2/3) W.muTwo) <= B)
    (hB0 : 0 <= B) :
    compactProfileAbsMoment (W.threeTapNormalizedProjectiveTwo eps) 0
      <= 8 * ((1 + 2*|eps|) * B)^2 := by
  let g := quarticFourWindowProfile W.R (2/3) W.muTwo
  have hg : Continuous g := quarticFourWindowProfile_continuous W.Rpos
  have hgc : HasCompactSupport g := quarticFourWindowProfile_compact W.Rpos
  have htap := taperMass_detectorThreeTap_le hg hgc eps
    (threeTapNormalizedShift t (Real.log 2))
  have hfac : 0 <= 1 + 2*|eps| := by positivity
  have hmass :
      taperMass (W.threeTapNormalizedTwo eps)
        <= (1 + 2*|eps|) * B := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedTwo
    exact htap.trans (mul_le_mul_of_nonneg_left hB hfac)
  have hmass0 : 0 <= taperMass (W.threeTapNormalizedTwo eps) := by
    unfold taperMass
    positivity
  have hproj := taperMass_genericProjectivePhysicalProfile_one_le
    (detectorThreeTap_contDiff hg.contDiff eps
      (threeTapNormalizedShift t (Real.log 2))).continuous
    (detectorThreeTap_compact hgc eps
      (threeTapNormalizedShift t (Real.log 2)))
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
    compactProfileAbsMoment at hproj ⊢
  simp only [pow_zero, mul_one]
  exact hproj.trans (by
    have hsquare := sq_le_sq₀ hmass0
      (mul_nonneg hfac hB0) hmass
    nlinarith)

/-- Canonical M0 is explicitly controlled by source-profile L1 and pole bounds.
This is uniform in the translation distance and therefore in t. -/
theorem QuarticFourSignedPolePair.threeTapCanonicalM0_le_of_sourceMass_poleBounds
    {t eps B P : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hB0 : 0 <= B)
    (hHalf : taperMass (quarticFourWindowProfile W.R (1/2) W.muHalf) <= B)
    (hTwo : taperMass (quarticFourWindowProfile W.R (2/3) W.muTwo) <= B)
    (hP0 : 0 <= P)
    (hpHalf : |W.poleHalf| <= P)
    (hpTwo : |W.poleTwo| <= P) :
    W.threeTapCanonicalM0 eps
      <= Real.cosh 1 * (16 * P * ((1 + 2*|eps|) * B)^2) := by
  have hH := W.threeTapNormalizedProjectiveHalf_absMass_le hHalf hB0 (eps:=eps)
  have hT := W.threeTapNormalizedProjectiveTwo_absMass_le hTwo hB0 (eps:=eps)
  have hprojH : 0 <= compactProfileAbsMoment
      (W.threeTapNormalizedProjectiveHalf eps) 0 := by
    unfold compactProfileAbsMoment
    positivity
  have hprojT : 0 <= compactProfileAbsMoment
      (W.threeTapNormalizedProjectiveTwo eps) 0 := by
    unfold compactProfileAbsMoment
    positivity
  have hSigned :
      W.threeTapNormalizedProjectiveAbsMass eps
        <= 16 * P * ((1 + 2*|eps|) * B)^2 := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
      compactProfileAbsMoment
      QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
    have hcontH := W.threeTapNormalizedProjective_continuous (eps:=eps)
    have hcompH := W.threeTapNormalizedProjective_compact (eps:=eps)
    have hpoint : ∀ v : ℝ,
        |W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v
          + (-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v|
        <= |W.poleTwo| * |W.threeTapNormalizedProjectiveHalf eps v|
          + |W.poleHalf| * |W.threeTapNormalizedProjectiveTwo eps v| := by
      intro v
      calc
        |_|
          <= |W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v|
            + |(-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v| := abs_add _ _
        _ = _ := by simp [abs_mul]
    have hi := integral_mono
      hcontH.abs.integrable_of_hasCompactSupport hcompH.abs
      (((W.threeTapNormalizedProjectiveHalf_continuous (eps:=eps)).abs
          .integrable_of_hasCompactSupport
            (W.threeTapNormalizedProjectiveHalf_compact (eps:=eps)).abs
          ).const_mul |W.poleTwo|
        |>.add
          (((W.threeTapNormalizedProjectiveTwo_continuous (eps:=eps)).abs
            .integrable_of_hasCompactSupport
              (W.threeTapNormalizedProjectiveTwo_compact (eps:=eps)).abs
            ).const_mul |W.poleHalf|))
      hpoint
    rw [integral_add,
        integral_const_mul, integral_const_mul] at hi
    · simp only [pow_zero, mul_one] at hH hT
      have h1 := mul_le_mul hpTwo hH hprojH hP0
      have h2 := mul_le_mul hpHalf hT hprojT hP0
      nlinarith
    · exact ((W.threeTapNormalizedProjectiveHalf_continuous (eps:=eps)).abs
        .integrable_of_hasCompactSupport
          (W.threeTapNormalizedProjectiveHalf_compact (eps:=eps)).abs).const_mul _
    · exact ((W.threeTapNormalizedProjectiveTwo_continuous (eps:=eps)).abs
        .integrable_of_hasCompactSupport
          (W.threeTapNormalizedProjectiveTwo_compact (eps:=eps)).abs).const_mul _
  unfold QuarticFourSignedPolePair.threeTapCanonicalM0
  exact mul_le_mul_of_nonneg_left hSigned (Real.cosh_pos _).le

end Synthesis
