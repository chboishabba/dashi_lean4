import Synthesis.RiemannSelectedPrimeSensitiveThreeTapLocalBudget

/-!
# Normalized transformed projective profile and adaptive support

The post-sixth Taylor machinery lives in the normalized profile coordinate.
This file pays the physical/normalized projective seam exactly.

For r>0,

  P_{G(r·),r}(u) = r⁻¹ P_{G,1}(r u).

Combining this with the already-proved detector three-tap rescaling shows that
the physical log-2 translation is exactly the normalized translation
B = r log 2 before projectivization.  We therefore define the transformed
normalized projective object directly and prove its support lies in

  |v| < (pi+1) + |B|.

No commutation of projectivization with translation is asserted.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

/-- Projective profile rescaling, including the extra r⁻¹ response factor. -/
theorem genericProjectivePhysicalProfile_rescale
    {G : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (u : ℝ) :
    genericProjectivePhysicalProfile
        (projectiveRescaleProfile G r) r u
      =
    (1/r) *
      genericProjectivePhysicalProfile G 1 (r*u) := by
  unfold genericProjectivePhysicalProfile
    Zeta23Bridge.LiteralWeilProjectiveTaper.twoRadiusBracket
    projectiveRescaleProfile
  rw [show r = (1:ℝ)*r by ring,
      show 2*r = (2:ℝ)*r by ring,
      evenResp_projectiveRescale hr 1,
      evenResp_projectiveRescale hr 2]
  field_simp [ne_of_gt hr]
  ring

/-- Generic support transport for a symmetric three-tap. -/
theorem detectorThreeTap_support_abs_lt_add
    {g : ℝ → ℝ} {S eps L u : ℝ}
    (hS : 0 <= S)
    (hshort : ∀ v : ℝ, g v ≠ 0 → |v| < S)
    (hu : detectorThreeTap g eps L u ≠ 0) :
    |u| < S + |L| := by
  by_contra hbad
  have hge : S + |L| <= |u| := le_of_not_gt hbad
  have zero_of_outside (v : ℝ) (hv : S <= |v|) : g v = 0 := by
    by_contra hvn
    exact (not_lt_of_ge hv) (hshort v hvn)
  have hz0 : g u = 0 :=
    zero_of_outside u (by linarith [abs_nonneg L])
  have hzm : g (u-L) = 0 := by
    apply zero_of_outside
    by_contra hlt
    have hlt' : |u-L| < S := lt_of_not_ge hlt
    have htri : |u| <= |u-L| + |L| := by
      have h := abs_add (u-L) L
      simpa using h
    linarith
  have hzp : g (u+L) = 0 := by
    apply zero_of_outside
    by_contra hlt
    have hlt' : |u+L| < S := lt_of_not_ge hlt
    have htri : |u| <= |u+L| + |L| := by
      have h := abs_add (u+L) (-L)
      simpa using h
    linarith
  apply hu
  simp [detectorThreeTap, hz0, hzm, hzp]

def QuarticFourSignedPolePair.threeTapNormalizedHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  detectorThreeTap
    (quarticFourWindowProfile W.R (1/2) W.muHalf)
    eps (threeTapNormalizedShift t (Real.log 2))

def QuarticFourSignedPolePair.threeTapNormalizedTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  detectorThreeTap
    (quarticFourWindowProfile W.R (2/3) W.muTwo)
    eps (threeTapNormalizedShift t (Real.log 2))

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  genericProjectivePhysicalProfile (W.threeTapNormalizedHalf eps) 1

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  genericProjectivePhysicalProfile (W.threeTapNormalizedTwo eps) 1

def QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  fun v =>
    W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v
      + (-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v

theorem QuarticFourSignedPolePair.threeTapHalf_eq_rescaled_normalized
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapHalf eps
      =
    projectiveRescaleProfile
      (W.threeTapNormalizedHalf eps) (t/16) := by
  unfold QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapNormalizedHalf
  simpa [threeTapNormalizedShift] using
    quarticFourPhysicalDetector_threeTap_eq_normalized
      W.R (1/2) W.muHalf t eps (Real.log 2)

theorem QuarticFourSignedPolePair.threeTapTwo_eq_rescaled_normalized
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapTwo eps
      =
    projectiveRescaleProfile
      (W.threeTapNormalizedTwo eps) (t/16) := by
  unfold QuarticFourSignedPolePair.threeTapTwo
    QuarticFourSignedPolePair.threeTapNormalizedTwo
  simpa [threeTapNormalizedShift] using
    quarticFourPhysicalDetector_threeTap_eq_normalized
      W.R (2/3) W.muTwo t eps (Real.log 2)

/-- Exact physical/normalized weld for the endpoint projective profile. -/
theorem QuarticFourSignedPolePair.threeTapProjectiveProfileHalf_rescale
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (u : ℝ) :
    W.threeTapProjectiveProfileHalf eps u
      =
    (1/(t/16)) *
      W.threeTapNormalizedProjectiveHalf eps ((t/16)*u) := by
  have hr : 0 < t/16 := by linarith
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileHalf
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
  rw [W.threeTapHalf_eq_rescaled_normalized]
  exact genericProjectivePhysicalProfile_rescale hr u

theorem QuarticFourSignedPolePair.threeTapProjectiveProfileTwo_rescale
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (u : ℝ) :
    W.threeTapProjectiveProfileTwo eps u
      =
    (1/(t/16)) *
      W.threeTapNormalizedProjectiveTwo eps ((t/16)*u) := by
  have hr : 0 < t/16 := by linarith
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileTwo
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
  rw [W.threeTapTwo_eq_rescaled_normalized]
  exact genericProjectivePhysicalProfile_rescale hr u

theorem QuarticFourSignedPolePair.threeTapSignedProjectiveProfile_rescale
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (u : ℝ) :
    W.threeTapSignedProjectiveProfile eps u
      =
    (1/(t/16)) *
      W.threeTapNormalizedSignedProjectiveProfile eps ((t/16)*u) := by
  unfold QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
    QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
  rw [W.threeTapProjectiveProfileHalf_rescale ht,
      W.threeTapProjectiveProfileTwo_rescale ht]
  ring

theorem QuarticFourSignedPolePair.threeTapNormalizedHalf_support
    {t eps v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedHalf eps v ≠ 0) :
    |v| < W.threeTapNormalizedSupportRadius := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedHalf
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  have hbase :
      ∀ x : ℝ,
        quarticFourWindowProfile W.R (1/2) W.muHalf x ≠ 0 →
          |x| < Real.pi + 1 := by
    intro x hx
    have hs := quarticFourWindowProfile_support_abs_lt W.Rpos hx
    linarith [W.RltOne]
  exact detectorThreeTap_support_abs_lt_add
    (by positivity : 0 <= Real.pi + 1) hbase hv

theorem QuarticFourSignedPolePair.threeTapNormalizedTwo_support
    {t eps v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedTwo eps v ≠ 0) :
    |v| < W.threeTapNormalizedSupportRadius := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedTwo
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  have hbase :
      ∀ x : ℝ,
        quarticFourWindowProfile W.R (2/3) W.muTwo x ≠ 0 →
          |x| < Real.pi + 1 := by
    intro x hx
    have hs := quarticFourWindowProfile_support_abs_lt W.Rpos hx
    linarith [W.RltOne]
  exact detectorThreeTap_support_abs_lt_add
    (by positivity : 0 <= Real.pi + 1) hbase hv

theorem genericProjectivePhysicalProfile_ne_zero_imp_source
    {g : ℝ → ℝ} {r u : ℝ}
    (hP : genericProjectivePhysicalProfile g r u ≠ 0) :
    g u ≠ 0 := by
  intro hg
  apply hP
  simp [genericProjectivePhysicalProfile, hg]

theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf_support
    {t eps v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedProjectiveHalf eps v ≠ 0) :
    |v| < W.threeTapNormalizedSupportRadius := by
  apply W.threeTapNormalizedHalf_support
  exact genericProjectivePhysicalProfile_ne_zero_imp_source hv

theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo_support
    {t eps v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedProjectiveTwo eps v ≠ 0) :
    |v| < W.threeTapNormalizedSupportRadius := by
  apply W.threeTapNormalizedTwo_support
  exact genericProjectivePhysicalProfile_ne_zero_imp_source hv

theorem QuarticFourSignedPolePair.threeTapNormalizedSignedProjective_support
    {t eps v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedSignedProjectiveProfile eps v ≠ 0) :
    |v| < W.threeTapNormalizedSupportRadius := by
  by_contra hbad
  have hge :
      W.threeTapNormalizedSupportRadius <= |v| := le_of_not_gt hbad
  have hz1 : W.threeTapNormalizedProjectiveHalf eps v = 0 := by
    by_contra h
    exact (not_lt_of_ge hge)
      (W.threeTapNormalizedProjectiveHalf_support h)
  have hz2 : W.threeTapNormalizedProjectiveTwo eps v = 0 := by
    by_contra h
    exact (not_lt_of_ge hge)
      (W.threeTapNormalizedProjectiveTwo_support h)
  apply hv
  simp [QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile,
    hz1, hz2]

/-- Adaptive Taylor-domain guarantee on the actual normalized transformed
projective object. -/
theorem QuarticFourSignedPolePair.abs_q_mul_v_le_one_of_threeTapAdaptive
    {t eps q v : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius)
    (hv : W.threeTapNormalizedSignedProjectiveProfile eps v ≠ 0) :
    |q*v| <= 1 := by
  have hs := W.threeTapNormalizedSignedProjective_support hv
  have hS := W.threeTapNormalizedSupportRadius_pos
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius at hq
  rw [abs_mul]
  have hqS :
      |q| * W.threeTapNormalizedSupportRadius <= 1 := by
    calc
      |q| * W.threeTapNormalizedSupportRadius
        <= (1 / W.threeTapNormalizedSupportRadius)
            * W.threeTapNormalizedSupportRadius :=
          mul_le_mul_of_nonneg_right hq hS.le
      _ = 1 := by field_simp [ne_of_gt hS]
  exact
    (mul_le_mul_of_nonneg_left hs.le (abs_nonneg q)).trans hqS

end Synthesis
