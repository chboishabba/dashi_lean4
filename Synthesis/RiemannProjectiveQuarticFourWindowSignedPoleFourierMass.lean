import Synthesis.RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb
import Synthesis.RiemannCompactCosineFourierMassInversion

/-!
# Fourier mass of the selected signed quartic RH test

This is the same-object specialization of the generic cosine inversion theorem
to the actual signed pole-cancelled RH witness.

The combined physical profile is even, C^2 and compactly supported, hence

  integral C_W(q) dq = 2*pi*P_W(0).

The support-separated central bump has exact value

  G_R(0) = 1/(R*M0),

and the physical origin factors through the already-defined smooth
pole-cancelled origin determinant.  Therefore

  integral C_W
    = 8*pi/(R*M0) * OriginDet_W.

Finally the literal ordinate test is

  Psi_t(x) = r^-2 C_W((x-t)/r),  r=t/16,

so an exact affine change of variables gives

  integral Psi_t
    = (2*pi/r) P_W(0)
    = 128*pi/(t*R*M0) * OriginDet_W.

This exposes the constant-density mode without estimating the discrete zero
source or the mu-variation term separately.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

theorem genericProjectivePhysicalProfile_even
    {g : ℝ -> ℝ}
    (heven : ∀ u : ℝ, g (-u) = g u)
    (r u : ℝ) :
    genericProjectivePhysicalProfile g r (-u)
      = genericProjectivePhysicalProfile g r u := by
  unfold genericProjectivePhysicalProfile twoRadiusBracket evenResp
  rw [heven u]
  simp only [mul_neg, Real.cos_neg]
  ring

theorem quarticFourNormalizedProjectiveProfile_even
    (R lam mu u : ℝ) :
    quarticFourNormalizedProjectiveProfile R lam mu (-u)
      =
    quarticFourNormalizedProjectiveProfile R lam mu u := by
  unfold quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_even
    (quarticFourWindowProfile_even R lam mu) 1 u

theorem quarticFourSignedPoleCombinedProfile_even
    (R muHalf muTwo t u : ℝ) :
    quarticFourSignedPoleCombinedProfile R muHalf muTwo t (-u)
      =
    quarticFourSignedPoleCombinedProfile R muHalf muTwo t u := by
  unfold quarticFourSignedPoleCombinedProfile profileLinearCombination
  rw [
    quarticFourNormalizedProjectiveProfile_even,
    quarticFourNormalizedProjectiveProfile_even
  ]

theorem QuarticFourSignedPolePair.normalizedOrdinateCosine_integrable
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable W.normalizedOrdinateCosine := by
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosine
  exact compactCosineTransform_integrable
    (quarticFourSignedPoleCombinedProfile_contDiff_two W.Rpos)
    (quarticFourSignedPoleCombinedProfile_compact W.Rpos)

theorem QuarticFourSignedPolePair.normalizedOrdinateCosine_mass_eq_profile_origin
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∫ q : ℝ, W.normalizedOrdinateCosine q)
      =
    2 * Real.pi *
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t 0 := by
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosine
  exact compactCosineTransform_integral_eq_two_pi_mul_zero
    (quarticFourSignedPoleCombinedProfile_contDiff_two W.Rpos)
    (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
    (quarticFourSignedPoleCombinedProfile_even
      W.R W.muHalf W.muTwo t)

theorem QuarticFourSignedPolePair.normalizedOrdinateCosine_mass_eq_originDet
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∫ q : ℝ, W.normalizedOrdinateCosine q)
      =
    (8 * Real.pi / (W.R * unitBumpMass0))
      *
    quarticFourSmoothFinitePoleCancelledOrigin
      W.R W.muHalf W.muTwo t := by
  rw [W.normalizedOrdinateCosine_mass_eq_profile_origin,
      W.combinedProfile_zero_eq_commonWindow_mul_origin,
      quarticFourWindowProfile_zero_eq_inv_mass W.Rpos W.RltOne]
  have hR : W.R ≠ 0 := ne_of_gt W.Rpos
  have hM : unitBumpMass0 ≠ 0 := ne_of_gt unitBumpMass0_pos
  field_simp [hR,hM]
  ring

theorem QuarticFourSignedPolePair.normalizedOrdinateCosine_mass_neg_of_origin_neg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (horigin :
      quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t < 0) :
    (∫ q : ℝ, W.normalizedOrdinateCosine q) < 0 := by
  rw [W.normalizedOrdinateCosine_mass_eq_originDet]
  have hR : 0 < W.R := W.Rpos
  have hM : 0 < unitBumpMass0 := unitBumpMass0_pos
  have hp : 0 < Real.pi := Real.pi_pos
  have hfac :
      0 < 8 * Real.pi / (W.R * unitBumpMass0) := by positivity
  exact mul_neg_of_pos_of_neg hfac horigin

theorem QuarticFourSignedPolePair.signedOrdinateTest_mass_eq_normalized
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (∫ x : ℝ, W.signedOrdinateTest x)
      =
    (16/t) * (∫ q : ℝ, W.normalizedOrdinateCosine q) := by
  let r : ℝ := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hpoint :
      (fun x : ℝ => W.signedOrdinateTest x)
        =
      fun x : ℝ =>
        (1/r^2) *
          W.normalizedOrdinateCosine ((x-t)/r) := by
    funext x
    rw [W.signedOrdinateTest_eq_combinedCosine]
    unfold QuarticFourSignedPolePair.normalizedOrdinateCosine
    rfl
  rw [hpoint, integral_const_mul]
  let F : ℝ -> ℝ :=
    fun y => W.normalizedOrdinateCosine (y/r)
  have hshift :
      (∫ x : ℝ, F (x + (-t))) = ∫ x : ℝ, F x :=
    integral_add_right_eq_self F (-t)
  have hrewrite :
      (fun x : ℝ => W.normalizedOrdinateCosine ((x-t)/r))
        =
      fun x : ℝ => F (x + (-t)) := by
    funext x
    dsimp [F]
    congr 2 <;> ring
  rw [hrewrite,hshift]
  have hscale :=
    Measure.integral_comp_mul_left
      W.normalizedOrdinateCosine (1/r)
  have habs :
      |((1/r : ℝ))⁻¹| = r := by
    rw [show (1/r : ℝ) = r⁻¹ by field_simp [hr0],
        inv_inv, abs_of_pos hr]
  have hscale' :
      (∫ x : ℝ, W.normalizedOrdinateCosine ((1/r)*x))
        =
      r * (∫ q : ℝ, W.normalizedOrdinateCosine q) := by
    simpa [habs, smul_eq_mul] using hscale
  have hsame :
      (fun x : ℝ => W.normalizedOrdinateCosine (x/r))
        =
      fun x : ℝ => W.normalizedOrdinateCosine ((1/r)*x) := by
    funext x
    congr 2
    field_simp [hr0]
  rw [hsame,hscale']
  dsimp [r]
  field_simp [ne_of_gt ht]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTest_mass_eq_profile_origin
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (∫ x : ℝ, W.signedOrdinateTest x)
      =
    (32 * Real.pi / t)
      *
    quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t 0 := by
  rw [W.signedOrdinateTest_mass_eq_normalized ht,
      W.normalizedOrdinateCosine_mass_eq_profile_origin]
  field_simp [ne_of_gt ht]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTest_mass_eq_originDet
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (∫ x : ℝ, W.signedOrdinateTest x)
      =
    (128 * Real.pi / (t * W.R * unitBumpMass0))
      *
    quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t := by
  rw [W.signedOrdinateTest_mass_eq_profile_origin ht,
      W.combinedProfile_zero_eq_commonWindow_mul_origin,
      quarticFourWindowProfile_zero_eq_inv_mass W.Rpos W.RltOne]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hR : W.R ≠ 0 := ne_of_gt W.Rpos
  have hM : unitBumpMass0 ≠ 0 := ne_of_gt unitBumpMass0_pos
  field_simp [ht0,hR,hM]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTest_mass_neg_of_origin_neg
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (horigin :
      quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t < 0) :
    (∫ x : ℝ, W.signedOrdinateTest x) < 0 := by
  rw [W.signedOrdinateTest_mass_eq_originDet ht]
  have hfac :
      0 < 128 * Real.pi / (t * W.R * unitBumpMass0) := by
    positivity
  exact mul_neg_of_pos_of_neg hfac horigin

theorem exists_quarticFourSignedPolePair_with_strength_floor_and_negative_ordinate_mass
    {t : ℝ}
    (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 <= W.targetStrength
      ∧ (∫ x : ℝ, W.signedOrdinateTest x) < 0 := by
  obtain ⟨W,hstrength,horigin⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor_and_negative_origin ht
  refine ⟨W,hstrength,?_⟩
  exact W.signedOrdinateTest_mass_neg_of_origin_neg
    (by linarith) horigin


/-!
## Exact constant-density mode

The center-density contribution is now a literal scalar, not an asymptotic
description.  We deliberately do not assume a sign for Zeta23.mu here; that
can be supplied by the existing Riemann--von Mangoldt owner when desired.
-/

def QuarticFourSignedPolePair.centerDensityMode
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  Zeta23.mu t * (∫ x : ℝ, W.signedOrdinateTest x)

theorem QuarticFourSignedPolePair.centerDensityMode_eq_originDet
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.centerDensityMode
      =
    (128 * Real.pi * Zeta23.mu t
        / (t * W.R * unitBumpMass0))
      *
    quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t := by
  unfold QuarticFourSignedPolePair.centerDensityMode
  rw [W.signedOrdinateTest_mass_eq_originDet ht]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hR : W.R ≠ 0 := ne_of_gt W.Rpos
  have hM : unitBumpMass0 ≠ 0 := ne_of_gt unitBumpMass0_pos
  field_simp [ht0,hR,hM]
  ring

def QuarticFourSignedPolePair.adverseCenterDensityMode
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  -(1/2 : ℝ) * W.centerDensityMode

theorem QuarticFourSignedPolePair.adverseCenterDensityMode_eq_originDet
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.adverseCenterDensityMode
      =
    -(64 * Real.pi * Zeta23.mu t
        / (t * W.R * unitBumpMass0))
      *
    quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t := by
  unfold QuarticFourSignedPolePair.adverseCenterDensityMode
  rw [W.centerDensityMode_eq_originDet ht]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hR : W.R ≠ 0 := ne_of_gt W.Rpos
  have hM : unitBumpMass0 ≠ 0 := ne_of_gt unitBumpMass0_pos
  field_simp [ht0,hR,hM]
  ring

theorem QuarticFourSignedPolePair.centerDensityMode_neg_of_mu_pos_origin_neg
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hmu : 0 < Zeta23.mu t)
    (horigin :
      quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t < 0) :
    W.centerDensityMode < 0 := by
  rw [W.centerDensityMode_eq_originDet ht]
  have hfac :
      0 <
      128 * Real.pi * Zeta23.mu t
        / (t * W.R * unitBumpMass0) := by
    positivity
  exact mul_neg_of_pos_of_neg hfac horigin

theorem QuarticFourSignedPolePair.adverseCenterDensityMode_pos_of_mu_pos_origin_neg
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hmu : 0 < Zeta23.mu t)
    (horigin :
      quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t < 0) :
    0 < W.adverseCenterDensityMode := by
  unfold QuarticFourSignedPolePair.adverseCenterDensityMode
  have hneg :=
    W.centerDensityMode_neg_of_mu_pos_origin_neg ht hmu horigin
  nlinarith

end Synthesis
