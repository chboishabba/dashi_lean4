import Synthesis.RiemannNormalizedProjectiveBaseProfile

/-!
# The projective base test vanishes at the same-ordinate point q = 0

The literal Off tsum excludes SameOrd t, while the theorem-bearing Zeta23
counting discrepancy naturally uses the full zero count.  On the normalized
coordinate

  q = (gamma-t)/t,

every same-ordinate zero lies at q=0.  Thus the two carriers agree on the base
consumer exactly if the projective base transform vanishes at q=0.

This file proves that exact identity from the literal scaling.  For the
canonical radius r=t/16,

  integral G_t(v) cos(k v/16) dv
    = t * A_0(k r),

where A_0(s)=evenResp(g_t,0,s).  Substitution into the projective determinant
gives

  Phi_proj(t,0)
    = 4t [A_0(2r) A_0(r) - A_0(r) A_0(2r)]
    = 0.

No zero distribution theorem is used.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/--
Exact scaling of the on-line cosine response into the fixed normalized profile.
-/
theorem integral_normalizedCanonicalFixedProfile_cos_scale
    {t k : ℝ} (ht : 0 < t) :
    (∫ v : ℝ,
      normalizedCanonicalFixedProfile t v
        * Real.cos (k * v / 16))
      =
    t * onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (k * quantitativeSampleRadius t) := by
  let F : ℝ → ℝ := fun v =>
    normalizedCanonicalFixedProfile t v * Real.cos (k * v / 16)
  have hpoint :
      (fun u : ℝ =>
        quantitativeCanonicalTaper t u
          * Real.cos ((k * quantitativeSampleRadius t) * u))
      =
      fun u : ℝ => F (t * u) := by
    funext u
    dsimp [F]
    have htne : t ≠ 0 := ne_of_gt ht
    have hfixed :
        quantitativeCanonicalTaper t u
          = normalizedCanonicalFixedProfile t (t*u) := by
      have htu : (t*u)/t = u := by
        field_simp [htne]
      rw [← htu]
      exact normalizedCanonicalTaper_eq_fixedProfile ht
    rw [hfixed]
    congr 1
    unfold quantitativeSampleRadius
    field_simp [htne]
    ring
  have hscale := Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1 / t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  have hresp :
      onLineRadiusProfile
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t)
        =
      ∫ u : ℝ,
        quantitativeCanonicalTaper t u
          * Real.cos ((k * quantitativeSampleRadius t) * u) := by
    unfold onLineRadiusProfile evenResp
    simp
  rw [hresp, hpoint]
  have hscaled :
      (∫ u : ℝ, F (t*u))
        =
      (1/t) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hscaled]
  field_simp [htne]
  ring

theorem integral_normalizedCanonicalFixedProfile_cos_one
    {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ,
      normalizedCanonicalFixedProfile t v * Real.cos (v / 16))
      =
    t * onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t) := by
  simpa using
    integral_normalizedCanonicalFixedProfile_cos_scale
      (t := t) (k := 1) ht

theorem integral_normalizedCanonicalFixedProfile_cos_two
    {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ,
      normalizedCanonicalFixedProfile t v * Real.cos (v / 8))
      =
    t * onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t) := by
  have h :=
    integral_normalizedCanonicalFixedProfile_cos_scale
      (t := t) (k := 2) ht
  simpa [show (2:ℝ) * (1:ℝ) = 2 by norm_num] using h

/--
The exact projective base test kills q=0, hence every SameOrd(t) atom.
-/
theorem normalizedProjectiveBaseTransform_zero
    {t : ℝ} (ht : 0 < t) :
    normalizedProjectiveBaseTransform t 0 = 0 := by
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine]
  simp only [zero_mul, Real.cos_zero, mul_one]
  unfold normalizedProjectivePhysicalProfile
  let A1 : ℝ :=
    onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
  let A2 : ℝ :=
    onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t)
  have hi1 :
      Integrable
        (fun v : ℝ =>
          normalizedCanonicalFixedProfile t v * Real.cos (v/8)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedCanonicalFixedProfile_compact t).mul_right)
  have hi2 :
      Integrable
        (fun v : ℝ =>
          normalizedCanonicalFixedProfile t v * Real.cos (v/16)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedCanonicalFixedProfile_compact t).mul_right)
  calc
    (∫ v : ℝ,
      4 * normalizedCanonicalFixedProfile t v
        * (A1 * Real.cos (v/8) - A2 * Real.cos (v/16)))
      =
    4 * (A1 * (∫ v : ℝ,
          normalizedCanonicalFixedProfile t v * Real.cos (v/8))
        - A2 * (∫ v : ℝ,
          normalizedCanonicalFixedProfile t v * Real.cos (v/16))) := by
      rw [← integral_const_mul]
      rw [← integral_sub (hi1.const_mul A1) (hi2.const_mul A2)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by ring
    _ =
    4 * (A1 * (t*A2) - A2 * (t*A1)) := by
      rw [integral_normalizedCanonicalFixedProfile_cos_two ht,
          integral_normalizedCanonicalFixedProfile_cos_one ht]
      rfl
    _ = 0 := by ring

end Synthesis
