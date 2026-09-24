/-
# Lifting the radial scale probe to three dimensions

`ScaleProbeExistence.lean` constructs, by a logarithmic pigeonhole, a
one-dimensional cut-off `χ` whose homogeneous probe is blind to the radial
scaling generator up to any prescribed tolerance.  That construction was stated
for the radial reduction "up to the angular factor".  This file removes the
caveat for *radial* fields: it identifies the angular factor exactly and shows
that the radial reduction of the dilation generator is not an analogy but an
identity.

* `ClayNS.radialField` — the radial vector field `V(|x|)·x/|x|` attached to a
  profile.
* `ClayNS.radialField_dot` — the pointwise pairing of two radial fields is the
  product of their profiles.
* `ClayNS.radialField_fderiv_self` — the exact directional derivative along the
  ray, `(Df)(x)x = V'(|x|)·x`.  Proved from the derivative of the norm at a
  nonzero point, which is obtained from the derivative of `‖·‖²`.
* `ClayNS.radialField_dilation` — **the dilation identity**: for a radial field,

    `U(x) + (DU)(x)x = radialField (radGen V V') x`,

  so the one-dimensional generator `ΛV = V + rV'` of `ScaleProbeRadial.lean` *is*
  the spatial dilation generator, exactly.
* `ClayNS.radialField_integral_polar` — **the angular factor**: integrating a
  pairing of radial fields over `ℝ³` multiplies the radial probe by
  `3·vol(B₁) = 4π`; there is no other loss.
* `ClayNS.radialField_probe_eq` — the two combined: a compactly supported radial
  weight has 3-D probe equal to `4π` times its radial probe.
* `ClayNS.exists_small_residual_radial_probe_3d` — **the conclusion**: for a
  radial profile there is an honest three-dimensional weight `w` on `ℝ³`,
  compactly supported away from the origin, with

    `|∫⟨w, ΛU⟩| ≤ ε`  and  `∫⟨w, U⟩ ≥ 4π·(core mass)`,

  where `ΛU` is the actual spatial dilation generator of `U`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleProbeExistence
import RequestProject.NavierStokes.AncientLiouville

open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Radial fields -/

/-- The radial vector field with profile `V`: `x ↦ V(|x|)·x/|x|`. -/
def radialField (V : ℝ → ℝ) : E3 → E3 := fun y => (V ‖y‖ / ‖y‖) • y

lemma radialField_apply (V : ℝ → ℝ) (y : E3) (a : Fin 3) :
    radialField V y a = (V ‖y‖ / ‖y‖) * y a := rfl

/-- The pointwise pairing of two radial fields is the product of the profiles. -/
lemma radialField_dot (Phi V : ℝ → ℝ) {x : E3} (hx : x ≠ 0) :
    ∑ a, radialField Phi x a * radialField V x a = Phi ‖x‖ * V ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hstep : ∀ a : Fin 3, radialField Phi x a * radialField V x a
      = (Phi ‖x‖ / ‖x‖ * (V ‖x‖ / ‖x‖)) * (x a * x a) := by
    intro a; simp only [radialField_apply]; ring
  rw [Finset.sum_congr rfl fun a _ => hstep a, ← Finset.mul_sum, sum_sq_eq_norm_sq]
  field_simp

/-! ## The derivative of a radial field along the ray -/

/-- The derivative of the norm at a nonzero point, obtained from the derivative
of `‖·‖²`. -/
theorem hasFDerivAt_norm_of_ne {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖) ((‖x‖⁻¹ : ℝ) • (innerSL ℝ x)) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hd : DifferentiableAt ℝ (fun y : E3 => ‖y‖) x :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun y : E3 => ‖y‖) (fderiv ℝ (fun y : E3 => ‖y‖) x) x := hd.hasFDerivAt
  have h2 := h1.pow 2
  have h3 : fderiv ℝ (fun y : E3 => ‖y‖ ^ 2) x = 2 • (innerSL ℝ x) := fderiv_norm_sq_apply x
  rw [h2.fderiv] at h3
  have h4 : ((2 : ℝ) * ‖x‖) • fderiv ℝ (fun y : E3 => ‖y‖) x = (2 : ℝ) • (innerSL ℝ x) := by
    rw [show ((2 : ℕ) • (innerSL ℝ x) : E3 →L[ℝ] ℝ) = (2 : ℝ) • (innerSL ℝ x) by
      simp [two_smul]] at h3
    simpa using h3
  have h5 : fderiv ℝ (fun y : E3 => ‖y‖) x = (‖x‖⁻¹ : ℝ) • (innerSL ℝ x) := by
    have h6 := congrArg (fun L => ((2 * ‖x‖)⁻¹ : ℝ) • L) h4
    simp only [smul_smul] at h6
    rw [inv_mul_cancel₀ (by positivity : (2 : ℝ) * ‖x‖ ≠ 0), one_smul] at h6
    rw [h6]
    congr 1
    field_simp
  rwa [h5] at h1

theorem radialField_hasFDerivAt {V V' : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hV : HasDerivAt V (V' ‖x‖) ‖x‖) :
    HasFDerivAt (radialField V)
      ((V ‖x‖ / ‖x‖) • (ContinuousLinearMap.id ℝ E3)
        + (((V' ‖x‖ * ‖x‖ - V ‖x‖) / ‖x‖ ^ 2) •
            ((‖x‖⁻¹ : ℝ) • (innerSL ℝ x))).smulRight x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hh : HasDerivAt (fun r => V r / r) ((V' ‖x‖ * ‖x‖ - V ‖x‖) / ‖x‖ ^ 2) ‖x‖ := by
    simpa using hV.div (hasDerivAt_id ‖x‖) hn
  have hc : HasFDerivAt (fun y : E3 => V ‖y‖ / ‖y‖)
      (((V' ‖x‖ * ‖x‖ - V ‖x‖) / ‖x‖ ^ 2) • ((‖x‖⁻¹ : ℝ) • (innerSL ℝ x))) x :=
    hh.comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)
  exact hc.smul (hasFDerivAt_id x)

lemma radialField_differentiableAt {V V' : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hV : HasDerivAt V (V' ‖x‖) ‖x‖) : DifferentiableAt ℝ (radialField V) x :=
  (radialField_hasFDerivAt hx hV).differentiableAt

/-- **The directional derivative along the ray.**  For a radial field the
derivative in the radial direction is `V'(|x|)·x`: the `1/r` in the profile
cancels the derivative of the direction. -/
theorem radialField_fderiv_self {V V' : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hV : HasDerivAt V (V' ‖x‖) ‖x‖) :
    fderiv ℝ (radialField V) x x = (V' ‖x‖) • x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [(radialField_hasFDerivAt hx hV).fderiv]
  have hinner : (innerSL ℝ x) x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, hinner, smul_eq_mul]
  rw [← add_smul]
  congr 1
  field_simp
  ring

/-- **The dilation identity.**  The one-dimensional generator `ΛV = V + rV'` of
`ClayNS.radGen` is exactly the spatial dilation generator `U + (DU)·x` of the
associated radial field.  So the radial reduction of the scaling direction is an
identity, not an approximation. -/
theorem radialField_dilation {V V' : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hV : HasDerivAt V (V' ‖x‖) ‖x‖) :
    radialField V x + fderiv ℝ (radialField V) x x = radialField (radGen V V') x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [radialField_fderiv_self hx hV]
  simp only [radialField, radGen]
  rw [← add_smul]
  congr 1
  field_simp

/-! ## The angular factor -/

/-- The angular factor of the radial reduction: `3·vol(B₁)`, which is `4π`. -/
def angularFactor : ℝ := 3 * volume.real (Metric.ball (0 : E3) 1)

lemma angularFactor_nonneg : 0 ≤ angularFactor := by
  have h : (0 : ℝ) ≤ volume.real (Metric.ball (0 : E3) 1) := measureReal_nonneg
  unfold angularFactor
  linarith

/-- The angular factor is exactly `4π`. -/
theorem angularFactor_eq : angularFactor = 4 * Real.pi := by
  have hG : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
    have h1 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
    have h2 : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
      have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
      norm_num at h ⊢
      linarith [h]
    have h3 : Real.Gamma (5 / 2) = (3 / 2) * Real.Gamma (3 / 2) := by
      have h := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
      norm_num at h ⊢
      linarith [h]
    rw [h3, h2, h1]; ring
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hspos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hval : Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2) = 4 * Real.pi / 3 := by
    rw [hG]
    field_simp
    nlinarith [hs, hspos]
  have hball : volume.real (Metric.ball (0 : E3) 1) = 4 * Real.pi / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin]
    norm_num
    rw [hval, ENNReal.toReal_ofReal (by positivity)]
  unfold angularFactor
  rw [hball]
  ring

/-- **The angular factor, exactly.**  Integrating the pairing of two radial
fields over `ℝ³` is the radial integral against `r²dr`, times `3·vol(B₁)`. -/
theorem radialField_integral_polar (Phi V : ℝ → ℝ) :
    ∫ x : E3, ∑ a, radialField Phi x a * radialField V x a
      = angularFactor * ∫ r in Ioi (0 : ℝ), r ^ 2 * (Phi r * V r) := by
  have hae : ∀ᵐ x : E3 ∂volume, x ≠ 0 := by
    have hset : {x : E3 | ¬ (x ≠ 0)} = {0} := by ext x; simp
    rw [MeasureTheory.ae_iff, hset]
    simp
  have h1 : (∫ x : E3, ∑ a, radialField Phi x a * radialField V x a)
      = ∫ x : E3, (fun r => Phi r * V r) ‖x‖ :=
    integral_congr_ae (hae.mono fun x hx => radialField_dot Phi V hx)
  rw [h1, MeasureTheory.integral_fun_norm_addHaar volume (fun r => Phi r * V r)]
  simp only [angularFactor, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  norm_num
  ring

/-- A compactly supported radial integral is an interval integral. -/
lemma integral_Ioi_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ r, r ≤ a ∨ b ≤ r → f r = 0) :
    (∫ r in Ioi (0 : ℝ), f r) = ∫ r in a..b, f r := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (fun z hz' => lt_trans ha hz'.1) ?_
  intro z hzmem
  rcases le_or_gt z a with h | h
  · exact hz z (Or.inl h)
  · refine hz z (Or.inr ?_)
    by_contra hcon
    exact hzmem.2 ⟨h, le_of_not_ge hcon⟩

/-- **The lifted probe.**  For a radial weight with profile `Φ` supported in
`[a,b] ⊂ (0,∞)`, the three-dimensional probe against a radial field is
`4π` times the one-dimensional probe. -/
theorem radialField_probe_eq {Phi V : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz : ∀ r, r ≤ a ∨ b ≤ r → Phi r = 0) :
    ∫ x : E3, ∑ j, radialField Phi x j * radialField V x j
      = angularFactor * radProbe Phi V a b := by
  rw [radialField_integral_polar Phi V]
  congr 1
  rw [integral_Ioi_eq_intervalIntegral_of_support ha hab
    (fun r hr => by rw [hz r hr]; ring)]
  unfold radProbe
  exact intervalIntegral.integral_congr fun r _ => by ring

/-! ## The three-dimensional separating probe -/

/-- **A three-dimensional scale probe with arbitrarily small residual.**  Let `V`
be a nonnegative `C¹` profile with uniformly bounded mass, and let `U =
radialField V` be the associated radial field on `ℝ³`.  For every tolerance
`ε > 0` there is a weight `w` — itself a radial field, with profile supported in
a compact annulus away from the origin — such that

  `|∫⟨w, ΛU⟩| ≤ 4π·ε`  and  `∫⟨w, U⟩ ≥ 4π·(core mass)`,

where `ΛU(x) = U(x) + (DU)(x)x` is the genuine spatial dilation generator.  The
angular factor is the *same* on both sides, so the separation margin of the
radial construction survives the lift intact. -/
theorem exists_small_residual_radial_probe_3d
    {V V' : ℝ → ℝ} {c1 c2 T eps : ℝ} (hc1 : 0 < c1) (hc12 : c1 < c2) (heps : 0 < eps)
    (hV : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt V (V' r) r)
    (hV'c : ContinuousOn V' (Ioi 0))
    (hVnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ V r)
    (hmass : ∀ x y : ℝ, 0 < x → x ≤ y → (∫ r in x..y, V r) ≤ T) :
    ∃ (Phi : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a < b ∧
      (∀ r, r ≤ a ∨ b ≤ r → Phi r = 0) ∧
      (∀ x : E3, x ≠ 0 →
        radialField (radGen V V') x = radialField V x + fderiv ℝ (radialField V) x x) ∧
      |∫ x : E3, ∑ j, radialField Phi x j * radialField (radGen V V') x j|
          ≤ angularFactor * eps ∧
      angularFactor * (∫ r in c1..c2, V r)
        ≤ ∫ x : E3, ∑ j, radialField Phi x j * radialField V x j := by
  obtain ⟨chi, chi', a, b, ha, hab, hd, hc', h0a, h0b, hnn, hle1, hone, hsupp, hres, hbulk⟩ :=
    exists_small_residual_radial_probe (V := V) (V' := V') (T := T) (eps := eps)
      hc1 hc12 heps hV hV'c hVnn hmass
  have hPhi0 : ∀ r, r ≤ a ∨ b ≤ r → chi r / r ^ 2 = 0 := by
    intro r hr
    rw [hsupp r hr, zero_div]
  have hdil : ∀ x : E3, x ≠ 0 →
      radialField (radGen V V') x = radialField V x + fderiv ℝ (radialField V) x x := by
    intro x hx
    exact (radialField_dilation hx (hV ‖x‖ (norm_pos_iff.2 hx))).symm
  refine ⟨fun r => chi r / r ^ 2, a, b, ha, hab, hPhi0, hdil, ?_, ?_⟩
  · rw [radialField_probe_eq (Phi := fun r => chi r / r ^ 2) (V := radGen V V') ha hab.le hPhi0,
      abs_mul, abs_of_nonneg angularFactor_nonneg]
    exact mul_le_mul_of_nonneg_left hres angularFactor_nonneg
  · rw [radialField_probe_eq (Phi := fun r => chi r / r ^ 2) (V := V) ha hab.le hPhi0]
    exact mul_le_mul_of_nonneg_left hbulk angularFactor_nonneg

end ClayNS
