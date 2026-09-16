/-
# The SU(2) principal chart: small operator defect admits a logarithm

The Eq. (119) chain needs, at the point where `Y_x = (1/i) log (U(Γ_{c,x}) U(c)⁻¹)`
is introduced, a genuine chart theorem:

  small operator defect  ⟹  the group element is `exp` of a Lie-algebra element,

with the logarithm on the principal branch.  This module proves that for
`SU(2)`, in the quaternion model, with no recognition receipt and no interface:

* `exp_qlog` — every unit quaternion with `-1 < re` is the exponential of the
  explicit imaginary quaternion `qlog u = (arccos u.re / ‖u.im‖) • u.im`;
* `norm_qlog` — its norm is exactly `arccos u.re`, hence `< π`: this is the
  principal branch;
* `su2AlgHom` — the `2 × 2` representation is an `ℝ`-algebra homomorphism, so it
  intertwines the quaternion and matrix exponentials;
* `principal_chart_of_defect_le` — the consumer form: an operator defect
  `‖U - 1‖ ≤ δ < 1` produces `Y` with `Y.re = 0`, `‖Y‖ < π/2` and
  `exp (su2 Y) = U`.

Composed with the relative-holonomy telescope (`37/1024 < 1/24 < 1`), this
supplies chart admission for the literal relative holonomy.
-/
import Mathlib
import RequestProject.YangMills.SU2QuaternionOperatorNorm
import RequestProject.YangMills.RelativeHolonomyDefect

namespace RequestProject.YangMills.SU2PrincipalChart

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator
open RequestProject.YangMills.SU2QuaternionOperatorNorm
open RequestProject.YangMills.RelativeHolonomyDefect (IsUnitQuaternion)

/-! ## The quaternion principal logarithm -/

/-- The principal logarithm of a unit quaternion: the imaginary quaternion of
norm `arccos u.re` pointing along `u.im`. -/
noncomputable def qlog (u : Quaternion ℝ) : Quaternion ℝ :=
  if ‖u.im‖ = 0 then 0 else (Real.arccos u.re / ‖u.im‖) • u.im

@[simp] theorem qlog_re (u : Quaternion ℝ) : (qlog u).re = 0 := by
  unfold qlog
  split
  · simp
  · simp [Quaternion.re_im]

theorem norm_im_of_unit {u : Quaternion ℝ} (h : IsUnitQuaternion u) :
    ‖u.im‖ = Real.sqrt (1 - u.re ^ 2) := by
  have hsq : ‖u.im‖ ^ 2 = 1 - u.re ^ 2 := by
    have h1 : Quaternion.normSq u.im = ‖u.im‖ * ‖u.im‖ :=
      Quaternion.normSq_eq_norm_mul_self _
    have h2 : Quaternion.normSq u.im
        = u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 := by
      simp [Quaternion.normSq_def']
    have := h
    unfold IsUnitQuaternion at this
    nlinarith [h1, h2]
  have hnn : 0 ≤ ‖u.im‖ := norm_nonneg _
  rw [← hsq, Real.sqrt_sq hnn]

theorem re_le_one_of_unit {u : Quaternion ℝ} (h : IsUnitQuaternion u) : u.re ≤ 1 := by
  unfold IsUnitQuaternion at h
  nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK, sq_nonneg (u.re - 1),
    sq_nonneg (u.re + 1)]

theorem neg_one_le_re_of_unit {u : Quaternion ℝ} (h : IsUnitQuaternion u) : -1 ≤ u.re := by
  unfold IsUnitQuaternion at h
  nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK, sq_nonneg (u.re + 1)]

/-- A unit quaternion with vanishing imaginary part and `re > -1` is `1`. -/
theorem eq_one_of_unit_of_im_zero {u : Quaternion ℝ} (h : IsUnitQuaternion u)
    (hre : -1 < u.re) (him : ‖u.im‖ = 0) : u = 1 := by
  have hsq : Real.sqrt (1 - u.re ^ 2) = 0 := by rw [← norm_im_of_unit h, him]
  have hre1 : u.re = 1 := by
    have h2 : 1 - u.re ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      exact absurd hsq (ne_of_gt (Real.sqrt_pos.mpr hc))
    nlinarith [re_le_one_of_unit h]
  have hcomp : u.imI = 0 ∧ u.imJ = 0 ∧ u.imK = 0 := by
    unfold IsUnitQuaternion at h
    rw [hre1] at h
    refine ⟨by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK],
      by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK],
      by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK]⟩
  obtain ⟨h1, h2, h3⟩ := hcomp
  ext <;> simp [hre1, h1, h2, h3]

/-- The principal logarithm has norm exactly `arccos u.re`. -/
theorem norm_qlog {u : Quaternion ℝ} (h : IsUnitQuaternion u) (hre : -1 < u.re) :
    ‖qlog u‖ = Real.arccos u.re := by
  unfold qlog
  split_ifs with him
  · have hu1 : u = 1 := eq_one_of_unit_of_im_zero h hre him
    simp [hu1]
  · have hpos : 0 < ‖u.im‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm him)
    have hθ : 0 ≤ Real.arccos u.re := Real.arccos_nonneg _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp

/-- **The chart.**  Every unit quaternion other than `-1` is the exponential of
its principal logarithm. -/
theorem exp_qlog {u : Quaternion ℝ} (h : IsUnitQuaternion u) (hre : -1 < u.re) :
    exp (qlog u) = u := by
  have hle : u.re ≤ 1 := re_le_one_of_unit h
  have hge : -1 ≤ u.re := le_of_lt hre
  unfold qlog
  split_ifs with him
  · have hu1 : u = 1 := eq_one_of_unit_of_im_zero h hre him
    simp [hu1]
  · have hpos : 0 < ‖u.im‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm him)
    set θ := Real.arccos u.re with hθdef
    have hθnn : 0 ≤ θ := Real.arccos_nonneg _
    have hcos : Real.cos θ = u.re := Real.cos_arccos hge hle
    have hsin : Real.sin θ = ‖u.im‖ := by
      rw [hθdef, Real.sin_arccos, ← norm_im_of_unit h]
    have hθpos : 0 < θ := by
      rcases lt_or_eq_of_le hθnn with h' | h'
      · exact h'
      · exfalso
        rw [← h'] at hsin
        simp at hsin
        exact him hsin.symm
    set Y := (θ / ‖u.im‖) • u.im with hY
    have hYre : Y.re = 0 := by simp [hY, Quaternion.re_im]
    have hYnorm : ‖Y‖ = θ := by
      rw [hY, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    rw [Quaternion.exp_of_re_eq_zero Y hYre, hYnorm, hY, smul_smul]
    have hcoef : Real.sin θ / θ * (θ / ‖u.im‖) = 1 := by
      rw [hsin]
      field_simp
    rw [hcoef, one_smul, hcos]
    exact u.re_add_im

/-- The principal branch: the logarithm lies in the ball of radius `π`. -/
theorem norm_qlog_lt_pi {u : Quaternion ℝ} (h : IsUnitQuaternion u) (hre : -1 < u.re) :
    ‖qlog u‖ < Real.pi := by
  rw [norm_qlog h hre]
  have := Real.arccos_lt_pi (x := u.re)
  exact this.mpr hre

theorem norm_qlog_lt_pi_div_two {u : Quaternion ℝ} (h : IsUnitQuaternion u)
    (hre : 0 < u.re) : ‖qlog u‖ < Real.pi / 2 := by
  rw [norm_qlog h (by linarith)]
  exact Real.arccos_lt_pi_div_two.mpr hre

/-! ## Transport to the matrix representation -/

/-- The quaternion representation as an `ℝ`-algebra homomorphism. -/
noncomputable def su2AlgHom : Quaternion ℝ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := su2
  map_one' := su2_one
  map_mul' := su2_mul
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su2]
  map_add' := by
    intro p q
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2, Complex.ext_iff] <;> ring
  commutes' := by
    intro r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2, Algebra.algebraMap_eq_smul_one]

@[simp] theorem su2AlgHom_apply (q : Quaternion ℝ) : su2AlgHom q = su2 q := rfl

theorem continuous_su2 : Continuous su2 :=
  (su2AlgHom.toLinearMap.restrictScalars ℝ).continuous_of_finiteDimensional

/-- The representation intertwines the exponentials. -/
theorem su2_exp (q : Quaternion ℝ) : su2 (exp q) = exp (su2 q) := by
  letI : NormedAlgebra ℚ (Quaternion ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (Quaternion ℝ)
  simpa using map_exp su2AlgHom continuous_su2 q

/-! ## The consumer form -/

theorem abs_re_sub_one_le_defect (u : Quaternion ℝ) : |u.re - 1| ≤ ‖su2 u - 1‖ := by
  rw [su2_sub_one, su2_norm]
  have h1 : (u.re - 1) ^ 2
      ≤ (u - 1).re ^ 2 + (u - 1).imI ^ 2 + (u - 1).imJ ^ 2 + (u - 1).imK ^ 2 := by
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq_eq_abs] at h2

/-- **Chart admission from the defect estimate.**  A unit quaternion whose
represented matrix has operator defect `< 1` lies in the principal image: it is
`exp` of an explicit skew-Hermitian generator of norm `< π/2`. -/
theorem principal_chart_of_defect_lt_one {u : Quaternion ℝ} (hu : IsUnitQuaternion u)
    (h : ‖su2 u - 1‖ < 1) :
    ∃ Y : Quaternion ℝ, Y.re = 0 ∧ ‖Y‖ < Real.pi / 2 ∧ exp (su2 Y) = su2 u := by
  have habs : |u.re - 1| < 1 := lt_of_le_of_lt (abs_re_sub_one_le_defect u) h
  have hre : 0 < u.re := by
    have := abs_lt.mp habs
    linarith [this.1]
  refine ⟨qlog u, qlog_re u, norm_qlog_lt_pi_div_two hu hre, ?_⟩
  rw [← su2_exp, exp_qlog hu (by linarith)]

/-- The form used downstream: the `1/24` threshold of the relative-holonomy
telescope is comfortably inside the chart. -/
theorem principal_chart_of_defect_le_inv24 {u : Quaternion ℝ} (hu : IsUnitQuaternion u)
    (h : ‖su2 u - 1‖ ≤ 1 / 24) :
    ∃ Y : Quaternion ℝ, Y.re = 0 ∧ ‖Y‖ < Real.pi / 2 ∧ exp (su2 Y) = su2 u :=
  principal_chart_of_defect_lt_one hu (lt_of_le_of_lt h (by norm_num))

end RequestProject.YangMills.SU2PrincipalChart
