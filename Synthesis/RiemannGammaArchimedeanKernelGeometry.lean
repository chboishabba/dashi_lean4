import Synthesis.RiemannGammaBracketOrder
import Synthesis.RiemannPoleWindowDeweighting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Geometry of the archimedean Gamma kernel

The digamma partial-fraction series points to the positive kernel

    K(u) = exp(-u/2) / (1 - exp(-2u)),   u > 0.

Indeed each reciprocal term
  a / (a^2 + x^2/4)
has cosine transform proportional to exp(-2a|u|), and the geometric series over
a = 1/4, 5/4, 9/4, ... sums to K.

This file pays the elementary real-variable geometry needed before the full
series/Fubini transport:

* K is strictly positive on u>0;
* K is strictly decreasing on u>0;
* the centered modulation weight 1-cos((t/16)u) is increasing on the canonical
  positive support window;
* the pole-annihilation weight cos((t/16)u) is positive there.

These are the comparison ingredients for the two-window Gamma sign argument.
-/

noncomputable section

open scoped Real

namespace Synthesis

def gammaArchKernel (u : ℝ) : ℝ :=
  Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

theorem gammaArchKernel_denom_pos {u : ℝ} (hu : 0 < u) :
    0 < 1 - Real.exp (-2 * u) := by
  have hneg : -2 * u < 0 := by linarith
  have hexp : Real.exp (-2 * u) < 1 := by
    simpa using (Real.exp_lt_one_iff.mpr hneg)
  linarith

theorem gammaArchKernel_pos {u : ℝ} (hu : 0 < u) :
    0 < gammaArchKernel u := by
  unfold gammaArchKernel
  exact div_pos (Real.exp_pos _) (gammaArchKernel_denom_pos hu)

theorem gammaArchKernel_eq_inv_two_sinh {u : ℝ} (hu : 0 < u) :
    gammaArchKernel u = 1 / (2 * Real.sinh u) := by
  unfold gammaArchKernel
  have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  have h2e : Real.exp (2 * u) ≠ 0 := (Real.exp_pos (2*u)).ne'
  rw [Real.sinh_eq]
  field_simp [he, h2e, Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  ring

theorem gammaArchKernel_strictAntiOn_pos :
    StrictAntiOn gammaArchKernel (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [gammaArchKernel_eq_inv_two_sinh hx,
      gammaArchKernel_eq_inv_two_sinh hy]
  have hsx : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hsy : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hsxy : Real.sinh x < Real.sinh y :=
    Real.strictMono_sinh hxy
  exact one_div_lt_one_div_of_lt
    (mul_pos (by norm_num) hsx)
    (mul_lt_mul_of_pos_left hsxy (by norm_num))

def centeredRadiusWeight (t u : ℝ) : ℝ :=
  1 - Real.cos ((t / 16) * u)

def poleRadiusWeight (t u : ℝ) : ℝ :=
  Real.cos ((t / 16) * u)

theorem canonical_radius_angle_bounds
    {t u : ℝ} (ht : 0 < t)
    (hu0 : 0 <= u)
    (hu : u <= 9 * Real.pi / (4 * t)) :
    0 <= (t / 16) * u
      ∧ (t / 16) * u <= 9 * Real.pi / 64
      ∧ (t / 16) * u < Real.pi / 2 := by
  have hfac : 0 < t / 16 := by positivity
  have h0 : 0 <= (t / 16) * u :=
    mul_nonneg hfac.le hu0
  have h9 :
      (t / 16) * u <= 9 * Real.pi / 64 := by
    have hm := mul_le_mul_of_nonneg_left hu hfac.le
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp [ht0] at hm ⊢
    nlinarith [Real.pi_pos]
  constructor
  · exact h0
  constructor
  · exact h9
  · nlinarith [Real.pi_pos]

theorem poleRadiusWeight_pos_on_canonical_support
    {t u : ℝ} (ht : 0 < t)
    (hu0 : 0 <= u)
    (hu : u <= 9 * Real.pi / (4 * t)) :
    0 < poleRadiusWeight t u := by
  unfold poleRadiusWeight
  obtain ⟨h0, -, hpi2⟩ := canonical_radius_angle_bounds ht hu0 hu
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

theorem centeredRadiusWeight_nonneg
    (t u : ℝ) :
    0 <= centeredRadiusWeight t u := by
  unfold centeredRadiusWeight
  linarith [Real.cos_le_one ((t/16)*u)]

theorem centeredRadiusWeight_mono_on_canonical
    {t u v : ℝ} (ht : 0 < t)
    (hu0 : 0 <= u)
    (huv : u <= v)
    (hv : v <= 9 * Real.pi / (4 * t)) :
    centeredRadiusWeight t u <= centeredRadiusWeight t v := by
  unfold centeredRadiusWeight
  have hv0 : 0 <= v := le_trans hu0 huv
  obtain ⟨hau0, -, haupi⟩ :=
    canonical_radius_angle_bounds ht hu0 (le_trans huv hv)
  obtain ⟨hav0, -, havpi⟩ :=
    canonical_radius_angle_bounds ht hv0 hv
  have hang : (t/16)*u <= (t/16)*v :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  have hcos :
      Real.cos ((t/16)*v) <= Real.cos ((t/16)*u) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      hau0 (by linarith [havpi, Real.pi_pos]) hang
  linarith

theorem poleRadiusWeight_antitone_on_canonical
    {t u v : ℝ} (ht : 0 < t)
    (hu0 : 0 <= u)
    (huv : u <= v)
    (hv : v <= 9 * Real.pi / (4 * t)) :
    poleRadiusWeight t v <= poleRadiusWeight t u := by
  unfold poleRadiusWeight
  have hv0 : 0 <= v := le_trans hu0 huv
  obtain ⟨hau0, -, -⟩ :=
    canonical_radius_angle_bounds ht hu0 (le_trans huv hv)
  obtain ⟨-, -, havpi⟩ :=
    canonical_radius_angle_bounds ht hv0 hv
  have hang : (t/16)*u <= (t/16)*v :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  exact Real.cos_le_cos_of_nonneg_of_le_pi
    hau0 (by linarith [havpi, Real.pi_pos]) hang

end Synthesis
