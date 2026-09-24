/-
# The outward-rescaling audit of the ancient oscillation contraction

`AncientOscillationContraction.lean` reduces the frontier item **C** to a single
unit-scale oscillation improvement, via

  `contraction_of_unit_step` :
    a class `Cls` closed under the parabolic rescaling `U_λ(y,s) = λU(λy,λ²s)`
    for **all** `λ > 0`, plus one improvement `osc_{Q_θ} ≤ (1−σ)osc_{Q_1}`,
    gives the contraction at every scale.

The De Giorgi machinery of `DeGiorgiRecurrence.lean` naturally produces the
improvement for the KNSŠ-normalized class `‖U‖_∞ ≤ 1`.  This file audits whether
that class may legitimately be plugged into the reduction.  The answer is no,
and the failure is sharp:

* `ClayNS.unitNormClass_parRescale_inward` — the normalized class **is** closed
  under *inward* rescaling `0 < λ ≤ 1`.
* `ClayNS.not_unitNormClass_parRescale_outward` — for every `λ > 1` there is a
  normalized field whose outward rescaling `U_λ` leaves the class
  (`‖U_λ‖_∞ = λ`), so the closure hypothesis of `contraction_of_unit_step`
  **fails** for this class: `ClayNS.unitNormClass_not_rescaling_closed`.
* `ClayNS.contraction_of_unit_step_inward` — what inward closure alone actually
  buys: the contraction at scales `R ≤ 1` only.
* `ClayNS.exists_nonconstant_of_smallScale_contraction` — and that is genuinely
  not enough: there is a normalized field which contracts at *every* scale
  `R ≤ 1` (for any `θ`, `σ`) and is *not* constant on the ancient region.  So a
  De Giorgi iteration performed at one fixed unit cylinder, however strong,
  cannot by itself close the ancient Liouville step; the oscillation improvement
  must hold for a genuinely Navier–Stokes-scale-invariant class.

This is the formal content of the correctness condition attached to
`IncrementDeGiorgiRecurrence`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.AncientOscillationContraction

open Metric Set

noncomputable section

namespace ClayNS

/-- The KNSŠ normalization: the class of fields with `‖U‖_∞ ≤ 1`. -/
def unitNormClass (U : STime → E3) : Prop := ∀ z, ‖U z‖ ≤ 1

/-- **Inward closure.**  The normalized class is closed under the parabolic
rescaling `U_λ` for `0 < λ ≤ 1`. -/
theorem unitNormClass_parRescale_inward {U : STime → E3} (hU : unitNormClass U)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : unitNormClass (parRescale U lam) := by
  intro z
  have : ‖parRescale U lam z‖ = lam * ‖U (lam ^ 2 * z.1, lam • z.2)‖ := by
    rw [parRescale, norm_smul, Real.norm_eq_abs, abs_of_pos h0]
  rw [this]
  calc lam * ‖U (lam ^ 2 * z.1, lam • z.2)‖ ≤ lam * 1 :=
        mul_le_mul_of_nonneg_left (hU _) h0.le
    _ = lam := mul_one _
    _ ≤ 1 := h1

/-- A concrete unit vector of `E3`. -/
def unitE3 : E3 := EuclideanSpace.single 0 (1 : ℝ)

lemma norm_unitE3 : ‖unitE3‖ = 1 := by
  simp [unitE3, EuclideanSpace.norm_single]

lemma unitE3_ne_zero : unitE3 ≠ 0 := by
  intro h
  have := congrArg (fun v : E3 => v 0) h
  simp [unitE3, EuclideanSpace.single_apply] at this

/-- **Outward closure fails.**  For every `λ > 1` the normalized class contains a
field whose outward parabolic rescaling is no longer normalized. -/
theorem not_unitNormClass_parRescale_outward {lam : ℝ} (hlam : 1 < lam) :
    ∃ U : STime → E3, unitNormClass U ∧ ¬ unitNormClass (parRescale U lam) := by
  refine ⟨fun _ => unitE3, fun _ => le_of_eq norm_unitE3, ?_⟩
  intro hcon
  have h := hcon (0, 0)
  have hnorm : ‖parRescale (fun _ : STime => unitE3) lam (0, 0)‖ = lam := by
    rw [parRescale, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < lam),
      norm_unitE3, mul_one]
  rw [hnorm] at h
  linarith

/-- The closure hypothesis of `contraction_of_unit_step` is *false* for the
KNSŠ-normalized class. -/
theorem unitNormClass_not_rescaling_closed :
    ¬ ∀ (U : STime → E3) (lam : ℝ), unitNormClass U → 0 < lam →
      unitNormClass (parRescale U lam) := by
  intro h
  obtain ⟨U, hU, hbad⟩ := not_unitNormClass_parRescale_outward (lam := 2) (by norm_num)
  exact hbad (h U 2 hU (by norm_num))

/-- **What inward closure alone buys.**  A class closed under *inward* parabolic
rescaling with a unit-scale oscillation improvement contracts at every scale
`R ≤ 1`, and only there. -/
theorem contraction_of_unit_step_inward (Cls : (STime → E3) → Prop) {theta sig : ℝ}
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → lam ≤ 1 →
      Cls (parRescale U lam))
    (hstep : ∀ U : STime → E3, Cls U → oscCyl U theta ≤ (1 - sig) * oscCyl U 1)
    (U : STime → E3) (hU : Cls U) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R := by
  have hUR : Cls (parRescale U R) := hclosed U R hU hR hR1
  have h := hstep (parRescale U R) hUR
  rw [oscCyl_parRescale U hR theta, oscCyl_parRescale U hR 1, mul_one] at h
  have hfinal : oscCyl U (R * theta) ≤ (1 - sig) * oscCyl U R :=
    le_of_mul_le_mul_left
      (by linarith : R * oscCyl U (R * theta) ≤ R * ((1 - sig) * oscCyl U R)) hR
  rwa [mul_comm theta R]

/-- Small parabolic cylinders sit inside the unit one. -/
lemma parCyl_subset_one {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) : parCyl R ⊆ parCyl 1 := by
  rintro z ⟨h1, h2, h3⟩
  refine ⟨?_, h2, lt_of_lt_of_le h3 hR1⟩
  have : R ^ 2 ≤ 1 := by nlinarith
  have : -(1:ℝ) ≤ -(R ^ 2) := by linarith
  calc -((1:ℝ) ^ 2) = -(1:ℝ) := by norm_num
    _ ≤ -(R ^ 2) := this
    _ < z.1 := h1

/-- The witness field: zero on the unit parabolic cylinder (indeed on the whole
slab `‖x‖ < 2`), and equal to a unit vector far away. -/
def farBump : STime → E3 := fun z => if ‖z.2‖ < 2 then 0 else unitE3

lemma farBump_norm_le (z : STime) : ‖farBump z‖ ≤ 1 := by
  by_cases h : ‖z.2‖ < 2 <;> simp [farBump, h, norm_unitE3]

lemma farBump_eq_zero_of_mem_parCyl_one {z : STime} (hz : z ∈ parCyl 1) : farBump z = 0 := by
  have h : ‖z.2‖ < 2 := lt_trans hz.2.2 (by norm_num)
  simp [farBump, h]

/-- **The no-go for the fixed-normalization De Giorgi step.**  There is a
KNSŠ-normalized field which satisfies the oscillation contraction at *every*
scale `R ≤ 1` — for arbitrary `θ ∈ (0,1]` and arbitrary `σ` — and which is
nevertheless not constant on the ancient region.  Hence an oscillation
improvement obtained at one fixed unit cylinder, without scale invariance of the
class, cannot be welded to `ancient_constant_of_oscillation_contraction`. -/
theorem exists_nonconstant_of_smallScale_contraction {theta sig : ℝ}
    (hth0 : 0 < theta) (hth1 : theta ≤ 1) :
    ∃ U : STime → E3, unitNormClass U ∧
      (∀ R : ℝ, 0 < R → R ≤ 1 → oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R) ∧
      ¬ ∃ b : E3, ∀ z : STime, z.1 ≤ 0 → U z = b := by
  have hzero : ∀ R : ℝ, 0 < R → R ≤ 1 → oscCyl farBump R = 0 := by
    intro R hR hR1
    refine le_antisymm ?_ (oscCyl_nonneg _ _)
    simp only [oscCyl, oscOn]
    refine Metric.diam_le_of_forall_dist_le le_rfl ?_
    rintro p ⟨z, hz, rfl⟩ q ⟨w, hw, rfl⟩
    rw [farBump_eq_zero_of_mem_parCyl_one (parCyl_subset_one hR hR1 hz),
      farBump_eq_zero_of_mem_parCyl_one (parCyl_subset_one hR hR1 hw)]
    simp
  refine ⟨farBump, farBump_norm_le, ?_, ?_⟩
  · intro R hR hR1
    have h1 : oscCyl farBump (theta * R) = 0 :=
      hzero (theta * R) (by positivity) (by nlinarith)
    have h2 : oscCyl farBump R = 0 := hzero R hR hR1
    rw [h1, h2, mul_zero]
  · rintro ⟨b, hb⟩
    have h0 : farBump (0, 0) = b := hb (0, 0) le_rfl
    have hb0 : b = 0 := by
      rw [← h0]
      simp [farBump]
    have hfar : farBump (0, (3 : ℝ) • unitE3) = unitE3 := by
      have : ‖(3 : ℝ) • unitE3‖ = 3 := by
        rw [norm_smul, Real.norm_eq_abs, norm_unitE3]
        norm_num
      simp [farBump, this, (by norm_num : ¬ (3:ℝ) < 2)]
    have := hb (0, (3 : ℝ) • unitE3) le_rfl
    rw [hfar, hb0] at this
    exact unitE3_ne_zero this

end ClayNS
