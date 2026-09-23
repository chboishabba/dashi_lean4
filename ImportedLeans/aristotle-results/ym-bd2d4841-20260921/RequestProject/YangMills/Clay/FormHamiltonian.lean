/-
# From a physical quadratic form to a self-adjoint Hamiltonian with a vacuum gap

The Yang–Mills operator lane in this library consumes a `VacuumGapDatum`: a
self-adjoint Hamiltonian `H`, a unit vacuum `Ω` with `HΩ = 0`, and a positive
form gap on `D(H) ∩ Ω^⊥`.  Physically one does **not** meet the Hamiltonian
first: one meets the energy *form* `q(Ψ, Φ)`, reads off the operator from it,
and only then asks about self-adjointness.  This file supplies that step in the
bounded (Riesz representation) case, so that the operator, its self-adjointness
and the vacuum condition are *produced* from form data rather than assumed
separately:

* `BoundedSesqForm` — a sesquilinear form on a complex Hilbert space, conjugate
  linear in the first slot, Hermitian, with `‖q x y‖ ≤ b‖x‖‖y‖`;
* `BoundedSesqForm.toCLM` — the associated bounded operator, characterised by
  `⟪z, H y⟫ = q z y` (`inner_toCLM`), constructed by Riesz representation;
* `BoundedSesqForm.isSelfAdjoint_toCLM` — Hermitian form ⇒ self-adjoint operator;
* `BoundedSesqForm.hamiltonian` — the same operator as a densely defined
  (indeed everywhere defined) unbounded operator, self-adjoint in the
  `LinearPMap` sense;
* `BoundedSesqForm.gapDatum` — **the compiler**: a form which annihilates the
  vacuum, `q z Ω = 0`, and is coercive on the vacuum complement,
  `b‖ψ‖² ≤ re q ψ ψ` for `ψ ⊥ Ω`, yields a `VacuumGapDatum` with gap `b`, hence
  (via `VacuumSectorSpectralGap`) the full vacuum-sector spectral conclusion.

Honest scope: nothing here constructs the Yang–Mills energy form.  What is
removed is the need to assume separately that the physical Hamiltonian exists,
is self-adjoint, kills the vacuum, and has a form gap: for a bounded form these
are one payment, namely the coercivity estimate `b‖ψ‖² ≤ re q ψ ψ` on `Ω^⊥`.
-/
import Mathlib
import RequestProject.YangMills.UnboundedFormGapResolvent
import RequestProject.YangMills.VacuumSectorSpectralGap

namespace RequestProject.YangMills.Clay

open scoped InnerProductSpace
open ComplexConjugate
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A bounded Hermitian sesquilinear form on a complex inner product space,
conjugate linear in the first argument and linear in the second (the convention
that matches `⟪x, H y⟫`). -/
structure BoundedSesqForm (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  /-- The form itself. -/
  form : E → E → ℂ
  /-- A continuity bound for the form. -/
  bound : ℝ
  /-- The continuity bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- Additivity in the first slot. -/
  add_left : ∀ x y z, form (x + y) z = form x z + form y z
  /-- Conjugate homogeneity in the first slot. -/
  smul_left : ∀ (c : ℂ) x y, form (c • x) y = conj c * form x y
  /-- Continuity. -/
  norm_le : ∀ x y, ‖form x y‖ ≤ bound * ‖x‖ * ‖y‖
  /-- The form is Hermitian. -/
  sesq_symm : ∀ x y, form x y = conj (form y x)

namespace BoundedSesqForm

variable (q : BoundedSesqForm E)

theorem add_right (x y z : E) : q.form x (y + z) = q.form x y + q.form x z := by
  rw [q.sesq_symm x (y + z), q.add_left, map_add, ← q.sesq_symm, ← q.sesq_symm]

theorem smul_right (c : ℂ) (x y : E) : q.form x (c • y) = c * q.form x y := by
  rw [q.sesq_symm x (c • y), q.smul_left, map_mul, ← q.sesq_symm]
  simp

/-- The Riesz functional `z ↦ conj (q z y)` of the form at `y`. -/
noncomputable def fnl (y : E) : E →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun z => conj (q.form z y)
      map_add' := by intro a b; simp [q.add_left, map_add]
      map_smul' := by intro c a; simp [q.smul_left] }
    (q.bound * ‖y‖) (by
      intro z
      have h := q.norm_le z y
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)

@[simp] theorem fnl_apply (y z : E) : q.fnl y z = conj (q.form z y) := rfl

variable [CompleteSpace E]

/-- The vector representing the form at `y`; this is `H y` for the associated
operator `H`. -/
noncomputable def opFun (y : E) : E := (InnerProductSpace.toDual ℂ E).symm (q.fnl y)

/-- **The defining identity of the associated operator.** -/
theorem inner_opFun (y z : E) : ⟪z, q.opFun y⟫_ℂ = q.form z y := by
  have h : ⟪q.opFun y, z⟫_ℂ = q.fnl y z := by
    rw [← InnerProductSpace.toDual_apply_apply (𝕜 := ℂ)]
    simp [opFun]
  rw [← inner_conj_symm, h]
  simp

theorem opFun_add (y y' : E) : q.opFun (y + y') = q.opFun y + q.opFun y' := by
  refine ext_inner_left ℂ ?_
  intro v
  rw [inner_opFun, inner_add_right, inner_opFun, inner_opFun, q.add_right]

theorem opFun_smul (c : ℂ) (y : E) : q.opFun (c • y) = c • q.opFun y := by
  refine ext_inner_left ℂ ?_
  intro v
  rw [inner_opFun, inner_smul_right, inner_opFun, q.smul_right]

theorem norm_opFun_le (y : E) : ‖q.opFun y‖ ≤ q.bound * ‖y‖ := by
  have h : ‖q.opFun y‖ = ‖q.fnl y‖ := by simp [opFun]
  rw [h]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg q.bound_nonneg (norm_nonneg y)) _

/-- **The bounded operator associated with the form.** -/
noncomputable def toCLM : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := q.opFun
      map_add' := q.opFun_add
      map_smul' := by intro c y; simpa using q.opFun_smul c y }
    q.bound q.norm_opFun_le

@[simp] theorem toCLM_apply (y : E) : q.toCLM y = q.opFun y := rfl

/-- The associated operator represents the form: `⟪z, H y⟫ = q z y`. -/
theorem inner_toCLM (y z : E) : ⟪z, q.toCLM y⟫_ℂ = q.form z y := q.inner_opFun y z

/-- A Hermitian form has a self-adjoint associated operator. -/
theorem isSelfAdjoint_toCLM : IsSelfAdjoint q.toCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have hc : conj ⟪v, q.toCLM u⟫_ℂ = ⟪q.toCLM u, v⟫_ℂ := inner_conj_symm _ _
  calc ⟪q.toCLM u, v⟫_ℂ = conj ⟪v, q.toCLM u⟫_ℂ := hc.symm
    _ = conj (q.form v u) := by rw [inner_toCLM]
    _ = q.form u v := (q.sesq_symm u v).symm
    _ = ⟪u, q.toCLM v⟫_ℂ := (inner_toCLM q v u).symm

/-- The associated operator as an (everywhere defined) unbounded operator, the
shape the vacuum-sector machinery consumes. -/
noncomputable def hamiltonian : E →ₗ.[ℂ] E := LinearMap.toPMap (q.toCLM : E →ₗ[ℂ] E) ⊤

@[simp] theorem hamiltonian_domain : q.hamiltonian.domain = ⊤ := rfl

@[simp] theorem hamiltonian_apply (ψ : q.hamiltonian.domain) :
    q.hamiltonian ψ = q.toCLM (ψ : E) := rfl

theorem isSelfAdjoint_hamiltonian : IsSelfAdjoint q.hamiltonian :=
  UnboundedFormGapResolvent.isSelfAdjoint_toPMap_top q.isSelfAdjoint_toCLM

/-- A vector annihilated by the form is a zero-energy state of the associated
operator: this is how the vacuum condition `HΩ = 0` is *produced*. -/
theorem hamiltonian_apply_eq_zero {vac : E} (hvac : ∀ z, q.form z vac = 0) :
    q.hamiltonian ⟨vac, Submodule.mem_top⟩ = 0 := by
  have h : q.toCLM vac = 0 := by
    refine ext_inner_left ℂ ?_
    intro v
    rw [inner_toCLM, hvac, inner_zero_right]
  simpa using h

/-- **Coercivity of the form on the vacuum complement gives the form gap of the
operator.** -/
theorem hasVacuumFormGap_hamiltonian {vac : E} {b : ℝ}
    (hcoer : ∀ ψ : E, ⟪vac, ψ⟫_ℂ = 0 → b * ‖ψ‖ ^ 2 ≤ (q.form ψ ψ).re) :
    HasVacuumFormGap q.hamiltonian vac b := by
  intro ψ hψ
  have h := hcoer (ψ : E) hψ
  rwa [hamiltonian_apply, inner_toCLM]

/-- **The form-to-datum compiler.**  A bounded Hermitian energy form which kills
a unit vector `Ω` and is `b`-coercive on `Ω^⊥` produces a genuine
`VacuumGapDatum`: the Hamiltonian, its self-adjointness, the zero-energy vacuum
and the gap are all derived from the form. -/
noncomputable def gapDatum {vac : E} {b : ℝ} (hunit : ‖vac‖ = 1) (hb : 0 < b)
    (hvac : ∀ z, q.form z vac = 0)
    (hcoer : ∀ ψ : E, ⟪vac, ψ⟫_ℂ = 0 → b * ‖ψ‖ ^ 2 ≤ (q.form ψ ψ).re) :
    VacuumGapDatum E where
  op := q.hamiltonian
  vac := vac
  gap := b
  vac_mem := Submodule.mem_top
  vac_unit := hunit
  vac_ground := q.hamiltonian_apply_eq_zero hvac
  selfAdjoint := q.isSelfAdjoint_hamiltonian
  gap_pos := hb
  form_gap := q.hasVacuumFormGap_hamiltonian hcoer

@[simp] theorem gapDatum_gap {vac : E} {b : ℝ} (hunit : ‖vac‖ = 1) (hb : 0 < b)
    (hvac : ∀ z, q.form z vac = 0)
    (hcoer : ∀ ψ : E, ⟪vac, ψ⟫_ℂ = 0 → b * ‖ψ‖ ^ 2 ≤ (q.form ψ ψ).re) :
    (q.gapDatum hunit hb hvac hcoer).gap = b := rfl

@[simp] theorem gapDatum_op {vac : E} {b : ℝ} (hunit : ‖vac‖ = 1) (hb : 0 < b)
    (hvac : ∀ z, q.form z vac = 0)
    (hcoer : ∀ ψ : E, ⟪vac, ψ⟫_ℂ = 0 → b * ‖ψ‖ ^ 2 ≤ (q.form ψ ψ).re) :
    (q.gapDatum hunit hb hvac hcoer).op = q.hamiltonian := rfl

end BoundedSesqForm

/-! ## Non-vacuity: a form with a prescribed gap -/

section Witness

variable [CompleteSpace E]

/-- The energy form `b·(⟪x,y⟫ − ⟪x,Ω⟫⟪Ω,y⟫)`: the rank-one defect of `b` times
the identity.  It is bounded and Hermitian, annihilates `Ω`, and is exactly
`b`-coercive on `Ω^⊥`. -/
noncomputable def rankOneDefectForm (vac : E) (b : ℝ) : BoundedSesqForm E where
  form := fun x y => (b : ℂ) * (⟪x, y⟫_ℂ - ⟪x, vac⟫_ℂ * ⟪vac, y⟫_ℂ)
  bound := |b| * (1 + ‖vac‖ ^ 2)
  bound_nonneg := by positivity
  add_left := by intro x y z; rw [inner_add_left, inner_add_left]; ring
  smul_left := by intro c x y; rw [inner_smul_left, inner_smul_left]; ring
  norm_le := by
    intro x y
    have h1 : ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    have h2 : ‖⟪x, vac⟫_ℂ‖ ≤ ‖x‖ * ‖vac‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    have h3 : ‖⟪vac, y⟫_ℂ‖ ≤ ‖vac‖ * ‖y‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    have hsub : ‖⟪x, y⟫_ℂ - ⟪x, vac⟫_ℂ * ⟪vac, y⟫_ℂ‖
        ≤ ‖x‖ * ‖y‖ + (‖x‖ * ‖vac‖) * (‖vac‖ * ‖y‖) := by
      refine (norm_sub_le _ _).trans ?_
      have : ‖⟪x, vac⟫_ℂ * ⟪vac, y⟫_ℂ‖ ≤ (‖x‖ * ‖vac‖) * (‖vac‖ * ‖y‖) := by
        rw [norm_mul]
        exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      linarith
    calc ‖(b : ℂ) * (⟪x, y⟫_ℂ - ⟪x, vac⟫_ℂ * ⟪vac, y⟫_ℂ)‖
        = |b| * ‖⟪x, y⟫_ℂ - ⟪x, vac⟫_ℂ * ⟪vac, y⟫_ℂ‖ := by simp
      _ ≤ |b| * (‖x‖ * ‖y‖ + (‖x‖ * ‖vac‖) * (‖vac‖ * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hsub (abs_nonneg b)
      _ = |b| * (1 + ‖vac‖ ^ 2) * ‖x‖ * ‖y‖ := by ring
  sesq_symm := by
    intro x y
    have e1 : conj ⟪y, x⟫_ℂ = ⟪x, y⟫_ℂ := inner_conj_symm _ _
    have e2 : conj ⟪y, vac⟫_ℂ = ⟪vac, y⟫_ℂ := inner_conj_symm _ _
    have e3 : conj ⟪vac, x⟫_ℂ = ⟪x, vac⟫_ℂ := inner_conj_symm _ _
    simp only [map_mul, map_sub, Complex.conj_ofReal, e1, e2, e3]
    ring

omit [CompleteSpace E] in
theorem rankOneDefectForm_vac (vac : E) (hunit : ‖vac‖ = 1) (b : ℝ) (z : E) :
    (rankOneDefectForm vac b).form z vac = 0 := by
  have hvv : ⟪vac, vac⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hunit]; norm_num
  have h : (rankOneDefectForm vac b).form z vac
      = (b : ℂ) * (⟪z, vac⟫_ℂ - ⟪z, vac⟫_ℂ * ⟪vac, vac⟫_ℂ) := rfl
  rw [h, hvv]
  ring

omit [CompleteSpace E] in
theorem rankOneDefectForm_coercive (vac : E) (b : ℝ) (ψ : E) (hψ : ⟪vac, ψ⟫_ℂ = 0) :
    b * ‖ψ‖ ^ 2 ≤ ((rankOneDefectForm vac b).form ψ ψ).re := by
  have hform : (rankOneDefectForm vac b).form ψ ψ = (b : ℂ) * ⟪ψ, ψ⟫_ℂ := by
    simp [rankOneDefectForm, hψ]
  have hre : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  rw [hform, Complex.re_ofReal_mul, hre]

/-- The compiler is not vacuous: in any complex Hilbert space, a unit vector and
a positive constant give a bounded Hermitian energy form whose associated
self-adjoint Hamiltonian has that vector as a zero-energy vacuum and exactly
that gap. -/
noncomputable def formWitness (vac : E) (hunit : ‖vac‖ = 1) {b : ℝ} (hb : 0 < b) :
    VacuumGapDatum E :=
  (rankOneDefectForm vac b).gapDatum hunit hb (rankOneDefectForm_vac vac hunit b)
    (rankOneDefectForm_coercive vac b)

theorem formWitness_gap (vac : E) (hunit : ‖vac‖ = 1) {b : ℝ} (hb : 0 < b) :
    (formWitness vac hunit hb).gap = b ∧ (formWitness vac hunit hb).vac = vac :=
  ⟨rfl, rfl⟩

end Witness

end RequestProject.YangMills.Clay

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Clay

#print axioms BoundedSesqForm.inner_toCLM
#print axioms BoundedSesqForm.isSelfAdjoint_hamiltonian
#print axioms BoundedSesqForm.hamiltonian_apply_eq_zero
#print axioms BoundedSesqForm.hasVacuumFormGap_hamiltonian
#print axioms BoundedSesqForm.gapDatum
#print axioms formWitness_gap

end Audit
