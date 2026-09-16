/-
# Non-vacuity of the assembled mass-gap package

`Clay/MassGapAssembly.lean` proves an implication whose hypotheses are three
packages of physical data (`EnergyFormFamily`/`ClusteringFamily`, `CutoffFamily`,
`OSWeld`).  An implication with unsatisfiable hypotheses proves nothing, so this
file exhibits, in *every* complex Hilbert space with a unit vector and every
prescribed `Δ > 0`, a simultaneous inhabitant of all three packages, and checks
that the conclusion it delivers is the intended nontrivial one:

* the energy form is the rank-one defect form `Δ(⟪x,y⟫ − ⟪x,Ω⟫⟪Ω,y⟫)`, which
  produces its own Hamiltonian, self-adjointness and zero-energy vacuum;
* the cutoff family is the constant family, which is its own vacuum-sector graph
  limit;
* the weld is along the genuine one-parameter group `t ↦ exp(tH)` that the
  bounded Hamiltonian generates, with `⊤` a core for it — none of the
  domain-theoretic hypotheses is assumed.

The resulting conclusion has gap exactly `Δ`, so the constant in the assembled
theorem is not forced and the statement is not degenerate.

This file demonstrates satisfiability only.  The physical Yang–Mills inhabitants
of the same packages are not constructed here or anywhere in this development.
-/
import Mathlib
import RequestProject.YangMills.Clay.BoundedCoreEvolution

namespace RequestProject.YangMills.Clay

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

noncomputable def witnessForms (vac : E) (hunit : ‖vac‖ = 1) (Δ : ℝ) :
    EnergyFormFamily E Δ where
  form := fun _ => rankOneDefectForm vac Δ
  vacuum := fun _ => vac
  vac_unit := fun _ => hunit
  vac_null := fun _ => rankOneDefectForm_vac vac hunit Δ
  coercive := fun _ => rankOneDefectForm_coercive vac Δ

noncomputable def witnessCutoff (vac : E) (hunit : ‖vac‖ = 1) (Δ : ℝ) :
    CutoffFamily E where
  ham := (witnessForms vac hunit Δ).ham
  vacuum := fun _ => vac
  limitHam := (rankOneDefectForm vac Δ).hamiltonian
  vac := vac
  graphLimit := isVacuumGraphLimit_const _ _
  limit_selfAdjoint := (rankOneDefectForm vac Δ).isSelfAdjoint_hamiltonian
  vac_mem := Submodule.mem_top
  vac_unit := hunit
  vac_ground := (rankOneDefectForm vac Δ).hamiltonian_apply_eq_zero
    (rankOneDefectForm_vac vac hunit Δ)

noncomputable def witnessWeld (vac : E) (Δ : ℝ) :
    OSWeld (rankOneDefectForm vac Δ).hamiltonian (rankOneDefectForm vac Δ).hamiltonian :=
  OSWeld.selfBounded (rankOneDefectForm vac Δ).toCLM

theorem massGap_package_inhabited (vac : E) (hunit : ‖vac‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) :
    MassGapConclusion (rankOneDefectForm vac Δ).hamiltonian vac Δ :=
  clay_mass_gap_of_energyForms hΔ (witnessForms vac hunit Δ)
    (witnessCutoff vac hunit Δ) rfl rfl (witnessWeld vac Δ)

theorem massGap_package_gap_arbitrary (vac : E) (hunit : ‖vac‖ = 1) :
    ∀ Δ : ℝ, 0 < Δ →
      MassGapConclusion (rankOneDefectForm vac Δ).hamiltonian vac Δ :=
  fun _ hΔ => massGap_package_inhabited vac hunit hΔ

theorem witness_resolvent_at_zero (vac : E) (hunit : ‖vac‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ)
    {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : (rankOneDefectForm vac Δ).hamiltonian.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      (rankOneDefectForm vac Δ).hamiltonian ψ - ((0 : ℝ) : ℂ) • (ψ : E) = y :=
  (massGap_package_inhabited vac hunit hΔ).resolvent 0 hΔ y hy

end RequestProject.YangMills.Clay

section Audit

open RequestProject.YangMills.Clay

#print axioms massGap_package_inhabited
#print axioms massGap_package_gap_arbitrary
#print axioms witness_resolvent_at_zero

end Audit
