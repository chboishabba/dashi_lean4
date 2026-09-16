/-
# The assembled mass-gap statement and the two routes into it

This file collects the Yang–Mills lane of this library into **one named
conclusion** and **one named hypothesis package**, and proves the implication
between them.

The conclusion, `MassGapConclusion H Ω Δ`, is the operator-theoretic content of
"the theory has a mass gap `Δ`" for a Hamiltonian with a zero-energy vacuum:
the form gap on `Ω^⊥`, no eigenvalue in `(0,Δ)` (equivalently: every excited
state has energy at least `Δ`), unique solvability of `Hψ − λψ = y` on the
vacuum sector for every real `λ < Δ`, and the resolvent bound `(Δ−λ)⁻¹`.

The hypothesis package is split into the three physical fronts identified in the
Yang–Mills notes:

* `CutoffFamily` — the finite-spacing family `(H_a, Ω_a)`, its vacuum-sector
  graph limit `(H_∞, Ω)`, and self-adjointness of the limit;
* the finite-spacing gap `∀ a, HasVacuumFormGap (H_a) (Ω_a) Δ`, which this file
  does **not** assume but *produces* from either of the two routes:
  - `finiteGap_of_energyForms` — the Row-A1/operator route: a bounded Hermitian
    energy form at each spacing, annihilating the vacuum and `Δ`-coercive on the
    vacuum complement (via `Clay.FormHamiltonian`, which also produces the
    Hamiltonian and its self-adjointness);
  - `finiteGap_of_clustering` — the source/clustering route: a spectral
    representation plus exponential clustering at rate `Δ` (via
    `BIDI.ClusteringGap`);
* `OSWeld` — the same-object identification of the reconstructed (OS) evolution
  with the physical one on a common core, which upgrades the conclusion from the
  continuum limit `H_∞` to the reconstructed Hamiltonian `H_OS`.

`clay_mass_gap_of_inputs` is the end-to-end implication.  `Clay/Witness.lean`
shows the whole package is simultaneously satisfiable, so nothing here is
vacuous.

**Honest scope.**  This is a conditional theorem: the fields of `CutoffFamily`,
`EnergyFormFamily`/`ClusteringFamily` and `OSWeld` are the physical inputs
(literal finite-spacing Yang–Mills energy form and its coercivity, actual
cutoff-to-continuum convergence, actual OS reconstruction).  They are displayed
as hypotheses; they are not proved here, and no file in this development claims
the Clay theorem.
-/
import Mathlib
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.ContinuumGapTransport
import RequestProject.YangMills.SameObjectGapTransfer
import RequestProject.YangMills.Clay.FormHamiltonian
import RequestProject.YangMills.BIDI.ClusteringGap
import RequestProject.YangMills.LocalGap

namespace RequestProject.YangMills.Clay

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open RequestProject.YangMills.SameObjectGapTransfer
open RequestProject.YangMills.UnboundedHamiltonianDomain
open RequestProject.YangMills.BIDI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

structure MassGapConclusion (H : E →ₗ.[ℂ] E) (vac : E) (Δ : ℝ) : Prop where
  gap_pos : 0 < Δ
  vac_unit : ‖vac‖ = 1
  form_gap : HasVacuumFormGap H vac Δ
  no_eigenvalue_below : ∀ (lam : ℝ) (ψ : H.domain), (ψ : E) ≠ 0 →
    H ψ = (lam : ℂ) • (ψ : E) → lam < Δ → lam = 0
  resolvent : ∀ (lam : ℝ), lam < Δ → ∀ y : E, ⟪vac, y⟫_ℂ = 0 →
    ∃! ψ : H.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧ H ψ - (lam : ℂ) • (ψ : E) = y
  resolvent_bound : ∀ (lam : ℝ), lam < Δ → ∀ ψ : H.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
    ‖(ψ : E)‖ ≤ (Δ - lam)⁻¹ * ‖H ψ - (lam : ℂ) • (ψ : E)‖

theorem massGapConclusion_of_datum (D : VacuumGapDatum E) :
    MassGapConclusion D.op D.vac D.gap where
  gap_pos := D.gap_pos
  vac_unit := D.vac_unit
  form_gap := D.form_gap
  no_eigenvalue_below := fun _ _ hne heig hlt => D.eigenvalue_eq_zero_of_lt_gap hne heig hlt
  resolvent := fun _ hlt _ hy => D.exists_unique_solution_vacuumSector hlt hy
  resolvent_bound := fun _ hlt _ horth => D.resolvent_bound_vacuumSector hlt horth rfl

structure CutoffFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  ham : ℕ → E →ₗ.[ℂ] E
  vacuum : ℕ → E
  limitHam : E →ₗ.[ℂ] E
  vac : E
  graphLimit : IsVacuumGraphLimit ham vacuum limitHam vac
  limit_selfAdjoint : IsSelfAdjoint limitHam
  vac_mem : vac ∈ limitHam.domain
  vac_unit : ‖vac‖ = 1
  vac_ground : limitHam ⟨vac, vac_mem⟩ = 0

structure OSWeld (Hinf Hos : E →ₗ.[ℂ] E) where
  core : Submodule ℂ E
  ymEvolution : ℝ → E → E
  osEvolution : ℝ → E → E
  evolutions_eq : ymEvolution = osEvolution
  core_limit : Hinf.HasCore core
  core_os : Hos.HasCore core
  gen_limit : IsPMapEvolutionGenerator ymEvolution core Hinf
  gen_os : IsPMapEvolutionGenerator osEvolution core Hos

def OSWeld.self (H : E →ₗ.[ℂ] E) (S : Submodule ℂ E) (hc : H.HasCore S)
    (U : ℝ → E → E) (hg : IsPMapEvolutionGenerator U S H) : OSWeld H H where
  core := S
  ymEvolution := U
  osEvolution := U
  evolutions_eq := rfl
  core_limit := hc
  core_os := hc
  gen_limit := hg
  gen_os := hg

structure EnergyFormFamily (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (gap : ℝ) where
  form : ℕ → BoundedSesqForm E
  vacuum : ℕ → E
  vac_unit : ∀ n, ‖vacuum n‖ = 1
  vac_null : ∀ n, ∀ z, (form n).form z (vacuum n) = 0
  coercive : ∀ n, ∀ ψ : E, ⟪vacuum n, ψ⟫_ℂ = 0 →
    gap * ‖ψ‖ ^ 2 ≤ ((form n).form ψ ψ).re

noncomputable def EnergyFormFamily.ham {gap : ℝ} (F : EnergyFormFamily E gap)
    (n : ℕ) : E →ₗ.[ℂ] E := (F.form n).hamiltonian

theorem finiteGap_of_energyForms {gap : ℝ} (F : EnergyFormFamily E gap) (n : ℕ) :
    HasVacuumFormGap (F.ham n) (F.vacuum n) gap :=
  (F.form n).hasVacuumFormGap_hamiltonian (F.coercive n)

theorem EnergyFormFamily.isSelfAdjoint_ham {gap : ℝ} (F : EnergyFormFamily E gap)
    (n : ℕ) : IsSelfAdjoint (F.ham n) := (F.form n).isSelfAdjoint_hamiltonian

theorem EnergyFormFamily.ham_vacuum {gap : ℝ} (F : EnergyFormFamily E gap) (n : ℕ) :
    (F.ham n) ⟨F.vacuum n, Submodule.mem_top⟩ = 0 :=
  (F.form n).hamiltonian_apply_eq_zero (F.vac_null n)

structure ClusteringFamily (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (gap : ℝ) where
  ham : ℕ → E →ₗ.[ℂ] E
  vacuum : ℕ → E
  data : ∀ n, ClusteringSpectralData (ham n) (vacuum n) gap

theorem finiteGap_of_clustering {gap : ℝ} (C : ClusteringFamily E gap) (n : ℕ) :
    HasVacuumFormGap (C.ham n) (C.vacuum n) gap :=
  hasVacuumFormGap_of_clustering (C.data n)

noncomputable def CutoffFamily.continuumDatum (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) : VacuumGapDatum E :=
  ContinuumGapTransport.continuumDatum hgap C.graphLimit C.limit_selfAdjoint
    C.vac_mem C.vac_unit C.vac_ground hΔ

@[simp] theorem CutoffFamily.continuumDatum_op (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) :
    (C.continuumDatum hΔ hgap).op = C.limitHam := rfl

@[simp] theorem CutoffFamily.continuumDatum_gap (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) :
    (C.continuumDatum hΔ hgap).gap = Δ := rfl

@[simp] theorem CutoffFamily.continuumDatum_vac (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) :
    (C.continuumDatum hΔ hgap).vac = C.vac := rfl

theorem continuum_massGap (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) :
    MassGapConclusion C.limitHam C.vac Δ :=
  massGapConclusion_of_datum (C.continuumDatum hΔ hgap)

theorem clay_mass_gap_of_inputs (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ :=
  massGapConclusion_of_datum
    (vacuumGapDatum_of_same_evolution W.evolutions_eq W.core_limit W.core_os
      W.gen_limit W.gen_os (C.continuumDatum hΔ hgap) rfl)

theorem clay_mass_gap_of_energyForms {Δ : ℝ} (hΔ : 0 < Δ) (F : EnergyFormFamily E Δ)
    (C : CutoffFamily E) (hfam : C.ham = F.ham) (hvac : C.vacuum = F.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ := by
  refine clay_mass_gap_of_inputs C hΔ (fun n => ?_) W
  rw [hfam, hvac]
  exact finiteGap_of_energyForms F n

theorem clay_mass_gap_of_clustering {Δ : ℝ} (hΔ : 0 < Δ) (K : ClusteringFamily E Δ)
    (C : CutoffFamily E) (hfam : C.ham = K.ham) (hvac : C.vacuum = K.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ := by
  refine clay_mass_gap_of_inputs C hΔ (fun n => ?_) W
  rw [hfam, hvac]
  exact finiteGap_of_clustering K n

section RowA1

open _root_.YangMills

theorem clay_mass_gap_rowA1 {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ splitCost (2 / 5)) (hh : h ≤ 1 / 2)
    (F : EnergyFormFamily E (bMinus (casimirAdjointSU N) r h))
    (C : CutoffFamily E) (hfam : C.ham = F.ham) (hvac : C.vacuum = F.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac (bMinus (casimirAdjointSU N) r h) :=
  clay_mass_gap_of_energyForms (bMinus_pos_SU hN hr hh) F C hfam hvac W

end RowA1

end RequestProject.YangMills.Clay

section Audit

open RequestProject.YangMills.Clay

#print axioms massGapConclusion_of_datum
#print axioms finiteGap_of_energyForms
#print axioms finiteGap_of_clustering
#print axioms continuum_massGap
#print axioms clay_mass_gap_of_inputs
#print axioms clay_mass_gap_of_energyForms
#print axioms clay_mass_gap_of_clustering
#print axioms clay_mass_gap_rowA1

end Audit
