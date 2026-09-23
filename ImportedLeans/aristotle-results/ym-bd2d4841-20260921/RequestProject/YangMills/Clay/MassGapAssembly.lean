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

/-! ## The conclusion -/

/-- **The mass-gap conclusion** for a Hamiltonian `H` with unit vacuum `Ω`:
the quadratic-form gap on `Ω^⊥`, no eigenvalue in `(0,Δ)`, unique solvability of
`Hψ − λψ = y` in the vacuum sector for every real `λ < Δ`, and the resolvent
bound.  For a Hamiltonian with `HΩ = 0` this is the precise operator form of
"`spec(H|_{Ω^⊥}) ∩ [0,Δ) = ∅`". -/
structure MassGapConclusion (H : E →ₗ.[ℂ] E) (vac : E) (Δ : ℝ) : Prop where
  /-- The gap is positive. -/
  gap_pos : 0 < Δ
  /-- The vacuum is a unit vector. -/
  vac_unit : ‖vac‖ = 1
  /-- The quadratic-form gap on the vacuum complement. -/
  form_gap : HasVacuumFormGap H vac Δ
  /-- No eigenvalue strictly between `0` and `Δ`. -/
  no_eigenvalue_below : ∀ (lam : ℝ) (ψ : H.domain), (ψ : E) ≠ 0 →
    H ψ = (lam : ℂ) • (ψ : E) → lam < Δ → lam = 0
  /-- Unique solvability on the vacuum sector below the gap. -/
  resolvent : ∀ (lam : ℝ), lam < Δ → ∀ y : E, ⟪vac, y⟫_ℂ = 0 →
    ∃! ψ : H.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧ H ψ - (lam : ℂ) • (ψ : E) = y
  /-- The quantitative resolvent bound. -/
  resolvent_bound : ∀ (lam : ℝ), lam < Δ → ∀ ψ : H.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
    ‖(ψ : E)‖ ≤ (Δ - lam)⁻¹ * ‖H ψ - (lam : ℂ) • (ψ : E)‖

/-- Every `VacuumGapDatum` satisfies the mass-gap conclusion: this is the
packaging of the vacuum-sector spectral theory. -/
theorem massGapConclusion_of_datum (D : VacuumGapDatum E) :
    MassGapConclusion D.op D.vac D.gap where
  gap_pos := D.gap_pos
  vac_unit := D.vac_unit
  form_gap := D.form_gap
  no_eigenvalue_below := fun _ _ hne heig hlt => D.eigenvalue_eq_zero_of_lt_gap hne heig hlt
  resolvent := fun _ hlt _ hy => D.exists_unique_solution_vacuumSector hlt hy
  resolvent_bound := fun _ hlt _ horth => D.resolvent_bound_vacuumSector hlt horth rfl

/-! ## The physical input packages -/

/-- **The cutoff family and its continuum limit.**  `ham a` is the Hamiltonian at
lattice spacing indexed by `a`, `vacuum a` its vacuum; `limitHam` is the
continuum Hamiltonian with vacuum `vac`, reached in the vacuum-sector graph
sense. -/
structure CutoffFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  /-- The finite-spacing Hamiltonians. -/
  ham : ℕ → E →ₗ.[ℂ] E
  /-- The finite-spacing vacua. -/
  vacuum : ℕ → E
  /-- The continuum Hamiltonian. -/
  limitHam : E →ₗ.[ℂ] E
  /-- The continuum vacuum. -/
  vac : E
  /-- The cutoff family converges to the limit in the vacuum-sector graph sense. -/
  graphLimit : IsVacuumGraphLimit ham vacuum limitHam vac
  /-- The continuum Hamiltonian is self-adjoint. -/
  limit_selfAdjoint : IsSelfAdjoint limitHam
  /-- The continuum vacuum lies in the domain. -/
  vac_mem : vac ∈ limitHam.domain
  /-- The continuum vacuum is normalised. -/
  vac_unit : ‖vac‖ = 1
  /-- The continuum vacuum has zero energy. -/
  vac_ground : limitHam ⟨vac, vac_mem⟩ = 0

/-- **The OS/Yang–Mills same-object weld.**  A submodule that is a core for both
the continuum Hamiltonian and the reconstructed one, together with the two
evolutions they differentiate there and the physical statement that those
evolutions coincide. -/
structure OSWeld (Hinf Hos : E →ₗ.[ℂ] E) where
  /-- The common core. -/
  core : Submodule ℂ E
  /-- The Yang–Mills evolution. -/
  ymEvolution : ℝ → E → E
  /-- The reconstructed (OS) evolution. -/
  osEvolution : ℝ → E → E
  /-- **The physical same-object statement.** -/
  evolutions_eq : ymEvolution = osEvolution
  /-- The core is a core for the continuum Hamiltonian. -/
  core_limit : Hinf.HasCore core
  /-- The core is a core for the reconstructed Hamiltonian. -/
  core_os : Hos.HasCore core
  /-- The continuum Hamiltonian generates the Yang–Mills evolution on the core. -/
  gen_limit : IsPMapEvolutionGenerator ymEvolution core Hinf
  /-- The reconstructed Hamiltonian generates the OS evolution on the core. -/
  gen_os : IsPMapEvolutionGenerator osEvolution core Hos

/-- The trivial weld of an operator with itself, along any core and evolution it
generates: the weld package is satisfiable. -/
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

/-! ## Route 1: the energy form (Row A1 / operator route) -/

/-- **A family of finite-spacing energy forms.**  At each spacing a bounded
Hermitian form on the physical Hilbert space which annihilates the vacuum and is
`gap`-coercive on the vacuum complement.  By `Clay.FormHamiltonian` this
*produces* the Hamiltonian, its self-adjointness, the zero-energy vacuum and the
form gap; only the coercivity estimate is a physical input. -/
structure EnergyFormFamily (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (gap : ℝ) where
  /-- The energy form at each spacing. -/
  form : ℕ → BoundedSesqForm E
  /-- The vacuum at each spacing. -/
  vacuum : ℕ → E
  /-- Each vacuum is normalised. -/
  vac_unit : ∀ n, ‖vacuum n‖ = 1
  /-- Each form annihilates its vacuum. -/
  vac_null : ∀ n, ∀ z, (form n).form z (vacuum n) = 0
  /-- **The Row-A1 coercivity input.** -/
  coercive : ∀ n, ∀ ψ : E, ⟪vacuum n, ψ⟫_ℂ = 0 →
    gap * ‖ψ‖ ^ 2 ≤ ((form n).form ψ ψ).re

/-- The Hamiltonian produced at spacing `n` by the energy form. -/
noncomputable def EnergyFormFamily.ham {gap : ℝ} (F : EnergyFormFamily E gap)
    (n : ℕ) : E →ₗ.[ℂ] E := (F.form n).hamiltonian

/-- **Route 1: energy forms give the finite-spacing gap.** -/
theorem finiteGap_of_energyForms {gap : ℝ} (F : EnergyFormFamily E gap) (n : ℕ) :
    HasVacuumFormGap (F.ham n) (F.vacuum n) gap :=
  (F.form n).hasVacuumFormGap_hamiltonian (F.coercive n)

/-- The produced finite-spacing Hamiltonians are self-adjoint. -/
theorem EnergyFormFamily.isSelfAdjoint_ham {gap : ℝ} (F : EnergyFormFamily E gap)
    (n : ℕ) : IsSelfAdjoint (F.ham n) := (F.form n).isSelfAdjoint_hamiltonian

/-- The produced finite-spacing Hamiltonians annihilate their vacua. -/
theorem EnergyFormFamily.ham_vacuum {gap : ℝ} (F : EnergyFormFamily E gap) (n : ℕ) :
    (F.ham n) ⟨F.vacuum n, Submodule.mem_top⟩ = 0 :=
  (F.form n).hamiltonian_apply_eq_zero (F.vac_null n)

/-! ## Route 2: exponential clustering (source route) -/

/-- **A family of clustering data.**  At each spacing, the spectral
representation of the finite-spacing Hamiltonian together with the exponential
clustering estimate at rate `gap` delivered by the source side. -/
structure ClusteringFamily (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (gap : ℝ) where
  /-- The finite-spacing Hamiltonians. -/
  ham : ℕ → E →ₗ.[ℂ] E
  /-- The finite-spacing vacua. -/
  vacuum : ℕ → E
  /-- Spectral representation plus clustering at each spacing. -/
  data : ∀ n, ClusteringSpectralData (ham n) (vacuum n) gap

/-- **Route 2: clustering gives the finite-spacing gap.** -/
theorem finiteGap_of_clustering {gap : ℝ} (C : ClusteringFamily E gap) (n : ℕ) :
    HasVacuumFormGap (C.ham n) (C.vacuum n) gap :=
  hasVacuumFormGap_of_clustering (C.data n)

/-! ## The assembled implication -/

/-- The continuum carrier produced from a cutoff family with a uniform gap. -/
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

/-- **The continuum mass gap.**  A uniform finite-spacing gap plus the
vacuum-sector graph limit gives the mass-gap conclusion for the continuum
Hamiltonian. -/
theorem continuum_massGap (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ) :
    MassGapConclusion C.limitHam C.vac Δ :=
  massGapConclusion_of_datum (C.continuumDatum hΔ hgap)

/-- **The end-to-end implication.**  A uniform finite-spacing gap, the
vacuum-sector graph limit, and the OS same-object weld give the mass-gap
conclusion for the *reconstructed* Hamiltonian, with the same constant.

Each hypothesis is one of the physical fronts: the gap comes from either route
(`finiteGap_of_energyForms` or `finiteGap_of_clustering`), the limit from the
cutoff family, the weld from the OS reconstruction. -/
theorem clay_mass_gap_of_inputs (C : CutoffFamily E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ n, HasVacuumFormGap (C.ham n) (C.vacuum n) Δ)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ :=
  massGapConclusion_of_datum
    (vacuumGapDatum_of_same_evolution W.evolutions_eq W.core_limit W.core_os
      W.gen_limit W.gen_os (C.continuumDatum hΔ hgap) rfl)

/-- **The whole chain from the energy-form route.**  The Row-A1 shape: a family
of bounded Yang–Mills energy forms, `Δ`-coercive on the vacuum complement, whose
Hamiltonians converge in the vacuum-sector graph sense, welded to the
reconstructed Hamiltonian, gives the mass gap `Δ` for the reconstructed
Hamiltonian. -/
theorem clay_mass_gap_of_energyForms {Δ : ℝ} (hΔ : 0 < Δ) (F : EnergyFormFamily E Δ)
    (C : CutoffFamily E) (hfam : C.ham = F.ham) (hvac : C.vacuum = F.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ := by
  refine clay_mass_gap_of_inputs C hΔ (fun n => ?_) W
  rw [hfam, hvac]
  exact finiteGap_of_energyForms F n

/-- **The whole chain from the clustering route.** -/
theorem clay_mass_gap_of_clustering {Δ : ℝ} (hΔ : 0 < Δ) (K : ClusteringFamily E Δ)
    (C : CutoffFamily E) (hfam : C.ham = K.ham) (hvac : C.vacuum = K.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ := by
  refine clay_mass_gap_of_inputs C hΔ (fun n => ?_) W
  rw [hfam, hvac]
  exact finiteGap_of_clustering K n

/-! ## The Row A1 constant as the gap -/

section RowA1

open _root_.YangMills

/-- **The Row-A1 instantiation.**  With the project's Row-A1 gap functional
`b₋ = (11/24)C_A − r − h` for `SU(N)`, `N ≥ 2`, under the shell-budget
constraints `r ≤ splitCost (2/5)` and `h ≤ 1/2`, a family of energy forms that is
`b₋`-coercive on the vacuum complement delivers the mass gap `b₋` for the
reconstructed Hamiltonian. -/
theorem clay_mass_gap_rowA1 {N : ℕ} (hN : 2 ≤ N) {r h : ℝ}
    (hr : r ≤ splitCost (2 / 5)) (hh : h ≤ 1 / 2)
    (F : EnergyFormFamily E (bMinus (casimirAdjointSU N) r h))
    (C : CutoffFamily E) (hfam : C.ham = F.ham) (hvac : C.vacuum = F.vacuum)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac (bMinus (casimirAdjointSU N) r h) :=
  clay_mass_gap_of_energyForms (bMinus_pos_SU hN hr hh) F C hfam hvac W

end RowA1

end RequestProject.YangMills.Clay

/-! ## Axiom audit -/

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
