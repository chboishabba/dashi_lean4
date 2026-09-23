/-
# The same-object weld: transferring the mass gap between Hamiltonians

A mass gap proved for one description of the dynamics is worth nothing for
another description unless the two are the *same object*.  This module supplies
the only legitimate bridge: an equality of unbounded operators, produced from a
common core, transports the whole `VacuumGapDatum` — vacuum, gap, resolvent
statement and all.

The composite theorem is `vacuumGapDatum_of_same_evolution`:

> if the Yang–Mills Hamiltonian `H_YM` and the Osterwalder–Schrader
> reconstructed Hamiltonian `H_OS` differentiate the *same* time evolution on a
> submodule that is a core for both, and `H_YM` carries a vacuum gap datum, then
> `H_OS` carries the same datum — hence has no spectrum in `[0, Δ)` on the
> vacuum complement.

The point of stating it this way is the strictness of the hypothesis: the
transfer is driven by `pmap_generator_unique_of_hasCore`, which delivers a
genuine equality `H_YM = H_OS` of operators *including their domains*.  A shared
name, a shared numerical constant, a record field or a provenance receipt cannot
substitute for it.

Nothing here identifies the Yang–Mills and OS evolutions: `U^YM = U^OS` on a
common core is an input, displayed as a hypothesis.
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.ContinuumGapTransport

namespace RequestProject.YangMills.SameObjectGapTransfer

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Transport along an operator equality -/

/-- The vacuum form gap is a property of the operator, so it transports along an
equality of operators. -/
theorem hasVacuumFormGap_of_eq {H₁ H₂ : E →ₗ.[ℂ] E} (hEq : H₁ = H₂) {vac : E} {Δ : ℝ}
    (h : HasVacuumFormGap H₁ vac Δ) : HasVacuumFormGap H₂ vac Δ := by
  subst hEq; exact h

section Complete

variable [CompleteSpace E]

/-- **Transport of the whole carrier along a same-object equality.**  A
`VacuumGapDatum` for `H₁` gives one for any operator equal to `H₁`. -/
def transferDatum (D : VacuumGapDatum E) {H₂ : E →ₗ.[ℂ] E}
    (hEq : D.op = H₂) : VacuumGapDatum E where
  op := H₂
  vac := D.vac
  gap := D.gap
  vac_mem := hEq ▸ D.vac_mem
  vac_unit := D.vac_unit
  vac_ground := by subst hEq; exact D.vac_ground
  selfAdjoint := hEq ▸ D.selfAdjoint
  gap_pos := D.gap_pos
  form_gap := hasVacuumFormGap_of_eq hEq D.form_gap

@[simp] theorem transferDatum_gap (D : VacuumGapDatum E) {H₂ : E →ₗ.[ℂ] E}
    (hEq : D.op = H₂) : (transferDatum D hEq).gap = D.gap := rfl

@[simp] theorem transferDatum_op (D : VacuumGapDatum E) {H₂ : E →ₗ.[ℂ] E}
    (hEq : D.op = H₂) : (transferDatum D hEq).op = H₂ := rfl

@[simp] theorem transferDatum_vac (D : VacuumGapDatum E) {H₂ : E →ₗ.[ℂ] E}
    (hEq : D.op = H₂) : (transferDatum D hEq).vac = D.vac := rfl

/-! ## The physical weld: same evolution on a common core -/

/-- **Same evolution ⇒ same gap.**  Two Hamiltonians that differentiate the same
evolution on a common core are the same operator, so a vacuum gap datum for the
first is one for the second. -/
def vacuumGapDatum_of_same_evolution {U V : ℝ → E → E} {S : Submodule ℂ E}
    {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁) (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁) : VacuumGapDatum E :=
  transferDatum D (hD.trans (pmap_generator_unique_of_hasCore hUV hc₁ hc₂ hg₁ hg₂))

@[simp] theorem vacuumGapDatum_of_same_evolution_op {U V : ℝ → E → E}
    {S : Submodule ℂ E} {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁) (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁) :
    (vacuumGapDatum_of_same_evolution hUV hc₁ hc₂ hg₁ hg₂ D hD).op = H₂ := rfl

@[simp] theorem vacuumGapDatum_of_same_evolution_gap {U V : ℝ → E → E}
    {S : Submodule ℂ E} {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁) (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁) :
    (vacuumGapDatum_of_same_evolution hUV hc₁ hc₂ hg₁ hg₂ D hD).gap = D.gap := rfl

/-- **The welded spectral statement.**  Under the same-object hypothesis, the
second Hamiltonian has no spectrum in `[0, Δ)` on the vacuum complement, with
the *same* gap constant `Δ` as the first. -/
theorem welded_no_spectrum_below_gap {U V : ℝ → E → E} {S : Submodule ℂ E}
    {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁) (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁)
    {lam : ℝ} (hlt : lam < D.gap) {y : E} (hy : ⟪D.vac, y⟫_ℂ = 0) :
    ∃! ψ : H₂.domain, ⟪D.vac, (ψ : E)⟫_ℂ = 0 ∧
      H₂ ψ - (lam : ℂ) • (ψ : E) = y :=
  (vacuumGapDatum_of_same_evolution hUV hc₁ hc₂ hg₁ hg₂ D hD).exists_unique_solution_vacuumSector
    hlt hy

/-- **The full chain in one statement.**  A cutoff family with a uniform gap `Δ`
above its vacua, converging in the vacuum-sector graph sense to a self-adjoint
limit with a normalised zero-energy vacuum, together with a second Hamiltonian
generating the *same* evolution on a common core, yields: the second Hamiltonian
has no spectrum in `[0, Δ)` on the vacuum complement.

This is `lattice/cutoff uniform gap → continuum transport → same-object weld →
spectral gap` with every step a theorem and every physical input a hypothesis. -/
theorem chain_no_spectrum_below_gap
    {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E} {Hinf Hos : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
    (hlim : ContinuumGapTransport.IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hΔ : 0 < Δ)
    {U V : ℝ → E → E} {S : Submodule ℂ E} (hUV : U = V)
    (hc₁ : Hinf.HasCore S) (hc₂ : Hos.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S Hinf) (hg₂ : IsPMapEvolutionGenerator V S Hos)
    {lam : ℝ} (hlt : lam < Δ) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : Hos.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      Hos ψ - (lam : ℂ) • (ψ : E) = y := by
  have hD : (ContinuumGapTransport.continuumDatum hgap hlim hsa hmem hunit hground hΔ).op
      = Hinf := rfl
  exact welded_no_spectrum_below_gap hUV hc₁ hc₂ hg₁ hg₂ _ hD hlt hy

/-! ## Non-vacuity of the weld -/

/-- The weld is satisfiable: an operator is trivially welded to itself, and the
transfer then returns the same datum. -/
theorem transferDatum_rfl (D : VacuumGapDatum E) :
    transferDatum D (rfl : D.op = D.op) = D := rfl

/-- A `VacuumGapDatum` is its own core-weld along the identity evolution, so
the hypotheses of `vacuumGapDatum_of_same_evolution` are simultaneously
satisfiable. -/
theorem same_evolution_self (D : VacuumGapDatum E) (S : Submodule ℂ E)
    (hc : D.op.HasCore S) (U : ℝ → E → E) (hg : IsPMapEvolutionGenerator U S D.op) :
    vacuumGapDatum_of_same_evolution (rfl : U = U) hc hc hg hg D rfl = D := rfl

end Complete

/-! ## Axiom audit -/

section Audit

#print axioms hasVacuumFormGap_of_eq
#print axioms transferDatum_gap
#print axioms vacuumGapDatum_of_same_evolution_op
#print axioms welded_no_spectrum_below_gap
#print axioms chain_no_spectrum_below_gap
#print axioms transferDatum_rfl
#print axioms same_evolution_self

end Audit

end RequestProject.YangMills.SameObjectGapTransfer
