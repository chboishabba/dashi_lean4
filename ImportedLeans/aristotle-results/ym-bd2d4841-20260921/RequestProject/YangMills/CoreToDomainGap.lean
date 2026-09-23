/-
# From a core to the domain: the vacuum gap survives closure

A physical Hamiltonian is written down on a *core* — a dense invariant subspace
of nice states — and the mass gap is estimated there.  The spectral statement,
however, lives on the closed operator.  This module supplies that step.

Main results:

* `hasVacuumFormGap_closure` — if a symmetric closable `H` has a normalised
  vacuum `Ω ∈ D(H)` with `HΩ = 0` and form gap `Δ` on `D(H) ∩ Ω^⊥`, then the
  **closure** `H̄` has form gap `Δ` on `D(H̄) ∩ Ω^⊥`.  The proof projects the
  graph-approximating sequence onto the vacuum complement — which is legitimate
  exactly because `HΩ = 0` — and then applies the graph-limit transport.
* `closureDatum` — given in addition that `H̄` is self-adjoint (i.e. `H` is
  essentially self-adjoint), the closure is a `VacuumGapDatum` with the same
  gap, so the full resolvent statement applies to it.
* `core_to_domain_no_spectrum_below_gap` — the resulting spectral statement:
  *an essentially self-adjoint Hamiltonian with a vacuum gap estimated on its
  core has no spectrum in `[0, Δ)` on the vacuum complement of its closure.*

This is the `core → domain → self-adjointness` leg of the chain.  Essential
self-adjointness is displayed as a hypothesis; it is the analytic input this
lane is waiting for, and nothing here pretends to supply it.  What is removed is
the step from "gap on the core" to "gap on the domain", which is now a theorem.
-/
import Mathlib
import RequestProject.YangMills.UnboundedHamiltonianDomain
import RequestProject.YangMills.VacuumSectorSpectralGap
import RequestProject.YangMills.ContinuumGapTransport

namespace RequestProject.YangMills.CoreToDomainGap

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The vacuum gap survives closure.**  A form gap above a normalised
zero-energy vacuum, valid on the domain of `H`, is valid on the domain of the
closure of `H`.

The vacuum-orthogonality of the approximants is not assumed: it is *produced*,
by subtracting the vacuum component, which costs nothing because `HΩ = 0`. -/
theorem hasVacuumFormGap_closure {H : E →ₗ.[ℂ] E} (hcl : H.IsClosable)
    {vac : E} {Δ : ℝ} (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hvac⟩ = 0) (hgap : HasVacuumFormGap H vac Δ) :
    HasVacuumFormGap H.closure vac Δ := by
  intro ψ hψ
  obtain ⟨a, ha1, ha2⟩ := exists_seq_of_mem_closure_domain hcl ψ
  have hvv : ⟪vac, vac⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hunit]; norm_num
  -- project the approximants onto the vacuum complement
  set c : ℕ → ℂ := fun n => ⟪vac, ((a n : E))⟫_ℂ with hc
  set b : ℕ → E := fun n => ((a n : E)) - c n • vac with hb
  have hbmem : ∀ n, b n ∈ H.domain := fun n =>
    H.domain.sub_mem (a n).2 (H.domain.smul_mem _ hvac)
  have hborth : ∀ n, ⟪vac, b n⟫_ℂ = 0 := by
    intro n
    rw [hb]
    simp only [inner_sub_right, inner_smul_right, hvv, mul_one, hc, sub_self]
  -- the projection does not change the image, because `HΩ = 0`
  have hbval : ∀ n, H ⟨b n, hbmem n⟩ = H (a n) := by
    intro n
    have hsub : (⟨b n, hbmem n⟩ : H.domain)
        = a n - c n • (⟨vac, hvac⟩ : H.domain) := by
      ext; simp [hb]
    rw [hsub, LinearPMap.map_sub, LinearPMap.map_smul, hground, smul_zero, sub_zero]
  -- the projected sequence still converges to `ψ`
  have hcconv : Tendsto c atTop (𝓝 (0 : ℂ)) := by
    have hlim : Tendsto c atTop (𝓝 (⟪vac, (ψ : E)⟫_ℂ)) :=
      (continuous_inner (𝕜 := ℂ)).tendsto _ |>.comp
        (Tendsto.prodMk_nhds tendsto_const_nhds ha1)
    rwa [hψ] at hlim
  have hbconv : Tendsto b atTop (𝓝 (ψ : E)) := by
    have h2 : Tendsto (fun n => c n • vac) atTop (𝓝 ((0 : ℂ) • vac)) :=
      hcconv.smul tendsto_const_nhds
    simpa [hb] using ha1.sub h2
  have hbop : Tendsto (fun n => H ⟨b n, hbmem n⟩) atTop (𝓝 (H.closure ψ)) := by
    simpa [hbval] using ha2
  exact formGap_le_of_graphLimit (H := fun _ : ℕ => H) (vacn := fun _ => vac)
    (fun _ => hgap) hbmem hborth hbconv hbop

section Complete

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- The closure of an operator still annihilates the vacuum. -/
theorem closure_vac {H : E →ₗ.[ℂ] E} {vac : E}
    (hvac : vac ∈ H.domain) (hground : H ⟨vac, hvac⟩ = 0) :
    ∃ h : vac ∈ H.closure.domain, H.closure ⟨vac, h⟩ = 0 := by
  have hle : H ≤ H.closure := H.le_closure
  refine ⟨hle.1 hvac, ?_⟩
  rw [← hle.2 (x := ⟨vac, hvac⟩) (y := ⟨vac, hle.1 hvac⟩) rfl, hground]

/-- **From an essentially self-adjoint Hamiltonian on a core to the carrier.**
A densely defined symmetric `H` with a normalised zero-energy vacuum, a positive
form gap `Δ` on its vacuum complement, and a self-adjoint closure, gives a
`VacuumGapDatum` on the closure with gap `Δ`. -/
noncomputable def closureDatum {H : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hdense : Dense (H.domain : Set E)) (hsym : IsSymmetric H)
    (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hvac⟩ = 0)
    (hgap : HasVacuumFormGap H vac Δ) (hΔ : 0 < Δ)
    (hsa : IsSelfAdjoint H.closure) : VacuumGapDatum E where
  op := H.closure
  vac := vac
  gap := Δ
  vac_mem := (closure_vac hvac hground).choose
  vac_unit := hunit
  vac_ground := (closure_vac hvac hground).choose_spec
  selfAdjoint := hsa
  gap_pos := hΔ
  form_gap := hasVacuumFormGap_closure (hsym.isClosable hdense) hvac hunit hground hgap

@[simp] theorem closureDatum_op {H : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hdense : Dense (H.domain : Set E)) (hsym : IsSymmetric H)
    (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hvac⟩ = 0)
    (hgap : HasVacuumFormGap H vac Δ) (hΔ : 0 < Δ) (hsa : IsSelfAdjoint H.closure) :
    (closureDatum hdense hsym hvac hunit hground hgap hΔ hsa).op = H.closure := rfl

@[simp] theorem closureDatum_gap {H : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hdense : Dense (H.domain : Set E)) (hsym : IsSymmetric H)
    (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hvac⟩ = 0)
    (hgap : HasVacuumFormGap H vac Δ) (hΔ : 0 < Δ) (hsa : IsSelfAdjoint H.closure) :
    (closureDatum hdense hsym hvac hunit hground hgap hΔ hsa).gap = Δ := rfl

/-- **The core-to-spectrum theorem.**  An essentially self-adjoint Hamiltonian
whose gap is only ever estimated on a core has no spectrum in `[0, Δ)` on the
vacuum complement of its closure. -/
theorem core_to_domain_no_spectrum_below_gap {H : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hdense : Dense (H.domain : Set E)) (hsym : IsSymmetric H)
    (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hvac⟩ = 0)
    (hgap : HasVacuumFormGap H vac Δ) (hΔ : 0 < Δ) (hsa : IsSelfAdjoint H.closure)
    {lam : ℝ} (hlt : lam < Δ) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! ψ : H.closure.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 ∧
      H.closure ψ - (lam : ℂ) • (ψ : E) = y :=
  (closureDatum hdense hsym hvac hunit hground hgap hΔ hsa).exists_unique_solution_vacuumSector
    hlt hy

/-- **No excited state below the gap, from a core estimate.** -/
theorem core_to_domain_no_eigenvalue_below_gap {H : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ}
    (hdense : Dense (H.domain : Set E)) (hsym : IsSymmetric H)
    (hvac : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hvac⟩ = 0)
    (hgap : HasVacuumFormGap H vac Δ) (hΔ : 0 < Δ) (hsa : IsSelfAdjoint H.closure)
    {lam : ℝ} {ψ : H.closure.domain} (hne : (ψ : E) ≠ 0)
    (heig : H.closure ψ = (lam : ℂ) • (ψ : E)) (hlt : lam < Δ) : lam = 0 :=
  (closureDatum hdense hsym hvac hunit hground hgap hΔ hsa).eigenvalue_eq_zero_of_lt_gap
    hne heig hlt

end Complete

/-! ## Non-vacuity -/

section Witness

variable [CompleteSpace E]

/-- The projection Hamiltonian is closed and self-adjoint, and its own closure,
so `closureDatum` is inhabited: the core-to-domain hypotheses are satisfiable
simultaneously. -/
theorem projHam_isSymmetric (vac : E) (c : ℝ) : IsSymmetric (projHam vac c) := by
  exact VacuumGapDatum.isSymmetric_of_isSelfAdjoint (isSelfAdjoint_projHam vac c)

theorem projHam_dense (vac : E) (c : ℝ) : Dense (((projHam vac c).domain : Submodule ℂ E) : Set E) :=
  (isSelfAdjoint_projHam vac c).dense_domain

/-- The closure of the projection Hamiltonian is itself, because it is
self-adjoint and hence closed. -/
theorem projHam_closure (vac : E) (c : ℝ) : (projHam vac c).closure = projHam vac c := by
  have hcl : (projHam vac c).IsClosed := (isSelfAdjoint_projHam vac c).isClosed
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← (hcl.isClosable).graph_closure_eq_closure_graph]
  exact SetLike.coe_injective hcl.closure_eq

/-- All hypotheses of `closureDatum` are met by the projection Hamiltonian. -/
theorem closureDatum_witness (vac : E) (hunit : ‖vac‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) :
    (closureDatum (H := projHam vac Δ) (vac := vac) (Δ := Δ)
      (projHam_dense vac Δ) (projHam_isSymmetric vac Δ) Submodule.mem_top hunit
      (projHam_vac vac Δ) (hasVacuumFormGap_projHam vac Δ) hΔ
      (by rw [projHam_closure]; exact isSelfAdjoint_projHam vac Δ)).gap = Δ := rfl

end Witness

/-! ## Axiom audit -/

section Audit

#print axioms hasVacuumFormGap_closure
#print axioms closure_vac
#print axioms closureDatum_op
#print axioms closureDatum_gap
#print axioms core_to_domain_no_spectrum_below_gap
#print axioms core_to_domain_no_eigenvalue_below_gap
#print axioms closureDatum_witness

end Audit

end RequestProject.YangMills.CoreToDomainGap
