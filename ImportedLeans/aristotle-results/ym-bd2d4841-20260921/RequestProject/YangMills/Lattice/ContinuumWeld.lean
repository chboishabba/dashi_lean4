/-
# Welding the literal lattice family to the continuum consumer

`Lattice/GaugeInvariantSlice.lean` constructs the **literal** physical objects of
four-dimensional `SU(2)` Wilson Yang–Mills at finite spacing: the gauge-invariant
Hilbert space `ymPhysicalSlice n β = L²_gauge(μ_{n,β})`, the physical vacuum
`ymPhysicalVacuum n β`, and the physical Hamiltonian `ymPhysicalHamiltonian`,
self-adjoint and annihilating the vacuum.  These spaces genuinely depend on the
cutoff, so they could not be fed into the fixed-carrier consumer of
`ContinuumGapTransport`.  `VaryingCarrierTransport.lean` removes that
restriction, and this file performs the weld.

What is proved here:

* `ym_continuum_massGap_of_uniform_gap_and_graphLimit` — for **the literal
  Wilson family** along an arbitrary trajectory `k ↦ (n_k, β_k, a_k)`, isometric
  embeddings into a common carrier `E`, a *uniform* vacuum form gap `Δ > 0`, and
  an embedded vacuum-sector graph limit `Hinf` that is self-adjoint with a
  normalised zero-energy vacuum, the continuum Hamiltonian satisfies the full
  `Clay.MassGapConclusion` at the same `Δ`;
* `ym_continuum_massGap_os_of_same_evolution` — the same with the
  Osterwalder–Schrader Hamiltonian in place of `Hinf`, given that the two
  generate the same evolution on a common core.

Both are theorems about the literal lattice Hamiltonians: no auxiliary or
synthetic model appears anywhere in the statements, and the finite-side objects
are exactly those constructed from the Wilson–Gibbs measure.

**Exactly four physical inputs remain, and they are displayed as hypotheses.**

* `hgap` — the uniform gap along the trajectory (`F1`).  This is *not* supplied
  by `Lattice/PhysicalStrongCoupling.lean`: that theorem gives a gap at fixed
  spacing under `64|β|(n+1)⁴ ≤ 1/10`, a threshold that shrinks with the volume
  and lies at the wrong end of the coupling flow.
* `J` — the isometric embeddings of the literal carriers into a common Hilbert
  space (`F2`).  Note that the weld needs *only* the embeddings: no vacuum
  compatibility, orthogonality-preservation, intertwining or domain-preservation
  conditions are required, because the gap hypothesis is stated on each literal
  carrier in its own inner product.  This reduces `F2` from a list of
  compatibility obligations to the bare existence of the embeddings.
* `hlim`, `hsa`, `hmem`, `hunit`, `hground` — the actual continuum limit (`F3`).
* `hUV` — the Yang–Mills/OS identity `U^{YM} = U^{OS}` (`F4`), in the second
  theorem only.

No Clay-level claim is made in this file.  See `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.PhysicalStrongCoupling
import RequestProject.YangMills.VaryingCarrierTransport
import RequestProject.YangMills.SameObjectGapTransfer

namespace RequestProject.YangMills.Lattice

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.VaryingCarrierTransport
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The literal cutoff family of physical Hamiltonians** along a trajectory
`k ↦ (vol k, beta k, a k)`: at step `k` this is the Hamiltonian of the
four-dimensional `SU(2)` Wilson theory with `vol k + 1` sites per direction at
inverse coupling `beta k` and spacing `a k`, acting on its gauge-invariant
physical Hilbert space. -/
noncomputable def ymTrajectoryHam (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (k : ℕ) :
    ymPhysicalSlice (vol k) (beta k) →ₗ.[ℂ] ymPhysicalSlice (vol k) (beta k) :=
  ymPhysicalHamiltonian (vol k) (beta k) (a k) (ha k)

/-- The literal cutoff family of physical vacua along the same trajectory. -/
noncomputable def ymTrajectoryVacuum (vol : ℕ → ℕ) (beta : ℕ → ℝ) (k : ℕ) :
    ymPhysicalSlice (vol k) (beta k) :=
  ymPhysicalVacuum (vol k) (beta k)

/-- **The continuum weld for the literal Wilson family.**  A uniform positive
vacuum form gap for the literal finite-spacing physical Hamiltonians, isometric
embeddings of their (varying) physical Hilbert spaces into a common carrier, and
an embedded vacuum-sector graph limit which is self-adjoint with a normalised
zero-energy vacuum, together give the full mass-gap conclusion for the limit:
the form gap on the vacuum complement, absence of an eigenvalue in `(0, Δ)`,
unique solvability of `Hψ − λψ = y` on the vacuum sector for every real `λ < Δ`,
and the resolvent bound `(Δ − λ)⁻¹`.

Every finite-side object in this statement is the literal Wilson object. -/
theorem ym_continuum_massGap_of_uniform_gap_and_graphLimit
    (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (J : ∀ k, ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] E)
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a ha k)
      (ymTrajectoryVacuum vol beta k) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J (ymTrajectoryHam vol beta a ha)
      (ymTrajectoryVacuum vol beta) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain) (hunit : ‖vac‖ = 1)
    (hground : Hinf ⟨vac, hmem⟩ = 0) :
    Clay.MassGapConclusion Hinf vac Δ :=
  Clay.massGapConclusion_of_datum
    (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ)

/-- **The welded endpoint with the Osterwalder–Schrader Hamiltonian.**  If, in
addition to the hypotheses of the previous theorem, the reconstructed evolution
`V` coincides with the continuum Yang–Mills evolution `U` and both Hamiltonians
generate their evolution on a common core, then the OS Hamiltonian satisfies the
same mass-gap conclusion, with the *same* gap constant and the same vacuum.

The equality `hUV : U = V` is the physical Yang–Mills/OS identification; it is an
input here, and it is not proved anywhere in this repository. -/
theorem ym_continuum_massGap_os_of_same_evolution
    (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (J : ∀ k, ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] E)
    {Hinf Hos : E →ₗ.[ℂ] E} {vac : E} {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a ha k)
      (ymTrajectoryVacuum vol beta k) Δ)
    (hlim : IsEmbeddedVacuumGraphLimit J (ymTrajectoryHam vol beta a ha)
      (ymTrajectoryVacuum vol beta) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain) (hunit : ‖vac‖ = 1)
    (hground : Hinf ⟨vac, hmem⟩ = 0)
    {U V : ℝ → E → E} {S : Submodule ℂ E} (hUV : U = V)
    (hcYM : Hinf.HasCore S) (hcOS : Hos.HasCore S)
    (hgYM : IsPMapEvolutionGenerator U S Hinf)
    (hgOS : IsPMapEvolutionGenerator V S Hos) :
    Clay.MassGapConclusion Hos vac Δ :=
  Clay.massGapConclusion_of_datum
    (SameObjectGapTransfer.vacuumGapDatum_of_same_evolution hUV hcYM hcOS hgYM hgOS
      (embeddedContinuumDatum hgap hlim hsa hmem hunit hground hΔ) rfl)

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms ym_continuum_massGap_of_uniform_gap_and_graphLimit
#print axioms ym_continuum_massGap_os_of_same_evolution

end Audit
