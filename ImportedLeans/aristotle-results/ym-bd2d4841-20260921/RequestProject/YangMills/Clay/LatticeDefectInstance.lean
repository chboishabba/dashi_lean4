/-
# A lattice-shaped instance of the assembled mass-gap statement

`CommutingProjectionGap` provides the finite-lattice engine: for a list of
pairwise commuting orthogonal projections `P₁,…,P_k` (the local averaging
operators of a strong-coupling lattice Hamiltonian) the Hamiltonian
`H = Σᵢ (1 − Pᵢ)` has form gap `1` above a vacuum that is jointly invariant,
provided the product `P₁⋯P_k` annihilates the vacuum complement.

This file feeds that engine into the assembly of `Clay/MassGapAssembly.lean`.
Because the local Hamiltonian is bounded and everywhere defined,
`Clay/BoundedCoreEvolution.lean` discharges every domain-theoretic hypothesis of
the same-object weld, so for a constant (single-scale) family the whole package
is inhabited and the conclusion is *unconditional*:

* `latticeDefect_massGap` — the local Hamiltonian satisfies `MassGapConclusion`
  with gap `1`: no eigenvalue in `(0,1)`, unique solvability of `Hψ − λψ = y` in
  the vacuum sector for every real `λ < 1`, and the resolvent bound.
* `latticeDefect_massGap_of_limit` — the same for a genuine family of such
  lattice Hamiltonians which converges in the vacuum-sector graph sense, welded
  to a reconstructed Hamiltonian.

**Honest scope.**  This is a lattice-shaped model statement, not a Yang–Mills
theorem: the projections are inputs, and nothing here says that the physical
Yang–Mills energy operator at spacing `a` is of this form.  It is the first link
of the chain, made fully explicit.
-/
import Mathlib
import RequestProject.YangMills.Clay.BoundedCoreEvolution
import RequestProject.YangMills.CommutingProjectionGap

namespace RequestProject.YangMills.Clay

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open RequestProject.YangMills.CommutingProjectionGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The constant cutoff family of a single lattice defect Hamiltonian. -/
noncomputable def latticeCutoff (l : List (E →L[ℂ] E)) (hp : ∀ T ∈ l, IsOrthProj T)
    (vac : E) (hunit : ‖vac‖ = 1) (hinv : ∀ T ∈ l, T vac = vac) : CutoffFamily E where
  ham := fun _ => (localHamiltonian l).toPMap ⊤
  vacuum := fun _ => vac
  limitHam := (localHamiltonian l).toPMap ⊤
  vac := vac
  graphLimit := isVacuumGraphLimit_const _ _
  limit_selfAdjoint := UnboundedFormGapResolvent.isSelfAdjoint_toPMap_top
    (isSelfAdjoint_localHamiltonian l hp)
  vac_mem := Submodule.mem_top
  vac_unit := hunit
  vac_ground := localHamiltonian_apply_eq_zero l hinv

/-- **The lattice defect Hamiltonian has the full mass-gap conclusion at gap
`1`.**  Every hypothesis of the assembled theorem is discharged here: the gap by
the commuting-projection engine, the graph limit by constancy, and the core and
evolution by boundedness. -/
theorem latticeDefect_massGap (l : List (E →L[ℂ] E)) (hp : ∀ T ∈ l, IsOrthProj T)
    (hc : l.Pairwise Commute) (vac : E) (hunit : ‖vac‖ = 1)
    (hinv : ∀ T ∈ l, T vac = vac)
    (hker : ∀ x : E, ⟪vac, x⟫_ℂ = 0 → l.prod x = 0) :
    MassGapConclusion ((localHamiltonian l).toPMap ⊤) vac 1 :=
  clay_mass_gap_of_inputs (latticeCutoff l hp vac hunit hinv) one_pos
    (fun _ => hasVacuumFormGap_localHamiltonian l hp hc vac hker)
    (OSWeld.selfBounded (localHamiltonian l))

/-- **A converging family of lattice defect Hamiltonians.**  If each scale is a
commuting-projection model with the same vacuum, and the family has a
vacuum-sector graph limit which is welded to a reconstructed Hamiltonian, then
the reconstructed Hamiltonian has the mass gap `1`. -/
theorem latticeDefect_massGap_of_limit (C : CutoffFamily E)
    (l : ℕ → List (E →L[ℂ] E)) (hfam : C.ham = fun n => (localHamiltonian (l n)).toPMap ⊤)
    (hp : ∀ n, ∀ T ∈ l n, IsOrthProj T) (hc : ∀ n, (l n).Pairwise Commute)
    (hker : ∀ n, ∀ x : E, ⟪C.vacuum n, x⟫_ℂ = 0 → (l n).prod x = 0)
    {Hos : E →ₗ.[ℂ] E} (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac 1 := by
  refine clay_mass_gap_of_inputs C one_pos (fun n => ?_) W
  rw [hfam]
  exact hasVacuumFormGap_localHamiltonian (l n) (hp n) (hc n) (C.vacuum n) (hker n)

/-! ## Non-vacuity of the lattice instance -/

/-- The hypotheses of `latticeDefect_massGap` are satisfiable with a genuinely
nonzero Hamiltonian: the one-term list consisting of the projection onto the
vacuum line gives `H = 1 − P_{ℂΩ}` and gap `1`. -/
theorem latticeDefect_massGap_witness (vac : E) (hunit : ‖vac‖ = 1) :
    MassGapConclusion
      ((localHamiltonian [((ℂ ∙ vac).starProjection)]).toPMap ⊤) vac 1 := by
  refine latticeDefect_massGap _ ?_ (by simp) vac hunit ?_ ?_
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    exact isOrthProj_vacLine vac
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self vac)
  · intro x hx
    have hmem : x ∈ (ℂ ∙ vac)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, ← inner_conj_symm]
      simp [hx]
    have hz : (ℂ ∙ vac).starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hmem
    simpa using hz

end RequestProject.YangMills.Clay

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Clay

#print axioms latticeDefect_massGap
#print axioms latticeDefect_massGap_of_limit
#print axioms latticeDefect_massGap_witness

end Audit
