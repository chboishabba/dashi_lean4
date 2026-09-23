/-
# The literal four-dimensional `SU(2)` lattice Yang–Mills package

This file instantiates the construction of `Lattice/Wilson.lean` and
`Lattice/TransferForm.lean` at the actual gauge group `SU(2)` with the actual
Wilson character `χ(g) = Re tr ρ(g)` of the defining representation, on the
periodic four-dimensional lattice with `n+1` sites in every direction, at
inverse coupling `β` and lattice spacing `a`.

Everything below is a theorem about that literal object:

* `ymGibbs` — the Wilson–Gibbs probability measure of `SU(2)` lattice gauge
  theory; it is invariant under lattice gauge transformations
  (`ymGibbs_gauge_invariant`) and under lattice translations
  (`ymGibbs_translation_invariant`);
* `ymHilbert`, `ymVacuum` — the physical Hilbert space of the time slice and the
  vacuum, a unit vector (`norm_ymVacuum`);
* `ymEnergyForm` — the physical energy form `a⁻¹(1 − ½(T + T*))` of the Euclidean
  transfer operator, bounded and Hermitian by construction, annihilating the
  vacuum (`ymEnergyForm_vacuum`);
* `ymHamiltonian` — the finite-spacing Hamiltonian obtained from the form by
  Riesz representation; it is self-adjoint (`ymHamiltonian_isSelfAdjoint`) and
  annihilates the vacuum (`ymHamiltonian_vacuum`);
* `HasLatticeCoercivity` — the one remaining finite-spacing physical estimate:
  the mass gap of the transfer matrix, written as coercivity of this same form on
  the vacuum complement;
* `lattice_massGap_of_coercivity` — given that estimate, the literal lattice
  theory satisfies the full mass-gap conclusion (form gap, no eigenvalue below
  the gap, unique solvability on the vacuum sector and the resolvent bound).

No part of the finite-spacing package is assumed except `HasLatticeCoercivity`,
whose status is discussed in `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.SU2
import RequestProject.YangMills.Lattice.TransferForm
import RequestProject.YangMills.Clay.MassGapAssembly

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable (n : ℕ) (beta : ℝ)

/-- The Wilson–Gibbs measure of four-dimensional `SU(2)` lattice gauge theory. -/
noncomputable def ymGibbs : Measure (Conf n SU2) := gibbs n SU2 beta chiSU2

theorem isProbabilityMeasure_ymGibbs : IsProbabilityMeasure (ymGibbs n beta) :=
  isProbabilityMeasure_gibbs continuous_chiSU2 beta

/-- **Gauge invariance of the literal `SU(2)` lattice measure.** -/
theorem ymGibbs_gauge_invariant (g : Site n → SU2) :
    MeasurePreserving (gaugeTransform g) (ymGibbs n beta) (ymGibbs n beta) :=
  measurePreserving_gauge_gibbs continuous_chiSU2 chiSU2_conj beta g

/-- **Translation invariance of the literal `SU(2)` lattice measure.** -/
theorem ymGibbs_translation_invariant (v : Site n) :
    MeasurePreserving (translate (G := SU2) v) (ymGibbs n beta) (ymGibbs n beta) :=
  measurePreserving_translate_gibbs continuous_chiSU2 beta v

/-- The physical Hilbert space of a time slice. -/
noncomputable abbrev ymHilbert : Type := SliceL2 n SU2 beta chiSU2

/-- The lattice vacuum. -/
noncomputable def ymVacuum : ymHilbert n beta :=
  vacuum (n := n) continuous_chiSU2 beta

theorem norm_ymVacuum : ‖ymVacuum n beta‖ = 1 :=
  norm_vacuum (n := n) continuous_chiSU2 beta

variable (a : ℝ)

/-- **The literal finite-spacing Yang–Mills energy form** at lattice spacing `a`:
`a⁻¹(1 − ½(T + T*))` for the Euclidean transfer operator `T` of the `SU(2)`
Wilson–Gibbs measure. -/
noncomputable def ymEnergyForm (ha : 0 ≤ a) :
    Clay.BoundedSesqForm (ymHilbert n beta) :=
  scaleForm a⁻¹ (inv_nonneg.2 ha) (energyForm (n := n) continuous_chiSU2 beta)

/-- The energy form annihilates the vacuum. -/
theorem ymEnergyForm_vacuum (ha : 0 ≤ a) (φ : ymHilbert n beta) :
    (ymEnergyForm n beta a ha).form φ (ymVacuum n beta) = 0 := by
  rw [ymEnergyForm, scaleForm_apply, ymVacuum,
    energyForm_vacuum (n := n) continuous_chiSU2 beta φ, mul_zero]

/-- **The finite-spacing Hamiltonian** of the literal lattice theory, obtained
from the energy form by Riesz representation. -/
noncomputable def ymHamiltonian (ha : 0 ≤ a) :
    ymHilbert n beta →ₗ.[ℂ] ymHilbert n beta :=
  (ymEnergyForm n beta a ha).hamiltonian

theorem ymHamiltonian_isSelfAdjoint (ha : 0 ≤ a) :
    IsSelfAdjoint (ymHamiltonian n beta a ha) :=
  (ymEnergyForm n beta a ha).isSelfAdjoint_hamiltonian

/-- The vacuum has zero energy. -/
theorem ymHamiltonian_vacuum (ha : 0 ≤ a) :
    (ymHamiltonian n beta a ha) ⟨ymVacuum n beta, Submodule.mem_top⟩ = 0 :=
  (ymEnergyForm n beta a ha).hamiltonian_apply_eq_zero (ymEnergyForm_vacuum n beta a ha)

/-- **The remaining finite-spacing physical estimate**: the energy form of the
literal `SU(2)` lattice theory is `Δ`-coercive on the vacuum complement.  In
terms of the transfer operator this says that the spectrum of `½(T+T*)` on the
orthogonal complement of the vacuum lies below `1 − aΔ`, i.e. that the lattice
theory has a mass gap at least `Δ` in physical units. -/
def HasLatticeCoercivity (Δ : ℝ) (ha : 0 ≤ a) : Prop :=
  ∀ ψ : ymHilbert n beta, ⟪ymVacuum n beta, ψ⟫_ℂ = 0 →
    Δ * ‖ψ‖ ^ 2 ≤ ((ymEnergyForm n beta a ha).form ψ ψ).re

/-- **The literal finite-spacing mass-gap conclusion.**  Given the coercivity
estimate for the literal `SU(2)` Wilson energy form, the finite-spacing
Hamiltonian of the literal lattice theory has the full vacuum-sector mass gap
`Δ`: the form gap, no eigenvalue in `(0,Δ)`, unique solvability of
`Hψ − λψ = y` on the vacuum sector for every `λ < Δ`, and the resolvent bound. -/
theorem lattice_massGap_of_coercivity {Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 ≤ a)
    (hcoer : HasLatticeCoercivity n beta a Δ ha) :
    Clay.MassGapConclusion (ymHamiltonian n beta a ha) (ymVacuum n beta) Δ :=
  Clay.massGapConclusion_of_datum
    ((ymEnergyForm n beta a ha).gapDatum (norm_ymVacuum n beta) hΔ
      (ymEnergyForm_vacuum n beta a ha) hcoer)

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms ymGibbs_gauge_invariant
#print axioms ymGibbs_translation_invariant
#print axioms norm_ymVacuum
#print axioms ymEnergyForm_vacuum
#print axioms ymHamiltonian_isSelfAdjoint
#print axioms ymHamiltonian_vacuum
#print axioms lattice_massGap_of_coercivity

end Audit
