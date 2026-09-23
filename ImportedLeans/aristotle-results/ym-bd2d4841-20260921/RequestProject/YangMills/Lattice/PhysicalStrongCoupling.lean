/-
# The gauge-invariant physical package at small coupling

`Lattice/GaugeInvariantSlice.lean` builds the gauge-invariant physical Hilbert
space of the literal Wilson slice measure, the physical vacuum, the restricted
energy form and the physical Hamiltonian, and reduces the mass gap there to
coercivity of the same form.  `Lattice/StrongCoupling.lean` proves that
coercivity for an explicit range of couplings.  This file combines the two: the
literal four-dimensional `SU(2)` lattice Yang–Mills theory, on its
gauge-invariant physical Hilbert space, has a proved positive mass gap at every
lattice spacing and every coupling below an explicit threshold.

As everywhere in this directory, this is a statement at fixed lattice spacing;
the threshold shrinks with the lattice volume and the gap is measured in units of
`a⁻¹`, so it says nothing about the continuum limit.  See `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.StrongCoupling
import RequestProject.YangMills.Lattice.GaugeInvariantSlice

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {chi : G → ℝ}

/-- **The gauge-invariant physical package of the literal lattice theory has the
full mass-gap conclusion whenever the Wilson action is uniformly small.** -/
theorem phys_massGap_of_small_action {n : ℕ} (hn : 1 ≤ n) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) {beta a M : ℝ}
    (hM : ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M)
    (hMsmall : (Real.exp (2 * M) - 1) ^ 2 + (Real.exp (2 * M)) ^ 2 < 2) (ha : 0 < a) :
    Clay.MassGapConclusion (physHamiltonian n hchi hconj beta a ha.le)
      (physVacuum n hchi hconj beta)
      (a⁻¹ * (2 - (Real.exp (2 * M) - 1) ^ 2 - (Real.exp (2 * M)) ^ 2)) := by
  refine phys_massGap_of_coercivity n hchi hconj beta a ha.le
    (mul_pos (inv_pos.2 ha) (by linarith)) ?_
  intro ψ hψ
  have hq := energyForm_coercive_of_small_action (zero_ne_one_zmod hn) hchi beta hM
    (ψ : SliceL2 n G beta chi) hψ
  rw [physEnergyForm, restrictForm_apply, scaleForm_apply, Complex.re_ofReal_mul]
  have hnn : (0 : ℝ) ≤ a⁻¹ := (inv_pos.2 ha).le
  have hnorm : ‖ψ‖ = ‖(ψ : SliceL2 n G beta chi)‖ := rfl
  rw [hnorm]
  nlinarith [hq]

/-- **The literal four-dimensional `SU(2)` lattice Yang–Mills theory, on its
gauge-invariant physical Hilbert space, has a positive mass gap at lattice
spacing `a` whenever `64|β|(n+1)^4 ≤ 1/10`.**  The conclusion is the full
vacuum-sector statement carried by `Clay.MassGapConclusion`: positivity of the
gap, the form gap `Δ‖ψ‖² ≤ Re⟪ψ, Hψ⟫` on the vacuum complement, absence of an
eigenvalue in `(0,Δ)`, unique solvability of `Hψ − λψ = y` on the vacuum sector
for every `λ < Δ`, and the resolvent bound `‖ψ‖ ≤ (Δ−λ)⁻¹‖(H−λ)ψ‖`. -/
theorem ym_phys_massGap_of_coupling_le {n : ℕ} (hn : 1 ≤ n) {beta a : ℝ} (ha : 0 < a)
    (hbeta : 64 * |beta| * ((n : ℝ) + 1) ^ 4 ≤ 1 / 10) :
    Clay.MassGapConclusion (ymPhysicalHamiltonian n beta a ha.le) (ymPhysicalVacuum n beta)
      (a⁻¹ * (2 - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4)) - 1) ^ 2
        - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4))) ^ 2)) := by
  refine phys_massGap_of_small_action (G := SU2) hn continuous_chiSU2 chiSU2_conj
    (abs_wilsonAction_SU2_le beta) (exp_smallness ?_ ?_) ha
  · positivity
  · linarith

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms phys_massGap_of_small_action
#print axioms ym_phys_massGap_of_coupling_le

end Audit
