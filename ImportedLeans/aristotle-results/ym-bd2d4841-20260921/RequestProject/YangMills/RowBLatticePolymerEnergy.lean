/-
# Row B — the shell energy of lattice polymers, with the entropy half discharged

Row B asked for a geometric shell energy `E_n ≤ E₀ r^n`, `r < 1`, for the
cluster-expansion polymer activities.  `RowBShellEnergy` reduced that to two
inputs, an exponential activity majorant with rate `μ` and a polymer entropy
bound with rate `ν < μ`; `MarkedPolymerDecay` showed that differentiating the
activities (the *marked* activities Row B actually needs) costs only an
explicit constant and never the margin.

`LatticeAnimalEntropy` now supplies the entropy input **unconditionally** for the
polymers of a four-dimensional lattice gauge theory: the connected subsets of
`ℤ⁴` of size `n` containing a fixed site number at most `2e^{νn}` with
`ν = 1 + 2 log 8`.  That is a theorem, not a hypothesis, and it fixes `B` and `ν`
numerically.

This file combines the two.  What is left of Row B afterwards is a *single*
scalar: an activity decay rate `μ > 1 + 2 log 8` for the literal
cluster-expansion activities.  Everything else in the Row-B chain — the marks,
the entropy, the summation, the geometric ratio, the total-energy bound — is
proved.
-/
import RequestProject.YangMills.MarkedPolymerDecay
import RequestProject.YangMills.LatticeAnimalEntropy

namespace YangMills

open Finset

/-- The polymer entropy rate of the four-dimensional lattice, `ν = 1 + 2 log 8`. -/
noncomputable def lattice4EntropyRate : ℝ := 1 + 2 * Real.log 8

/-- **The geometric shell energy of marked lattice polymer activities.**  Only
the activity decay rate `μ` is assumed; the entropy is the proved lattice-animal
bound. -/
theorem lattice4_marked_shell_energy_geometric
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act : Finset (Fin 4 → ℤ) → ℝ}
    {A mu : ℝ} {m : ℕ} {v : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hact : ∀ n, ∀ S ∈ shell n, |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hA : 0 ≤ A) (hmu : lattice4EntropyRate < mu) (n : ℕ) :
    ∑ S ∈ shell n, |act S|
      ≤ ((A * markCost m mu lattice4EntropyRate) * 2)
          * shellRatio lattice4EntropyRate (markedRate mu lattice4EntropyRate) ^ n := by
  refine marked_shell_energy_geometric (A := A) (B := 2) (mu := mu)
    (nu := lattice4EntropyRate) (m := m) hact ?_ hA hmu n
  intro k
  have h := animal_shell_card_le (nb := nbFromE latticeStep) (nbE := latticeStep) (v := v)
    (nbFromE_enumerates latticeStep) (nbFromE_symm latticeStep_involutive) hshell k
  rw [card_latticeDir] at h
  rw [lattice4EntropyRate]
  exact h

/-- The total marked polymer energy of a four-dimensional lattice cluster
expansion is finite, with an explicit bound, as soon as the activity decay rate
exceeds the (proved) lattice entropy rate. -/
theorem lattice4_marked_shell_energy_tsum_le
    {shell : ℕ → Finset (Finset (Fin 4 → ℤ))} {act : Finset (Fin 4 → ℤ) → ℝ}
    {A mu : ℝ} {m : ℕ} {v : Fin 4 → ℤ}
    (hshell : ∀ n, ∀ S ∈ shell n, IsAnimal (nbFromE latticeStep) v S ∧ S.card = n)
    (hact : ∀ n, ∀ S ∈ shell n, |act S| ≤ A * (n : ℝ) ^ m * Real.exp (-(mu * n)))
    (hA : 0 ≤ A) (hmu : lattice4EntropyRate < mu) :
    ∑' n : ℕ, (∑ S ∈ shell n, |act S|)
      ≤ ((A * markCost m mu lattice4EntropyRate) * 2)
          / (1 - shellRatio lattice4EntropyRate (markedRate mu lattice4EntropyRate)) := by
  refine marked_shell_energy_tsum_le (A := A) (B := 2) (mu := mu)
    (nu := lattice4EntropyRate) (m := m) hact ?_ hA hmu
  intro k
  have h := animal_shell_card_le (nb := nbFromE latticeStep) (nbE := latticeStep) (v := v)
    (nbFromE_enumerates latticeStep) (nbFromE_symm latticeStep_involutive) hshell k
  rw [card_latticeDir] at h
  rw [lattice4EntropyRate]
  exact h

/-! ## Non-vacuity -/

/-- A one-point set is a connected polymer, so the animal predicate is
inhabited. -/
theorem isAnimal_singleton {V : Type*} [DecidableEq V] (nb : V → Finset V) (v : V) :
    IsAnimal nb v {v} := by
  refine ⟨Finset.mem_singleton_self v, ?_⟩
  intro u hu
  refine ⟨0, fun _ => v, rfl, ?_, ?_, ?_⟩
  · exact (Finset.mem_singleton.mp hu).symm
  · intro i hi
    omega
  · intro i _
    exact Finset.mem_singleton_self v

end YangMills
