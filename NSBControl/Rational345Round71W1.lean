import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import NSBControl.Rational345RealSnapshotRows

/-!
# W1 narrow Round71/Lean finite-real codec weld

This is intentionally not a general cross-prover interoperability layer.  It
mirrors exactly the Round851 coordinate convention used by Agda:

  (x_re, x_im, y_re, y_im, z_re, z_im)

for one positive reality-orbit representative, and checks the concrete 3-4-5
initial state plus its literal radius-four RHS.  Negative modes are reconstructed
by complex conjugation rather than duplicated as independent coordinates.
-/

namespace NSBControl
namespace Rational345Round71W1

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse
open Rational345RealSnapshotRows

classical

abbrev Real6 := Fin 6 → ℝ

/-- Exact Round851 slot order. -/
def encodeVec3 (value : Vec3) : Real6 :=
  ![(value 0).re, (value 0).im,
    (value 1).re, (value 1).im,
    (value 2).re, (value 2).im]

def decodeVec3 (slots : Real6) : Vec3 :=
  ![(slots 0 : ℂ) + slots 1 * Complex.I,
    (slots 2 : ℂ) + slots 3 * Complex.I,
    (slots 4 : ℂ) + slots 5 * Complex.I]

theorem decode_encode (value : Vec3) : decodeVec3 (encodeVec3 value) = value := by
  funext j
  fin_cases j <;> apply Complex.ext <;> simp [encodeVec3, decodeVec3]

/-- Three positive representatives of the six-mode initial state. -/
def positiveInitialSlots (k : Mode) : Real6 :=
  if k = k300 then encodeVec3 v300
  else if k = k040 then encodeVec3 v040
  else if k = k340 then encodeVec3 v340
  else 0

/-- Decode only the concrete initial reality orbits needed by the decision
experiment. -/
def decodeInitial : State := fun k =>
  if k = k300 then decodeVec3 (positiveInitialSlots k300)
  else if k = km300 then vecConj (decodeVec3 (positiveInitialSlots k300))
  else if k = k040 then decodeVec3 (positiveInitialSlots k040)
  else if k = k0m40 then vecConj (decodeVec3 (positiveInitialSlots k040))
  else if k = k340 then decodeVec3 (positiveInitialSlots k340)
  else if k = km3m40 then vecConj (decodeVec3 (positiveInitialSlots k340))
  else 0

theorem decodeInitial_exact : decodeInitial = u₀ := by
  funext k
  simp [decodeInitial, positiveInitialSlots, decode_encode,
    u₀, k300, km300, k040, k0m40, k340, km3m40]

/-- The seed support is contained in the eight nonzero R850 outputs. -/
theorem seedModes_subset_activeOutputs : seedModes ⊆ activeOutputs := by
  intro k hk
  simp [seedModes, activeOutputs] at hk ⊢
  aesop

/-- Outside the eight active outputs both the initial velocity and the initial
projected forcing vanish, hence so does the literal Galerkin RHS. -/
theorem galerkinField_u₀_zero_of_not_mem_active
    {k : Mode} (hk : k ∉ activeOutputs) : galerkinField u₀ k = 0 := by
  have hkSeed : k ∉ seedModes := by
    intro hseed
    exact hk (seedModes_subset_activeOutputs hseed)
  have hu : u₀ k = 0 := u₀_zero_of_not_mem_seed hkSeed
  have hf : projectedNonlinearity u₀ k = 0 :=
    projectedNonlinearity_u₀_zero_of_not_mem_active hk
  funext j
  have hbil : projectedBilinear u₀ u₀ k = 0 := by
    simpa [projectedNonlinearity] using hf
  simp [galerkinField, viscousLinear, hu, hbil]

/-- Four positive reality representatives of the eight-output initial RHS. -/
def rhsPositiveSlots (k : Mode) : Real6 :=
  if k = k₅ then encodeVec3 (galerkinField u₀ k₅)
  else if k = k₆ then encodeVec3 (galerkinField u₀ k₆)
  else if k = k₇ then encodeVec3 (galerkinField u₀ k₇)
  else if k = k₈ then encodeVec3 (galerkinField u₀ k₈)
  else 0

private theorem field_pair₁₈ :
    galerkinField u₀ k₁ = vecConj (galerkinField u₀ k₈) := by
  change viscousLinear u₀ k₁ + projectedNonlinearity u₀ k₁ =
    vecConj (viscousLinear u₀ k₈ + projectedNonlinearity u₀ k₈)
  rw [projectedNonlinearity_k₁, projectedNonlinearity_k₈]
  funext j
  fin_cases j <;>
    simp [viscousLinear, vecConj, u₀, v300, v040, v340,
      k₁, k₈, km3m40, k340, normSq, kReal, kInt, axisInt,
      f₁, f₈, Rational345RealSnapshotRows.c,
      Rational345RealSnapshotRows.v] <;> norm_num <;> ring

private theorem field_pair₂₇ :
    galerkinField u₀ k₂ = vecConj (galerkinField u₀ k₇) := by
  change viscousLinear u₀ k₂ + projectedNonlinearity u₀ k₂ =
    vecConj (viscousLinear u₀ k₇ + projectedNonlinearity u₀ k₇)
  rw [projectedNonlinearity_k₂, projectedNonlinearity_k₇]
  funext j
  fin_cases j <;>
    simp [viscousLinear, vecConj, u₀, v300, v040, v340,
      k₂, k₇, km300, k300, normSq, kReal, kInt, axisInt,
      f₂, f₇, Rational345RealSnapshotRows.c,
      Rational345RealSnapshotRows.v] <;> norm_num <;> ring

private theorem field_pair₃₆ :
    galerkinField u₀ k₃ = vecConj (galerkinField u₀ k₆) := by
  change viscousLinear u₀ k₃ + projectedNonlinearity u₀ k₃ =
    vecConj (viscousLinear u₀ k₆ + projectedNonlinearity u₀ k₆)
  rw [projectedNonlinearity_k₃, projectedNonlinearity_k₆]
  funext j
  fin_cases j <;>
    simp [viscousLinear, vecConj, u₀,
      k₃, k₆, km340, k3m40, normSq, kReal, kInt, axisInt,
      f₃, f₆, Rational345RealSnapshotRows.c,
      Rational345RealSnapshotRows.v] <;> norm_num <;> ring

private theorem field_pair₄₅ :
    galerkinField u₀ k₄ = vecConj (galerkinField u₀ k₅) := by
  change viscousLinear u₀ k₄ + projectedNonlinearity u₀ k₄ =
    vecConj (viscousLinear u₀ k₅ + projectedNonlinearity u₀ k₅)
  rw [projectedNonlinearity_k₄, projectedNonlinearity_k₅]
  funext j
  fin_cases j <;>
    simp [viscousLinear, vecConj, u₀, v040,
      k₄, k₅, k0m40, k040, normSq, kReal, kInt, axisInt,
      f₄, f₅, Rational345RealSnapshotRows.c,
      Rational345RealSnapshotRows.v] <;> norm_num <;> ring

/-- Decode the initial RHS from only its four positive reality representatives. -/
def decodeInitialRHS : State := fun k =>
  if k = k₅ then decodeVec3 (rhsPositiveSlots k₅)
  else if k = k₆ then decodeVec3 (rhsPositiveSlots k₆)
  else if k = k₇ then decodeVec3 (rhsPositiveSlots k₇)
  else if k = k₈ then decodeVec3 (rhsPositiveSlots k₈)
  else if k = k₄ then vecConj (decodeVec3 (rhsPositiveSlots k₅))
  else if k = k₃ then vecConj (decodeVec3 (rhsPositiveSlots k₆))
  else if k = k₂ then vecConj (decodeVec3 (rhsPositiveSlots k₇))
  else if k = k₁ then vecConj (decodeVec3 (rhsPositiveSlots k₈))
  else 0

/-- Narrow W1 closure: the six-slot Round851 convention reconstructs both the
actual initial state and its actual literal real radius-four RHS. -/
theorem decodeInitialRHS_exact : decodeInitialRHS = galerkinField u₀ := by
  funext k
  by_cases hk : k ∈ activeOutputs
  · simp [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈] at hk
    rcases hk with h | h | h | h | h | h | h | h
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode, field_pair₁₈]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode, field_pair₂₇]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode, field_pair₃₆]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode, field_pair₄₅]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode]
    · subst k
      simp [decodeInitialRHS, rhsPositiveSlots, decode_encode]
  · have hz := galerkinField_u₀_zero_of_not_mem_active hk
    have hne :
        k ≠ k₁ ∧ k ≠ k₂ ∧ k ≠ k₃ ∧ k ≠ k₄ ∧
        k ≠ k₅ ∧ k ≠ k₆ ∧ k ≠ k₇ ∧ k ≠ k₈ := by
      simpa [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈] using hk
    rcases hne with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    simpa [decodeInitialRHS, h1,h2,h3,h4,h5,h6,h7,h8] using hz.symm

end Rational345Round71W1
end NSBControl
