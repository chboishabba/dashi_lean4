import Mathlib
import YangMills.OSCenteredExcitationSector
import YangMills.OSStronglyContinuousSemigroup

/-!
# Restrict the continuous OS semigroup to the excitation sector

A symmetric OS semigroup fixing a normalized vacuum preserves the vacuum
orthogonal sector.  Hence its full continuous-time contraction semigroup
restricts canonically to the excitation sector, with strong continuity,
symmetry and positivity inherited from the same operators.

This pays the excitation-sector invariance part of E2 before any appeal to an
unbounded generator theorem.
-/

namespace RequestProject.YangMills

structure OSVacuumStronglyContinuousSemigroup
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    extends OSSymmetricPositiveStronglyContinuousSemigroup H where
  vacuum : H
  vacuumNormalized : ⟪vacuum, vacuum⟫_ℝ = 1
  vacuumFixed : ∀ t : ℝ≥0,
    toOSSymmetricPositiveStronglyContinuousSemigroup
      .toOSStronglyContinuousSemigroup.transfer t vacuum = vacuum

namespace OSVacuumStronglyContinuousSemigroup

/-- The continuous OS transfer preserves `Ω⊥` at every nonnegative time. -/
theorem transfer_preserves_excitation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H)
    (t : ℝ≥0) {x : H}
    (hx : x ∈ vacuumOrthogonalSubmodule S.vacuum) :
    S.toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.transfer t x ∈
      vacuumOrthogonalSubmodule S.vacuum := by
  apply os_transfer_preserves_vacuumOrthogonal
    S.vacuum
    (S.toOSSymmetricPositiveStronglyContinuousSemigroup
      .toOSStronglyContinuousSemigroup.transfer t).toLinearMap
  · exact S.vacuumFixed t
  · intro left right
    exact (S.toOSSymmetricPositiveStronglyContinuousSemigroup
      .symmetric t left right).symm
  · exact hx

/-- Continuous transfer restricted in both domain and codomain to `Ω⊥`. -/
def excitationTransfer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H)
    (t : ℝ≥0) :
    vacuumOrthogonalSubmodule S.vacuum →L[ℝ]
      vacuumOrthogonalSubmodule S.vacuum :=
  ((S.toOSSymmetricPositiveStronglyContinuousSemigroup
      .toOSStronglyContinuousSemigroup.transfer t)
      .domRestrict (vacuumOrthogonalSubmodule S.vacuum)).codRestrict
    (vacuumOrthogonalSubmodule S.vacuum)
    (fun x => S.transfer_preserves_excitation t x.property)

/-- The restricted family is itself a strongly continuous contraction semigroup. -/
def toExcitationStronglyContinuousSemigroup
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) :
    OSStronglyContinuousSemigroup (vacuumOrthogonalSubmodule S.vacuum) where
  transfer := S.excitationTransfer
  transfer_zero := by
    ext x
    apply Subtype.ext
    simp [excitationTransfer,
      S.toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.zero_apply]
  transfer_add := by
    intro s t
    ext x
    apply Subtype.ext
    simp [excitationTransfer,
      S.toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.add_apply]
  contractive := by
    intro t x
    exact S.toOSSymmetricPositiveStronglyContinuousSemigroup
      .toOSStronglyContinuousSemigroup.contractive t (x : H)
  stronglyContinuous := by
    intro x
    apply Continuous.subtype_mk
    · simpa [excitationTransfer] using
        S.toOSSymmetricPositiveStronglyContinuousSemigroup
          .toOSStronglyContinuousSemigroup.stronglyContinuous (x : H)
    · intro t
      exact (S.excitationTransfer t x).property

/-- The excitation-sector semigroup inherits OS symmetry and positivity. -/
def toExcitationSymmetricPositiveStronglyContinuousSemigroup
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) :
    OSSymmetricPositiveStronglyContinuousSemigroup
      (vacuumOrthogonalSubmodule S.vacuum) where
  toOSStronglyContinuousSemigroup :=
    S.toExcitationStronglyContinuousSemigroup
  symmetric := by
    intro t x y
    simpa [excitationTransfer] using
      S.toOSSymmetricPositiveStronglyContinuousSemigroup.symmetric
        t (x : H) (y : H)
  positive := by
    intro t x
    simpa [excitationTransfer] using
      S.toOSSymmetricPositiveStronglyContinuousSemigroup.positive
        t (x : H)

end OSVacuumStronglyContinuousSemigroup

end RequestProject.YangMills
