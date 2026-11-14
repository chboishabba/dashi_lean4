import Mathlib
import YangMills.OSCenteredSpectralNoPollution
import YangMills.HalfRatePhysicalTimeNormalization

open Filter MeasureTheory

/-!
# Same-H subgap spectral-window exclusion

The physical gap argument is now reduced to the standard spectral-calculus
statement that a nonempty energy window below a cutoff `E_*` gives a nonzero
projection whose transfer moments are bounded below by

  exp(-a E_*)^n * ‖P x‖².

If `E_* < log 2 / a`, that base is strictly larger than one half.  The centered
same-carrier half-rate theorem then forces the projection to be zero, a
contradiction.  This file proves that compiler step and leaves only the genuine
functional-calculus construction of such windows external.
-/

namespace RequestProject.YangMills

/--
A genuine same-H spectral window below the half-rate mass floor, expressed only
through the consequences needed by the discrete transfer argument.
-/
structure SameHSubgapTransferWindow
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (time : WilsonPhysicalTimeStep) where
  energyCeiling : ℝ
  energyBelowFloor : energyCeiling < time.halfRateMassFloor
  projection : vacuumOrthogonalSubmodule weld.vacuum →L[ℝ]
    vacuumOrthogonalSubmodule weld.vacuum
  projectionNonzero : projection ≠ 0
  transferLowerBound :
    SpectralWindowLowerBound weld.excitationTransfer projection
      (Real.exp (-time.step * energyCeiling))

/-- No nonzero same-H spectral window can live strictly below the half-rate floor. -/
theorem no_sameH_subgap_transfer_window
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (time : WilsonPhysicalTimeStep) :
    ¬ Nonempty (SameHSubgapTransferWindow weld time) := by
  rintro ⟨window⟩
  have hAbove :
      (1 / 2 : ℝ) < Real.exp (-time.step * window.energyCeiling) :=
    time.transfer_above_half_of_energy_below_massFloor
      window.energyCeiling window.energyBelowFloor
  have hZero :=
    weld.strict_above_half_spectral_window_zero
      window.projection
      (Real.exp (-time.step * window.energyCeiling))
      hAbove window.transferLowerBound
  exact window.projectionNonzero hZero

end RequestProject.YangMills
