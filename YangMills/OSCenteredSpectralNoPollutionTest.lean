import Mathlib
import YangMills.OSCenteredSpectralNoPollution

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (P : vacuumOrthogonalSubmodule weld.vacuum →L[ℝ]
      vacuumOrthogonalSubmodule weld.vacuum)
    (λ : ℝ) (hλ : (1 / 2 : ℝ) < λ)
    (hLower : SpectralWindowLowerBound weld.excitationTransfer P λ) :
    P = 0 :=
  weld.strict_above_half_spectral_window_zero P λ hλ hLower

end RequestProject.YangMills
