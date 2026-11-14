import Mathlib
import YangMills.SameHSubgapSpectralWindow

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (time : WilsonPhysicalTimeStep) :
    ¬ Nonempty (SameHSubgapTransferWindow weld time) :=
  no_sameH_subgap_transfer_window weld time

end RequestProject.YangMills
