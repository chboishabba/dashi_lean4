import Mathlib
import YangMills.OSGramRawDenseSameFamilyWeld

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    DenseRange data.rawVector :=
  data.denseRange_rawVector

example
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    SameHDenseWilsonMixedHalfRateWeld State V weld.data.Hilbert :=
  weld.toDenseSameFamilyWeld

end RequestProject.YangMills
