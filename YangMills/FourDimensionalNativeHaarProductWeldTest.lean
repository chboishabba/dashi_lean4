import Mathlib
import YangMills.FourDimensionalNativeHaarProductWeld
import YangMills.FourDimensionalFlatHaarReflectionIndex

namespace RequestProject.YangMills

/-!
Compile probes for Block A's final one-link Haar leaves.

These examples intentionally name the concrete theorems required by the
max-cut.  Before their implementation this file does not elaborate; after the
implementation it becomes a minimal regression surface for A1/A2.
-/

example
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    CompactGroupNormalizedHaarLeftInvariant G :=
  compact_group_native_haar_left_invariant G

example
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    MeasureTheory.Measure.IsMulRightInvariant
      (((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G)) :=
  compact_group_native_haar_right_invariant G

example
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    CompactGroupNormalizedHaarInversionInvariant G :=
  compact_group_native_haar_inversion_invariant G

end RequestProject.YangMills
