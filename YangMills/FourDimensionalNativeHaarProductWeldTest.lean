import Mathlib
import YangMills.FourDimensionalNativeHaarProductWeld
import YangMills.FourDimensionalFlatHaarReflectionIndex
import YangMills.FourDimensionalNativeHaarReflectionTransport

namespace RequestProject.YangMills

/-!
Compile probes for Block A's final Haar leaves.

The first three examples are one-link regression surfaces.  The last one is
the actual whole-link result required by the Wilson OS2 assembly.
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

example
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    FourDimensionalNativeHaarReflectionInvariant G n :=
  four_dimensional_native_haar_reflection_invariant_closed G n

end RequestProject.YangMills
