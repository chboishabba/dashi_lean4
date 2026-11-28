import Mathlib
import YangMills.LiteralSU2LinkHaarReflection

namespace RequestProject.YangMills

example (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure (SU2TorusLinks L) :=
  literalSU2LinkHaar L

example (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@su2EvenTimeReflectLinks n)
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))))
    =
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))) :=
  literal_su2_link_haar_reflection_invariant n

end RequestProject.YangMills
