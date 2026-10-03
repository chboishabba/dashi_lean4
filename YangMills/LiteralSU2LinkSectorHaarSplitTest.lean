import Mathlib
import YangMills.LiteralSU2LinkSectorHaarSplit

namespace RequestProject.YangMills

example (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (su2LiteralSectorAssemble n)
      (literalSU2LinkSectorHaar n)
    =
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :=
  literal_su2_link_sector_haar_split n

end RequestProject.YangMills
