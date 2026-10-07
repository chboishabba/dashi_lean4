import Mathlib
import YangMills.LiteralSU2ProductHaar

open MeasureTheory

namespace RequestProject.YangMills

example (L : ℕ) [NeZero L] :
    ProbabilityMeasure (SU2TorusLinks L) :=
  literalSU2ProductLinkHaar L

example (L : ℕ) [NeZero L] :
    (((literalSU2ProductLinkHaar L : ProbabilityMeasure (SU2TorusLinks L)) :
      Measure (SU2TorusLinks L))) =
      Measure.pi (fun _ : SU2TorusSite L =>
        Measure.pi (fun _ : Fin 4 =>
          (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
            Measure SU2PlaquetteHolonomy)))) := by
  rfl

end RequestProject.YangMills
