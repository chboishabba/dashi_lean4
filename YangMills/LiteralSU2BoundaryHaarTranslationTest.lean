import YangMills.LiteralSU2BoundaryHaarTranslation

open MeasureTheory

namespace RequestProject.YangMills

example (g : SU2PlaquetteHolonomy) :
    Measure.map (fun U : SU2PlaquetteHolonomy => U * g)
      (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
        Measure SU2PlaquetteHolonomy)) =
      (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
        Measure SU2PlaquetteHolonomy) :=
  literal_su2_one_link_haar_mul_right_invariant g

example
    (n : ℕ) [NeZero n]
    (g : SU2UpperBoundaryTemporalLinks n) :
    Measure.map (fun b : SU2UpperBoundaryTemporalLinks n => fun p => b p * g p)
      (literalSU2UpperBoundaryTemporalHaar n) =
      literalSU2UpperBoundaryTemporalHaar n :=
  literal_su2_upper_boundary_haar_mul_right_invariant n g

end RequestProject.YangMills
