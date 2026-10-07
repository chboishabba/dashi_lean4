import Mathlib
import YangMills.LiteralSU2CompactQuaternionHaar

namespace RequestProject.YangMills

example : CompactSpace SU2CompactQuaternion := inferInstance
example : IsTopologicalGroup SU2CompactQuaternion := inferInstance

example : SU2PlaquetteHolonomy ≃* SU2CompactQuaternion :=
  literalSU2QuaternionGroupEquiv

example :
    MeasureTheory.Measure.map (fun U : SU2PlaquetteHolonomy => U⁻¹)
      (((literalSU2OneLinkHaar : MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
        MeasureTheory.Measure SU2PlaquetteHolonomy))
    =
      (((literalSU2OneLinkHaar : MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
        MeasureTheory.Measure SU2PlaquetteHolonomy) :=
  literal_su2_one_link_haar_inversion_invariant

end RequestProject.YangMills
