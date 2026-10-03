import Mathlib
import YangMills.ProjectiveCylinderMeasure

open MeasureTheory

namespace RequestProject.YangMills

example
    {ι : Type*} {α : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)]
    (producer : ProbabilityProjectiveCylinderExtensionProducer α) :
    IsProjectiveLimit producer.globalMeasure producer.family.measureFamily :=
  producer.isProjectiveLimit_globalMeasure

end RequestProject.YangMills
