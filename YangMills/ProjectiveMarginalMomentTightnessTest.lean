import Mathlib
import YangMills.ProjectiveMarginalMomentTightness

namespace RequestProject.YangMills

example
    (producer : RealMarginalMomentTightnessProducer) :
    RealProjectiveMarginalTightnessProducer :=
  producer.toTightnessProducer

end RequestProject.YangMills
