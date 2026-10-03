import Mathlib
import YangMills.CanonicalMarginalMomentSource

open Set MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCanonicalMarginalMomentSource Ω) :
    RealMarginalMomentTightnessProducer :=
  source.toMomentTightnessProducer

end RequestProject.YangMills
