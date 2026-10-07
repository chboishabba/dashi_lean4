import Mathlib
import YangMills.CMP119SelectedExactComponentReflection

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n] {X : Type*}
    {sector : CMP119SelectedSectorComponents n}
    (realization : CMP119SelectedSectorExactFunctionalRealization sector X)
    (c : sector.Component) :
    ReflectionPositiveKernel (realization.actualKernel c) :=
  realization.actual_component_rp c

example
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  cut.source_kernel_rp

end RequestProject.YangMills
