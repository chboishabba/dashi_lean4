import Mathlib
import YangMills.CMP119SelectedCompleteFunctionalRP

namespace RequestProject.YangMills

example
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) (β : ℝ) (hβ : 0 ≤ β) :
    ReflectionPositiveKernel (su2WilsonCrossingPlaneKernel crossings β) :=
  su2_wilson_crossing_plane_functional_rp crossings β hβ

example
    {n : ℕ} [NeZero n]
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) (β : ℝ) (hβ : 0 ≤ β)
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n
      (SU2CrossingBoundary P)) :
    ReflectionPositiveKernel
      (fun left right =>
        su2WilsonCrossingPlaneKernel crossings β left right *
          cut.sourceKernel left right) :=
  cmp119_selected_complete_crossing_functional_rp
    crossings β hβ cut

end RequestProject.YangMills
