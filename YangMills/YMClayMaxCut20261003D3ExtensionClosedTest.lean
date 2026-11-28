import Mathlib
import YangMills.YMClayMaxCut20261003D3ExtensionClosed

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

example
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) :
    ym_20261003_d3_ext_measure sequence |>.map (frestrictLe n) =
      (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) :=
  ym_20261003_d3_ext_prefix sequence n

end RequestProject.YangMills
