import Synthesis.RiemannImprovedZeroFreeG21UniformGap

namespace Synthesis

example : improvedZeroFreeUniformPoleGap = (62521 : ℝ) / 500000 := by
  exact improvedZeroFreeUniformPoleGap_eq

example : (1 : ℝ) / 8 < improvedZeroFreeUniformPoleGap := by
  exact oneEighth_lt_improvedZeroFreeUniformPoleGap

example {a : ℝ} (ha : a ≤ improvedZeroFreeSafeHorizontalCap) :
    improvedZeroFreeUniformPoleGap ≤ (1 : ℝ) / 2 - a := by
  exact improvedZeroFree_uniformPoleSeparation ha

end Synthesis
