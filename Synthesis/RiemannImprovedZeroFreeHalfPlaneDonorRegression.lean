import Synthesis.RiemannImprovedZeroFreeHalfPlaneDonorAudit

namespace Synthesis

example : improvedZeroFreeSafeBeta = (437479 : ℝ) / 500000 := by
  rfl

example : improvedZeroFreeSafeHorizontalCap = (187479 : ℝ) / 500000 := by
  exact improvedZeroFreeSafeHorizontalCap_eq

example : improvedZeroFreeSafeBeta < (7 : ℝ) / 8 := by
  exact improvedZeroFreeSafeBeta_lt_sevenEighths

example : improvedZeroFreeSafeHorizontalCap < (3 : ℝ) / 8 := by
  exact improvedZeroFreeSafeHorizontalCap_lt_threeEighths

example (A : ℝ) (hA : A ≤ improvedZeroFreeSafeHorizontalCap) : A < (3 : ℝ) / 8 := by
  exact targetDisplacement_lt_threeEighths hA

example (B signedCredit : ℝ) (hcredit : 0 < signedCredit) :
    signedHybridStep B signedCredit < B := by
  exact signedHybridStep_lt_positiveStep hcredit

end Synthesis
