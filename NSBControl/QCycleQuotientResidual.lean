import Mathlib.Tactic

namespace NSBControl
namespace QCycleQuotientResidual

theorem threePositionProduction_collect
    (wk wp wq X Y Z Z2 : ℝ)
    (hBase : X + Y + Z = 0)
    (hQ : Z + X + Z2 = 0) :
    ((wk - wq) * X + (wp - wq) * Y) +
      ((wq - wp) * Z + (wk - wp) * X) +
      ((wp - wk) * Z2 + (wq - wk) * Z)
      =
      3 * ((wk - wp) * X + (wq - wp) * Z) := by
  have hY : Y = -(X + Z) := by linarith
  have hZ2 : Z2 = -(Z + X) := by linarith
  rw [hY, hZ2]
  ring

theorem factorTwentySeven_to_factorNine
    (D B P Q : ℝ)
    (hResidual : 3 * D = 27 * B - 2 * P)
    (hCycle : P = 3 * Q) :
    D = 9 * B - 2 * Q := by
  rw [hCycle] at hResidual
  linarith

theorem separatedCancellation_iff_quotientBalance
    (D B Q : ℝ)
    (hNormal : D = 9 * B - 2 * Q) :
    D = 0 ↔ 2 * Q = 9 * B := by
  constructor <;> intro h
  · linarith
  · linarith

end QCycleQuotientResidual
end NSBControl
