import Synthesis.MillenniumBSDCMQ2Hensel3705CandidateExact
import Mathlib.Tactic

/-!
BSD K1 source-point continuation for the original
E : y² = x³ − x over Q₂, at actual x=39.

The owning Hensel candidate produces z²=3705. This file uses no
replacement curve or finite-only ZMod approximation:
  39³−39=16·3705 and y=4z.
The original Q₂ root lemma is still source-written and must pass
the pinned Lean 4.28 / Mathlib kernel; so this downstream theorem
is also a candidate, NOT a Kummer/Selmer/Sha closure.
-/

noncomputable section
namespace Synthesis.Millennium.BSD

/-- An actual Q₂-valued affine point of the original CM curve
    E : y²=x³−x, obtained from the original Hensel root. -/
theorem cmActualCurveQ2PointAt39 :
    ∃ y : ℚ_[2], y ^ 2 = (39 : ℚ_[2]) ^ 3 - 39 := by
  obtain ⟨z, hz⟩ := cmQ2SquareRoot3705
  refine ⟨4*z, ?_⟩
  calc
    (4*z)^2 = 16*z^2 := by ring
    _ = 16*(3705 : ℚ_[2]) := by rw [hz]
    _ = (39 : ℚ_[2])^3 - 39 := by norm_num

/-- The same original integer x=39 produces a real local point,
    separately from its Q₂ point. -/
theorem cmActualCurveRealPointAt39 :
    ∃ y : ℝ, y ^ 2 = (39 : ℝ) ^ 3 - 39 := by
  refine ⟨Real.sqrt (39^3 - 39 : ℝ), ?_⟩
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 39^3 - 39)]

/-- Exact source identity that the dyadic root has no hidden
    denominator or replacement cubic. -/
theorem cmActualCurve39Numerator :
    (39:ℤ) * (39-1) * (39+1) = 16*3705 := by norm_num

end Synthesis.Millennium.BSD
