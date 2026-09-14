import Mathlib

/-
# Exact odd Taylor determinant algebra

Lean port of the newer G21 Agda owner
`RiemannG21OddTaylorDeterminantExact`.

For the scaled cubic odd response

    -6 r N1 + r^3 N3

the two-radius determinant factors exactly.  At r₂ = 2 r₁ the signal is

    -36 r^4 * (N1_a N3_p - N3_a N1_p).

This is pure exact algebra; no analytic remainder estimate is claimed here.
-/

namespace Zeta23Bridge
namespace OddTaylorDeterminant

def square (x : ℝ) : ℝ := x * x
def cube (x : ℝ) : ℝ := x * x * x
def fourth (x : ℝ) : ℝ := square x * square x

def oddCubicScaled (r n1 n3 : ℝ) : ℝ :=
  -(6 * r * n1) + cube r * n3

def oddCubicDeterminant
    (r1 r2 n1a n3a n1p n3p : ℝ) : ℝ :=
  oddCubicScaled r1 n1a n3a * oddCubicScaled r2 n1p n3p
  - oddCubicScaled r2 n1a n3a * oddCubicScaled r1 n1p n3p

def oddMomentPositiveMargin (n1a n3a n1p n3p : ℝ) : ℝ :=
  n1a * n3p - n3a * n1p

theorem oddCubicDeterminantFactorization
    (r1 r2 n1a n3a n1p n3p : ℝ) :
    oddCubicDeterminant r1 r2 n1a n3a n1p n3p
      =
      (6 * r1 * r2 * (square r2 - square r1))
        * (n3a * n1p - n1a * n3p) := by
  unfold oddCubicDeterminant oddCubicScaled cube square
  ring

theorem oddCubicDeterminantAsNegativeMargin
    (r1 r2 n1a n3a n1p n3p : ℝ) :
    oddCubicDeterminant r1 r2 n1a n3a n1p n3p
      =
      -(6 * r1 * r2 * (square r2 - square r1))
        * oddMomentPositiveMargin n1a n3a n1p n3p := by
  unfold oddCubicDeterminant oddCubicScaled oddMomentPositiveMargin cube square
  ring

theorem oddCubicDeterminantDoubleRadius
    (r n1a n3a n1p n3p : ℝ) :
    oddCubicDeterminant r (2 * r) n1a n3a n1p n3p
      =
      -(36 * fourth r) * oddMomentPositiveMargin n1a n3a n1p n3p := by
  unfold oddCubicDeterminant oddCubicScaled oddMomentPositiveMargin fourth cube square
  ring

def linearPartScaled (r n1 : ℝ) : ℝ := -(6 * r * n1)
def cubicPart (r n3 : ℝ) : ℝ := cube r * n3

theorem linearLinearCancellation (r1 r2 n1a n1p : ℝ) :
    linearPartScaled r1 n1a * linearPartScaled r2 n1p
      =
      linearPartScaled r2 n1a * linearPartScaled r1 n1p := by
  unfold linearPartScaled
  ring

theorem cubicCubicCancellation (r1 r2 n3a n3p : ℝ) :
    cubicPart r1 n3a * cubicPart r2 n3p
      =
      cubicPart r2 n3a * cubicPart r1 n3p := by
  unfold cubicPart cube
  ring

end OddTaylorDeterminant
end Zeta23Bridge
