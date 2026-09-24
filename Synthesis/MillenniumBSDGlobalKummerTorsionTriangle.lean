import Synthesis.MillenniumBSDGlobalKummerOrdinaryHom
import Mathlib.Tactic

/-!
# Rational two-torsion triangle on the actual global elliptic group

The three finite rational two-torsion points are evaluated inside the actual
E(Q) group, and their Kummer multiplication table is matched to the literal
global total Kummer map.  This pays the exceptional-exceptional cases of the
global homomorphism; only translation of a generic affine point by one of
these torsion points remains.
-/

namespace Synthesis.Millennium.BSD

def rationalZeroTorsionPoint : RationalProjectivePoint :=
  .affine 0 0 (by norm_num)

def rationalOneTorsionPoint : RationalProjectivePoint :=
  .affine 1 0 (by norm_num)

def rationalMinusOneTorsionPoint : RationalProjectivePoint :=
  .affine (-1) 0 (by norm_num)

@[simp] theorem totalGlobalKummer_rationalZeroTorsion :
    totalGlobalKummer rationalZeroTorsionPoint
      = torsionKummer .zero := by
  simp [rationalZeroTorsionPoint, totalGlobalKummer]

@[simp] theorem totalGlobalKummer_rationalOneTorsion :
    totalGlobalKummer rationalOneTorsionPoint
      = torsionKummer .one := by
  simp [rationalOneTorsionPoint, totalGlobalKummer]

@[simp] theorem totalGlobalKummer_rationalMinusOneTorsion :
    totalGlobalKummer rationalMinusOneTorsionPoint
      = torsionKummer .negOne := by
  simp [rationalMinusOneTorsionPoint, totalGlobalKummer,
    ordinaryKummer, minusOnePoint, negOneNZ, negTwoNZ]

theorem rational_zero_add_one_torsion :
    rationalZeroTorsionPoint + rationalOneTorsionPoint
      = rationalMinusOneTorsionPoint := by
  rw [show rationalZeroTorsionPoint =
      (.affine 0 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [show rationalOneTorsionPoint =
      (.affine 1 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [rationalProjective_secant_add
      (by norm_num) (by norm_num) (by norm_num : (0 : ℚ) ≠ 1)]
  simp [rationalMinusOneTorsionPoint, rationalSecantSumX,
    rationalSecantSlope, rationalSecantSumY]

theorem rational_zero_add_minusOne_torsion :
    rationalZeroTorsionPoint + rationalMinusOneTorsionPoint
      = rationalOneTorsionPoint := by
  rw [show rationalZeroTorsionPoint =
      (.affine 0 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [show rationalMinusOneTorsionPoint =
      (.affine (-1) 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [rationalProjective_secant_add
      (by norm_num) (by norm_num) (by norm_num : (0 : ℚ) ≠ -1)]
  simp [rationalOneTorsionPoint, rationalSecantSumX,
    rationalSecantSlope, rationalSecantSumY]

theorem rational_one_add_minusOne_torsion :
    rationalOneTorsionPoint + rationalMinusOneTorsionPoint
      = rationalZeroTorsionPoint := by
  rw [show rationalOneTorsionPoint =
      (.affine 1 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [show rationalMinusOneTorsionPoint =
      (.affine (-1) 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [rationalProjective_secant_add
      (by norm_num) (by norm_num) (by norm_num : (1 : ℚ) ≠ -1)]
  simp [rationalZeroTorsionPoint, rationalSecantSumX,
    rationalSecantSlope, rationalSecantSumY]

theorem totalGlobalKummer_zero_add_one_torsion :
    totalGlobalKummer
      (rationalZeroTorsionPoint + rationalOneTorsionPoint)
      =
    totalGlobalKummer rationalZeroTorsionPoint
      * totalGlobalKummer rationalOneTorsionPoint := by
  rw [rational_zero_add_one_torsion]
  simp only [totalGlobalKummer_rationalZeroTorsion,
    totalGlobalKummer_rationalOneTorsion,
    totalGlobalKummer_rationalMinusOneTorsion]
  exact rationalTorsionKummer_zero_mul_one.symm

theorem totalGlobalKummer_zero_add_minusOne_torsion :
    totalGlobalKummer
      (rationalZeroTorsionPoint + rationalMinusOneTorsionPoint)
      =
    totalGlobalKummer rationalZeroTorsionPoint
      * totalGlobalKummer rationalMinusOneTorsionPoint := by
  rw [rational_zero_add_minusOne_torsion]
  simp only [totalGlobalKummer_rationalZeroTorsion,
    totalGlobalKummer_rationalOneTorsion,
    totalGlobalKummer_rationalMinusOneTorsion]
  exact rationalTorsionKummer_zero_mul_negOne.symm

theorem totalGlobalKummer_one_add_minusOne_torsion :
    totalGlobalKummer
      (rationalOneTorsionPoint + rationalMinusOneTorsionPoint)
      =
    totalGlobalKummer rationalOneTorsionPoint
      * totalGlobalKummer rationalMinusOneTorsionPoint := by
  rw [rational_one_add_minusOne_torsion]
  simp only [totalGlobalKummer_rationalZeroTorsion,
    totalGlobalKummer_rationalOneTorsion,
    totalGlobalKummer_rationalMinusOneTorsion]
  exact rationalTorsionKummer_one_mul_negOne.symm

end Synthesis.Millennium.BSD
