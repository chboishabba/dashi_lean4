import Synthesis.RiemannReflectionDoubledProjectiveGate
import Synthesis.RiemannConstructedSmoothShortWindowSchur
import Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
import Zeta23Bridge.LiteralWeilNormalizedWindowBounds

/-!
# Explicit leading signal floor on the smooth separated windows

For a smooth Schur certificate with positive polarization lambda, each taper is

  g0 = p + lambda q0,
  g1 = p + lambda q1.

The leading coefficient decomposes exactly into two nonnegative self terms plus
twice the cross covariance.  The unit-mass separated-window theorem gives a
strictly positive explicit floor for that cross covariance.

Hence, for a > 0,

  L(g0,a) >= 2 lambda responseFloor(a, be0, al1),
  L(g1,a) >= 2 lambda responseFloor(a, be0, al2).

This is an actual radius-free lower bound on the target signal coefficient.

For an arbitrary off-line zero, the functional-equation orbit contains a
positive-height representative at the same ordinate and with the same
multiplicity, so no sign convention on height is needed downstream.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilNormalizedWindowBounds
open Zeta23Bridge.LiteralWeilWindowSchurAdmission
open Zeta23Bridge.NormalizedNarrowWindowCertificate

namespace SmoothShortWindowSchurCertificate

variable {sigma rho : Zeros}
variable (C : SmoothShortWindowSchurCertificate sigma rho)

theorem targetLeadingCoeff_ge_floor_zero
    {a : ℝ} (ha : 0 < a) :
    2 * C.lam *
        responseFloor a C.windows.triple.be0 C.windows.triple.al1
      <= targetLeadingCoeff (C.g 0) a := by
  have hp0 :=
    targetLeadingCoeff_nonneg
      C.windows.triple.pNorm.continuous
      C.windows.triple.pNorm.compactSupport
      C.windows.triple.pNorm.nonneg a
  have hq0 :=
    targetLeadingCoeff_nonneg
      C.windows.triple.q0Norm.continuous
      C.windows.triple.q0Norm.compactSupport
      C.windows.triple.q0Norm.nonneg a
  have hcross :=
    covForm_ge_unitMass
      C.windows.triple.pWindow
      C.windows.triple.q0Window
      C.windows.triple.pNorm.unitMass
      C.windows.triple.q0Norm.unitMass
      ha
      C.windows.triple.lowPositive
      C.windows.triple.lowOrdered
      C.windows.triple.lowMiddleSeparated
  have hlam0 : 0 <= C.lam := C.lam_pos.le
  have hlam2 : 0 <= C.lam ^ 2 := sq_nonneg C.lam
  have hcrossScaled :
      2 * C.lam *
          responseFloor a C.windows.triple.be0 C.windows.triple.al1
        <= 2 * C.lam *
          covForm C.windows.triple.p C.windows.triple.q0 a := by
    exact mul_le_mul_of_nonneg_left hcross
      (mul_nonneg (by norm_num) hlam0)

  unfold g
  rw [windowPair_zero]
  rw [targetLeadingCoeff_add_smul
    C.windows.triple.pNorm.continuous
    C.windows.triple.pNorm.compactSupport
    C.windows.triple.q0Norm.continuous
    C.windows.triple.q0Norm.compactSupport]
  nlinarith [hcrossScaled, mul_nonneg hlam2 hq0]

theorem targetLeadingCoeff_ge_floor_one
    {a : ℝ} (ha : 0 < a) :
    2 * C.lam *
        responseFloor a C.windows.triple.be0 C.windows.triple.al2
      <= targetLeadingCoeff (C.g 1) a := by
  have hp0 :=
    targetLeadingCoeff_nonneg
      C.windows.triple.pNorm.continuous
      C.windows.triple.pNorm.compactSupport
      C.windows.triple.pNorm.nonneg a
  have hq1 :=
    targetLeadingCoeff_nonneg
      C.windows.triple.q1Norm.continuous
      C.windows.triple.q1Norm.compactSupport
      C.windows.triple.q1Norm.nonneg a
  have hcross :=
    covForm_ge_unitMass
      C.windows.triple.pWindow
      C.windows.triple.q1Window
      C.windows.triple.pNorm.unitMass
      C.windows.triple.q1Norm.unitMass
      ha
      C.windows.triple.lowPositive
      C.windows.triple.lowOrdered
      (lt_trans C.windows.triple.lowMiddleSeparated
        (lt_of_le_of_lt C.windows.triple.middleOrdered
          C.windows.triple.middleTopSeparated))
  have hlam0 : 0 <= C.lam := C.lam_pos.le
  have hlam2 : 0 <= C.lam ^ 2 := sq_nonneg C.lam
  have hcrossScaled :
      2 * C.lam *
          responseFloor a C.windows.triple.be0 C.windows.triple.al2
        <= 2 * C.lam *
          covForm C.windows.triple.p C.windows.triple.q1 a := by
    exact mul_le_mul_of_nonneg_left hcross
      (mul_nonneg (by norm_num) hlam0)

  unfold g
  rw [windowPair_one]
  rw [targetLeadingCoeff_add_smul
    C.windows.triple.pNorm.continuous
    C.windows.triple.pNorm.compactSupport
    C.windows.triple.q1Norm.continuous
    C.windows.triple.q1Norm.compactSupport]
  nlinarith [hcrossScaled, mul_nonneg hlam2 hq1]

theorem targetLeadingCoeff_floor_zero_pos
    {a : ℝ} (ha : 0 < a) :
    0 <
      2 * C.lam *
        responseFloor a C.windows.triple.be0 C.windows.triple.al1 := by
  have hbe0 : 0 < C.windows.triple.be0 :=
    lt_of_lt_of_le C.windows.triple.lowPositive
      C.windows.triple.lowOrdered
  have hf :=
    responseFloor_pos
      ha hbe0 C.windows.triple.lowMiddleSeparated
  positivity

theorem targetLeadingCoeff_floor_one_pos
    {a : ℝ} (ha : 0 < a) :
    0 <
      2 * C.lam *
        responseFloor a C.windows.triple.be0 C.windows.triple.al2 := by
  have hbe0 : 0 < C.windows.triple.be0 :=
    lt_of_lt_of_le C.windows.triple.lowPositive
      C.windows.triple.lowOrdered
  have hsep :
      C.windows.triple.be0 < C.windows.triple.al2 :=
    lt_trans C.windows.triple.lowMiddleSeparated
      (lt_of_le_of_lt C.windows.triple.middleOrdered
        C.windows.triple.middleTopSeparated)
  have hf := responseFloor_pos ha hbe0 hsep
  positivity

end SmoothShortWindowSchurCertificate

/-- Choose the member of the functional-equation orbit with positive height. -/
def positiveHeightRepresentative (rho : Zeros) : Zeros :=
  if 0 < heightOf rho then rho else reflectZero rho

theorem positiveHeightRepresentative_im (rho : Zeros) :
    ((positiveHeightRepresentative rho : Zeros) : ℂ).im
      = (rho : ℂ).im := by
  unfold positiveHeightRepresentative
  split_ifs with h
  · rfl
  · exact Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.im_reflectZero rho

theorem positiveHeightRepresentative_height_pos
    {rho : Zeros} (hoff : heightOf rho ≠ 0) :
    0 < heightOf (positiveHeightRepresentative rho) := by
  unfold positiveHeightRepresentative
  split_ifs with h
  · exact h
  · rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.heightOf_reflectZero]
    have hle : heightOf rho <= 0 := le_of_not_gt h
    exact neg_pos.mpr (lt_of_le_of_ne hle (Ne.symm hoff))

theorem positiveHeightRepresentative_mult (rho : Zeros) :
    zetaZeroConfig.mult (positiveHeightRepresentative rho)
      = zetaZeroConfig.mult rho := by
  unfold positiveHeightRepresentative
  split_ifs
  · rfl
  · exact reflectZero_mult rho

end Synthesis
