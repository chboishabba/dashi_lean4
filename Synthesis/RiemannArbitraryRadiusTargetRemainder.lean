import Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

/-!
# Arbitrary-radius target-defect remainder

The historical target-defect compiler assumed r <= 1 only at its final line,
where the exact sextic contribution was weakened using r^6 <= r^4.

This module keeps that sextic term.  No upper bound on r is required:

  |D(g,r,a)-r^2 L(g,a)|
    <= r^4 * C4(g,a) + r^6 * C6(g,a),

where

  C4 = 17/24 * (Q4_a Q0_0 + Q0_a Q4_0),
  C6 = 10/24 * Q2_a Q4_0.

This is the correct form for the canonical high taper, whose sample radius
r=t/16 grows while its physical support shrinks like 1/t.
-/

noncomputable section

open scoped Real
open MeasureTheory

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

def defectRemainder4 (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  17 / 24 *
    (absMom4 g a * absMom0 g 0
      + absMom0 g a * absMom4 g 0)

def defectRemainder6 (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  10 / 24 * (absMom2 g a * absMom4 g 0)

theorem defectRemainder4_nonneg (g : ℝ → ℝ) (a : ℝ) :
    0 <= defectRemainder4 g a := by
  unfold defectRemainder4
  positivity

theorem defectRemainder6_nonneg (g : ℝ → ℝ) (a : ℝ) :
    0 <= defectRemainder6 g a := by
  unfold defectRemainder6
  positivity

theorem det_remainder_bound_arbitrary_radius
    {A1 A2 B1 B2 Ma Na M0 N0 Q0a Q2a Q4a Q00 Q40 r : ℝ}
    (hr0 : 0 <= r)
    (hA1 : |A1 - (Ma - r ^ 2 / 2 * Na)| <= r ^ 4 / 24 * Q4a)
    (hA2 : |A2 - (Ma - (2 * r) ^ 2 / 2 * Na)|
      <= (2 * r) ^ 4 / 24 * Q4a)
    (hB1 : |B1 - (M0 - r ^ 2 / 2 * N0)| <= r ^ 4 / 24 * Q40)
    (hB2 : |B2 - (M0 - (2 * r) ^ 2 / 2 * N0)|
      <= (2 * r) ^ 4 / 24 * Q40)
    (hB1' : |B1| <= Q00) (hB2' : |B2| <= Q00)
    (hMa : |Ma| <= Q0a) (hNa : |Na| <= Q2a)
    (hQ0a : 0 <= Q0a) (hQ2a : 0 <= Q2a)
    (hQ4a : 0 <= Q4a) (hQ40 : 0 <= Q40) :
    |A1 * B2 - A2 * B1
        - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))|
      <=
    r ^ 4 * (17 / 24 * (Q4a * Q00 + Q0a * Q40))
      + r ^ 6 * (10 / 24 * (Q2a * Q40)) := by
  have hPa1B :
      |Ma - r ^ 2 / 2 * Na| <= Q0a + r ^ 2 / 2 * Q2a := by
    have hstep :
        |Ma - r ^ 2 / 2 * Na|
          <= |Ma| + |r ^ 2 / 2 * Na| := abs_sub _ _
    have hmul :
        |r ^ 2 / 2 * Na| = r ^ 2 / 2 * |Na| := by
      rw [abs_mul, abs_of_nonneg
        (by positivity : (0 : ℝ) <= r ^ 2 / 2)]
    have hle :
        r ^ 2 / 2 * |Na| <= r ^ 2 / 2 * Q2a :=
      mul_le_mul_of_nonneg_left hNa (by positivity)
    linarith

  have hPa2B :
      |Ma - (2 * r) ^ 2 / 2 * Na|
        <= Q0a + (2 * r) ^ 2 / 2 * Q2a := by
    have hstep :
        |Ma - (2 * r) ^ 2 / 2 * Na|
          <= |Ma| + |(2 * r) ^ 2 / 2 * Na| := abs_sub _ _
    have hmul :
        |(2 * r) ^ 2 / 2 * Na|
          = (2 * r) ^ 2 / 2 * |Na| := by
      rw [abs_mul, abs_of_nonneg
        (by positivity : (0 : ℝ) <= (2 * r) ^ 2 / 2)]
    have hle :
        (2 * r) ^ 2 / 2 * |Na|
          <= (2 * r) ^ 2 / 2 * Q2a :=
      mul_le_mul_of_nonneg_left hNa (by positivity)
    linarith

  have key1 :
      |A1 * B2
        - (Ma - r ^ 2 / 2 * Na)
          * (M0 - (2 * r) ^ 2 / 2 * N0)|
      <=
      (r ^ 4 / 24 * Q4a) * Q00
        + (Q0a + r ^ 2 / 2 * Q2a)
          * ((2 * r) ^ 4 / 24 * Q40) :=
    abs_mul_sub_mul_le hA1 hB2' hPa1B hB2
      (add_nonneg hQ0a
        (mul_nonneg (by positivity) hQ2a))
      (mul_nonneg (by positivity) hQ4a)

  have key2 :
      |A2 * B1
        - (Ma - (2 * r) ^ 2 / 2 * Na)
          * (M0 - r ^ 2 / 2 * N0)|
      <=
      ((2 * r) ^ 4 / 24 * Q4a) * Q00
        + (Q0a + (2 * r) ^ 2 / 2 * Q2a)
          * (r ^ 4 / 24 * Q40) :=
    abs_mul_sub_mul_le hA2 hB1' hPa2B hB1
      (add_nonneg hQ0a
        (mul_nonneg (by positivity) hQ2a))
      (mul_nonneg (by positivity) hQ4a)

  have hsplit :
      A1 * B2 - A2 * B1
          - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))
      =
      (A1 * B2
        - (Ma - r ^ 2 / 2 * Na)
          * (M0 - (2 * r) ^ 2 / 2 * N0))
      -
      (A2 * B1
        - (Ma - (2 * r) ^ 2 / 2 * Na)
          * (M0 - r ^ 2 / 2 * N0)) := by
    ring

  have htri :
      |A1 * B2 - A2 * B1
          - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))|
      <=
      |A1 * B2
        - (Ma - r ^ 2 / 2 * Na)
          * (M0 - (2 * r) ^ 2 / 2 * N0)|
      +
      |A2 * B1
        - (Ma - (2 * r) ^ 2 / 2 * Na)
          * (M0 - r ^ 2 / 2 * N0)| := by
    rw [hsplit]
    exact abs_sub _ _

  calc
    |A1 * B2 - A2 * B1
        - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))|
      <= _ := htri
    _ <=
      r ^ 4 * (17 / 24 * (Q4a * Q00 + Q0a * Q40))
        + r ^ 6 * (10 / 24 * (Q2a * Q40)) := by
      nlinarith [key1, key2]

theorem abs_heightDefect_sub_leading_le_arbitrary_radius
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (a r : ℝ)
    (hr0 : 0 <= r) :
    |heightDefect g r a 0 - r ^ 2 * targetLeadingCoeff g a|
      <=
    r ^ 4 * defectRemainder4 g a
      + r ^ 6 * defectRemainder6 g a := by
  unfold defectRemainder4 defectRemainder6
  exact det_remainder_bound_arbitrary_radius hr0
    (abs_evenResp_sub_quadratic_le hg hgc a r)
    (abs_evenResp_sub_quadratic_le hg hgc a (2 * r))
    (abs_evenResp_sub_quadratic_le hg hgc 0 r)
    (abs_evenResp_sub_quadratic_le hg hgc 0 (2 * r))
    (abs_evenResp_le hg hgc 0 r)
    (abs_evenResp_le hg hgc 0 (2 * r))
    (abs_coshMoment_le hg hgc a)
    (abs_sqCoshMoment_le hg hgc a)
    (absMom0_nonneg g a)
    (absMom2_nonneg g a)
    (absMom4_nonneg g a)
    (absMom4_nonneg g 0)

def zeroRemainder4 (g : ℝ → ℝ) (rho : Zeros) : ℝ :=
  2 * ((zetaZeroConfig).mult rho : ℝ)
    * defectRemainder4 g (heightOf rho)

def zeroRemainder6 (g : ℝ → ℝ) (rho : Zeros) : ℝ :=
  2 * ((zetaZeroConfig).mult rho : ℝ)
    * defectRemainder6 g (heightOf rho)

theorem zeroRemainder4_nonneg (g : ℝ → ℝ) (rho : Zeros) :
    0 <= zeroRemainder4 g rho := by
  unfold zeroRemainder4
  positivity

theorem zeroRemainder6_nonneg (g : ℝ → ℝ) (rho : Zeros) :
    0 <= zeroRemainder6 g rho := by
  unfold zeroRemainder6
  positivity

theorem abs_zeroHeightDefect_sub_leading_le_arbitrary_radius
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (rho : Zeros)
    (r : ℝ)
    (hr0 : 0 <= r) :
    |zeroHeightDefect g r rho
        - r ^ 2 * zeroLeadingCoeff g rho|
      <=
    r ^ 4 * zeroRemainder4 g rho
      + r ^ 6 * zeroRemainder6 g rho := by
  let m : ℝ := ((zetaZeroConfig).mult rho : ℝ)
  have hm0 : 0 <= m := by
    dsimp [m]
    positivity
  have hbase :=
    abs_heightDefect_sub_leading_le_arbitrary_radius
      hg hgc (heightOf rho) r hr0
  have hEq :
      zeroHeightDefect g r rho
          - r ^ 2 * zeroLeadingCoeff g rho
      =
      2 * m *
        (heightDefect g r (heightOf rho) 0
          - r ^ 2 * targetLeadingCoeff g (heightOf rho)) := by
    unfold zeroHeightDefect zeroLeadingCoeff
    dsimp [m]
    ring
  rw [hEq, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) hm0)]
  unfold zeroRemainder4 zeroRemainder6
  dsimp [m]
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase
      (mul_nonneg (by norm_num : (0 : ℝ) <= 2) hm0)
  nlinarith

theorem reflectionPair_gate_of_arbitraryRadius_coefficientComparison
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (rho : Zeros)
    (r E : ℝ)
    (hr0 : 0 < r)
    (hcmp :
      E
        + 2 * r ^ 2 * zeroRemainder4 g rho
        + 2 * r ^ 4 * zeroRemainder6 g rho
      < 2 * zeroLeadingCoeff g rho) :
    r ^ 2 * E < 2 * zeroHeightDefect g r rho := by
  have hbase :=
    abs_zeroHeightDefect_sub_leading_le_arbitrary_radius
      hg hgc rho r hr0.le
  have hlow :
      r ^ 2 * zeroLeadingCoeff g rho
        - (r ^ 4 * zeroRemainder4 g rho
          + r ^ 6 * zeroRemainder6 g rho)
      <= zeroHeightDefect g r rho := by
    have habs := abs_le.1 hbase
    linarith [habs.1]
  have hr2 : 0 < r ^ 2 := by positivity
  nlinarith [hcmp, hlow, hr2]

end Synthesis
