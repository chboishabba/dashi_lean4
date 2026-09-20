import Synthesis.MillenniumBSDLocalKummerTorsionTranslate
import Mathlib.Tactic

/-!
# The local rational two-torsion triangle and its Kummer multiplication table

The exceptional points on E : y²=x³-x are

  T₀=(0,0), T₁=(1,0), T₋₁=(-1,0).

Their actual elliptic additions form the expected Klein four group.  We prove
these identities through the already-established secant dispatch, then prove
the corresponding total Kummer products using the literal square-class
quotients.
-/

namespace Synthesis.Millennium.BSD

def minusOneTorsionPoint
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p :=
  .affine (-1) 0 (by norm_num)

def localMinusOneKummer
    (p : ℕ) [Fact p.Prime] :
    PadicSquareClass p × PadicSquareClass p :=
  (localRationalClass p negOneNZ,
   localRationalClass p negTwoNZ)

theorem totalLocalKummer_minusOne
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p (minusOneTorsionPoint p)
      =
    localMinusOneKummer p := by
  simp [minusOneTorsionPoint, totalLocalKummer,
    localMinusOneKummer, ordinaryPadicKummer,
    localRationalClass, negOneNZ, negTwoNZ]

theorem zero_add_one_torsion
    (p : ℕ) [Fact p.Prime] :
    zeroTorsionPoint p + oneTorsionPoint p
      =
    minusOneTorsionPoint p := by
  rw [show zeroTorsionPoint p =
      (.affine 0 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [show oneTorsionPoint p =
      (.affine 1 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [padicProjective_secant_add
      (by norm_num) (by norm_num)
      (by norm_num : (0 : ℚ_[p]) ≠ 1)]
  simp [minusOneTorsionPoint, secantSumX, secantSlope,
    secantSumY]

theorem zero_add_minusOne_torsion
    (p : ℕ) [Fact p.Prime] :
    zeroTorsionPoint p + minusOneTorsionPoint p
      =
    oneTorsionPoint p := by
  rw [show zeroTorsionPoint p =
      (.affine 0 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [show minusOneTorsionPoint p =
      (.affine (-1) 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [padicProjective_secant_add
      (by norm_num) (by norm_num)
      (by norm_num : (0 : ℚ_[p]) ≠ -1)]
  simp [oneTorsionPoint, secantSumX, secantSlope,
    secantSumY]

theorem one_add_minusOne_torsion
    (p : ℕ) [Fact p.Prime] :
    oneTorsionPoint p + minusOneTorsionPoint p
      =
    zeroTorsionPoint p := by
  rw [show oneTorsionPoint p =
      (.affine 1 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [show minusOneTorsionPoint p =
      (.affine (-1) 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [padicProjective_secant_add
      (by norm_num) (by norm_num)
      (by norm_num : (1 : ℚ_[p]) ≠ -1)]
  simp [zeroTorsionPoint, secantSumX, secantSlope,
    secantSumY]

theorem rationalTorsionKummer_zero_mul_one :
    torsionKummer .zero * torsionKummer .one
      =
    torsionKummer .negOne := by
  apply Prod.ext
  · apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    norm_num [torsionKummer, nzRatMul,
      negOneNZ, oneNZ]
  · apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    norm_num [torsionKummer, nzRatMul,
      negOneNZ, twoNZ, negTwoNZ]

theorem rationalTorsionKummer_zero_mul_negOne :
    torsionKummer .zero * torsionKummer .negOne
      =
    torsionKummer .one := by
  apply Prod.ext
  · apply Quotient.sound
    refine ⟨negOneNZ, oneNZ, ?_⟩
    norm_num [torsionKummer, nzRatMul,
      negOneNZ, oneNZ]
  · apply Quotient.sound
    refine ⟨negTwoNZ, twoNZ, ?_⟩
    norm_num [torsionKummer, nzRatMul,
      negOneNZ, negTwoNZ, twoNZ]

theorem rationalTorsionKummer_one_mul_negOne :
    torsionKummer .one * torsionKummer .negOne
      =
    torsionKummer .zero := by
  apply Prod.ext
  · simp [torsionKummer]
  · apply Quotient.sound
    refine ⟨negTwoNZ, negOneNZ, ?_⟩
    norm_num [torsionKummer, nzRatMul,
      twoNZ, negTwoNZ, negOneNZ]

theorem localize_torsionKummer_zero
    (p : ℕ) [Fact p.Prime] :
    localizeKummerPair p (torsionKummer .zero)
      =
    localZeroKummer p := rfl

theorem localize_torsionKummer_one
    (p : ℕ) [Fact p.Prime] :
    localizeKummerPair p (torsionKummer .one)
      =
    localOneKummer p := rfl

theorem localize_torsionKummer_negOne
    (p : ℕ) [Fact p.Prime] :
    localizeKummerPair p (torsionKummer .negOne)
      =
    localMinusOneKummer p := rfl

theorem localZero_mul_localOne
    (p : ℕ) [Fact p.Prime] :
    localZeroKummer p * localOneKummer p
      =
    localMinusOneKummer p := by
  have h := congrArg
    (localizeKummerPair p)
    rationalTorsionKummer_zero_mul_one
  simpa [localizeKummerPair_eq_hom] using h

theorem localZero_mul_localMinusOne
    (p : ℕ) [Fact p.Prime] :
    localZeroKummer p * localMinusOneKummer p
      =
    localOneKummer p := by
  have h := congrArg
    (localizeKummerPair p)
    rationalTorsionKummer_zero_mul_negOne
  simpa [localizeKummerPair_eq_hom] using h

theorem localOne_mul_localMinusOne
    (p : ℕ) [Fact p.Prime] :
    localOneKummer p * localMinusOneKummer p
      =
    localZeroKummer p := by
  have h := congrArg
    (localizeKummerPair p)
    rationalTorsionKummer_one_mul_negOne
  simpa [localizeKummerPair_eq_hom] using h

theorem totalLocalKummer_zero_add_one_torsion
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p
      (zeroTorsionPoint p + oneTorsionPoint p)
      =
    totalLocalKummer p (zeroTorsionPoint p)
      * totalLocalKummer p (oneTorsionPoint p) := by
  rw [zero_add_one_torsion,
      totalLocalKummer_minusOne]
  rw [show totalLocalKummer p (zeroTorsionPoint p) =
      localZeroKummer p by
        exact totalLocalKummer_zeroTorsion p]
  rw [show totalLocalKummer p (oneTorsionPoint p) =
      localOneKummer p by
        exact totalLocalKummer_one p]
  exact (localZero_mul_localOne p).symm

theorem totalLocalKummer_zero_add_minusOne_torsion
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p
      (zeroTorsionPoint p + minusOneTorsionPoint p)
      =
    totalLocalKummer p (zeroTorsionPoint p)
      * totalLocalKummer p (minusOneTorsionPoint p) := by
  rw [zero_add_minusOne_torsion,
      totalLocalKummer_one,
      totalLocalKummer_minusOne]
  rw [show totalLocalKummer p (zeroTorsionPoint p) =
      localZeroKummer p by exact totalLocalKummer_zeroTorsion p]
  exact (localZero_mul_localMinusOne p).symm

theorem totalLocalKummer_one_add_minusOne_torsion
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p
      (oneTorsionPoint p + minusOneTorsionPoint p)
      =
    totalLocalKummer p (oneTorsionPoint p)
      * totalLocalKummer p (minusOneTorsionPoint p) := by
  rw [one_add_minusOne_torsion,
      totalLocalKummer_zero,
      totalLocalKummer_minusOne]
  rw [show totalLocalKummer p (oneTorsionPoint p) =
      localOneKummer p by exact totalLocalKummer_one p]
  exact (localOne_mul_localMinusOne p).symm

end Synthesis.Millennium.BSD
