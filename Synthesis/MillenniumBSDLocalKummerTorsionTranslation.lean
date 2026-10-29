import Synthesis.MillenniumBSDLocalKummerSecantDispatch
import Synthesis.MillenniumBSDLocalKummerBoundaryCases
import Mathlib.Tactic

/-!
# Translation by the exceptional rational 2-torsion points

For E : y² = x³ - x and an ordinary affine point P=(x,y), the two exceptional
2-torsion translations have literal x-coordinate formulas

  x(P + (0,0)) = -1/x,
  x(P + (1,0)) = (x+1)/(x-1).

The curve equation
  y² = x(x-1)(x+1)
shows that the two Kummer coordinates transform by the square classes of the
corresponding torsion point.  Hence totalLocalKummer is multiplicative for
translation by (0,0) and (1,0).

These are the exceptional input branches required by the full local Kummer
homomorphism.
-/

namespace Synthesis.Millennium.BSD

def zeroTorsionPoint
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p :=
  .affine 0 0 (by ring)

def oneTorsionPoint
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p :=
  .affine 1 0 (by ring)

@[simp] theorem totalLocalKummer_zeroTorsion
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p (zeroTorsionPoint p) =
      localZeroKummer p := by
  simp [zeroTorsionPoint, totalLocalKummer]

@[simp] theorem totalLocalKummer_oneTorsion
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p (oneTorsionPoint p) =
      localOneKummer p := by
  simp [oneTorsionPoint, totalLocalKummer]

theorem secantSumX_zeroTorsion
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) :
    secantSumX x y 0 0 = -1 / x := by
  unfold secantSumX secantSlope
  field_simp [hx0]
  rw [hcurve]
  ring

theorem secantSumX_oneTorsion
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx1 : x ≠ 1) :
    secantSumX x y 1 0 = (x + 1) / (x - 1) := by
  unfold secantSumX secantSlope
  field_simp [sub_ne_zero.mpr hx1]
  rw [hcurve]
  ring

theorem zeroTorsion_first_squareClass
    {p : ℕ} [Fact p.Prime]
    {x : ℚ_[p]}
    (hx0 : x ≠ 0) :
    padicSquareClassOf p
      ⟨-1 / x, div_ne_zero (by norm_num) hx0⟩
      =
    padicSquareClassOf p ⟨x, hx0⟩
      * localRationalClass p negOneNZ := by
  rw [← padicSquareClassOf_mul]
  apply Quotient.sound
  refine ⟨⟨x, hx0⟩, nzPadicOne p, ?_⟩
  dsimp [nzPadicMul, nzPadicOne, localRationalClass,
    localizeSquareClass, padicSquareClassOf,
    localizeNonzeroRat, negOneNZ]
  field_simp [hx0]
  ring

theorem zeroTorsion_second_squareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxNeg : x ≠ -1) :
    padicSquareClassOf p
      ⟨(-1 / x) - 1, by
        field_simp [hx0]
        exact add_ne_zero.mpr (by
          intro h
          exact hxNeg (by linarith))⟩
      =
    padicSquareClassOf p
      ⟨x - 1, sub_ne_zero.mpr hx1⟩
      * localRationalClass p negOneNZ := by
  rw [← padicSquareClassOf_mul]
  apply Quotient.sound
  let s : ℚ_[p] := x * (x - 1)
  have hs : s ≠ 0 :=
    mul_ne_zero hx0 (sub_ne_zero.mpr hx1)
  refine ⟨⟨s, hs⟩, ⟨y, ?_⟩, ?_⟩
  · intro hy
    rw [hy] at hcurve
    have : x * (x - 1) * (x + 1) = 0 := by
      calc
        x * (x - 1) * (x + 1)
            = x ^ 3 - x := by ring
        _ = 0 := by simpa using hcurve.symm
    rcases mul_eq_zero.mp this with hprod | hplus
    · rcases mul_eq_zero.mp hprod with hx | hxminus
      · exact hx0 hx
      · exact hx1 (sub_eq_zero.mp hxminus)
    · exact hxNeg (by
        have := add_eq_zero.mp hplus
        simpa using this)
  · dsimp [s, nzPadicMul, localRationalClass,
      localizeSquareClass, localizeNonzeroRat, negOneNZ]
    field_simp [hx0]
    rw [hcurve]
    ring

theorem oneTorsion_first_squareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxNeg : x ≠ -1) :
    padicSquareClassOf p
      ⟨(x + 1) / (x - 1), div_ne_zero
        (by exact add_ne_zero.mpr (by
          intro h
          exact hxNeg (by linarith)))
        (sub_ne_zero.mpr hx1)⟩
      =
    padicSquareClassOf p ⟨x, hx0⟩
      * localRationalClass p oneNZ := by
  rw [mul_one]
  apply Quotient.sound
  let s : ℚ_[p] := x * (x - 1)
  have hs : s ≠ 0 :=
    mul_ne_zero hx0 (sub_ne_zero.mpr hx1)
  refine ⟨⟨s, hs⟩, ⟨y, ?_⟩, ?_⟩
  · intro hy
    rw [hy] at hcurve
    have : x * (x - 1) * (x + 1) = 0 := by
      calc
        x * (x - 1) * (x + 1)
            = x ^ 3 - x := by ring
        _ = 0 := by simpa using hcurve.symm
    rcases mul_eq_zero.mp this with hprod | hplus
    · rcases mul_eq_zero.mp hprod with hx | hxminus
      · exact hx0 hx
      · exact hx1 (sub_eq_zero.mp hxminus)
    · exact hxNeg (by
        have := add_eq_zero.mp hplus
        simpa using this)
  · dsimp [s]
    field_simp [hx0, sub_ne_zero.mpr hx1]
    rw [hcurve]
    ring

theorem oneTorsion_second_squareClass
    {p : ℕ} [Fact p.Prime]
    {x : ℚ_[p]}
    (hx1 : x ≠ 1) :
    padicSquareClassOf p
      ⟨((x + 1) / (x - 1)) - 1, by
        field_simp [sub_ne_zero.mpr hx1]
        norm_num⟩
      =
    padicSquareClassOf p
      ⟨x - 1, sub_ne_zero.mpr hx1⟩
      * localRationalClass p twoNZ := by
  rw [← padicSquareClassOf_mul]
  apply Quotient.sound
  refine ⟨⟨x - 1, sub_ne_zero.mpr hx1⟩, nzPadicOne p, ?_⟩
  dsimp [nzPadicMul, nzPadicOne, localRationalClass,
    localizeSquareClass, localizeNonzeroRat, twoNZ]
  field_simp [sub_ne_zero.mpr hx1]
  ring

theorem totalLocalKummer_add_zeroTorsion
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxNeg : x ≠ -1) :
    totalLocalKummer p
      ((.affine x y hcurve : PadicProjectivePoint p)
        + zeroTorsionPoint p)
      =
    totalLocalKummer p (.affine x y hcurve)
      * totalLocalKummer p (zeroTorsionPoint p) := by
  have hx : x ≠ (0 : ℚ_[p]) := hx0
  rw [padicProjective_secant_add hcurve (by ring) hx]
  rw [secantSumX_zeroTorsion hcurve hx0]
  simp [totalLocalKummer, zeroTorsionPoint, hx0, hx1,
    zeroTorsion_first_squareClass hx0,
    zeroTorsion_second_squareClass hcurve hx0 hx1 hxNeg]

theorem totalLocalKummer_add_oneTorsion
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxNeg : x ≠ -1) :
    totalLocalKummer p
      ((.affine x y hcurve : PadicProjectivePoint p)
        + oneTorsionPoint p)
      =
    totalLocalKummer p (.affine x y hcurve)
      * totalLocalKummer p (oneTorsionPoint p) := by
  rw [padicProjective_secant_add hcurve (by ring) hx1]
  rw [secantSumX_oneTorsion hcurve hx1]
  simp [totalLocalKummer, oneTorsionPoint, hx0, hx1,
    oneTorsion_first_squareClass hcurve hx0 hx1 hxNeg,
    oneTorsion_second_squareClass hx1]

end Synthesis.Millennium.BSD
