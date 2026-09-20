import Synthesis.MillenniumBSDLocalKummerSecantDispatch
import Mathlib.Tactic

/-!
# Translation by the exceptional rational 2-torsion points

The total Kummer map uses special branches at x=0 and x=1.  To complete
multiplicativity these branches must be handled by actual elliptic addition,
not by pretending the ordinary formula still applies.

For P=(x,y) on y²=x³-x:

* adding T₀=(0,0) gives x(P+T₀) = -1/x;
* adding T₁=(1,0) gives x(P+T₁) = (x+1)/(x-1).

The curve equation proves the two Kummer-coordinate ratios are squares.
Thus translation by T₀ and T₁ multiplies the Kummer class by their exact
special values.
-/

namespace Synthesis.Millennium.BSD

def zeroTorsionPoint
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p :=
  .affine 0 0 (by norm_num)

def oneTorsionPoint
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p :=
  .affine 1 0 (by norm_num)

theorem zeroTorsion_translate_x
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx : x ≠ 0) :
    secantSumX x y 0 0 = -x⁻¹ := by
  unfold secantSumX secantSlope
  field_simp [hx]
  linear_combination -hcurve

theorem oneTorsion_translate_x
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx1 : x ≠ 1) :
    secantSumX x y 1 0 = (x + 1) / (x - 1) := by
  unfold secantSumX secantSlope
  field_simp [sub_ne_zero.mpr hx1]
  linear_combination -hcurve

theorem y_ne_zero_of_x_ne_three_torsion_roots
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    y ≠ 0 := by
  intro hy
  subst y
  have hpoly : x ^ 3 - x = 0 := by
    simpa using hcurve.symm
  have hfac : x * (x - 1) * (x + 1) = 0 := by
    calc
      x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfac with hleft | hplus
  · rcases mul_eq_zero.mp hleft with hx | hxminus
    · exact hx0 hx
    · exact hx1 (sub_eq_zero.mp hxminus)
  · exact hxm1 (by
      have : x = -1 := by linear_combination hplus
      exact this)

theorem zeroTranslate_firstSquareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx : x ≠ 0) :
    padicSquareClassOf p
      ⟨secantSumX x y 0 0,
        by rw [zeroTorsion_translate_x hcurve hx];
           exact neg_ne_zero.mpr (inv_ne_zero hx)⟩
      =
    (localZeroKummer p).1
      * padicSquareClassOf p ⟨x, hx⟩ := by
  rw [zeroTorsion_translate_x hcurve hx]
  let a : NonzeroPadic p :=
    ⟨-x⁻¹, neg_ne_zero.mpr (inv_ne_zero hx)⟩
  let b : NonzeroPadic p :=
    nzPadicMul p
      ⟨(-1 : ℚ_[p]), by norm_num⟩
      ⟨x, hx⟩
  have hab :
      padicSquareClassOf p a =
      padicSquareClassOf p b := by
    apply padicSquareClass_eq_of_product_square
      a.property b.property (by norm_num : (1 : ℚ_[p]) ≠ 0)
    dsimp [a, b, nzPadicMul]
    field_simp [hx]
  calc
    padicSquareClassOf p a
        = padicSquareClassOf p b := hab
    _ = padicSquareClassOf p
          ⟨(-1 : ℚ_[p]), by norm_num⟩
          * padicSquareClassOf p ⟨x, hx⟩ := rfl
    _ = (localZeroKummer p).1
          * padicSquareClassOf p ⟨x, hx⟩ := rfl

theorem zeroTranslate_secondSquareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    padicSquareClassOf p
      ⟨secantSumX x y 0 0 - 1, by
        rw [zeroTorsion_translate_x hcurve hx0]
        intro h
        have : x = -1 := by
          field_simp [hx0] at h
          linear_combination h
        exact hxm1 this⟩
      =
    (localZeroKummer p).2
      * padicSquareClassOf p
          ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
  have hy :=
    y_ne_zero_of_x_ne_three_torsion_roots
      hcurve hx0 hx1 hxm1
  have hxr1 : -x⁻¹ - 1 ≠ 0 := by
    intro h
    have : x = -1 := by
      field_simp [hx0] at h
      linear_combination h
    exact hxm1 this
  let a : NonzeroPadic p := ⟨-x⁻¹ - 1, hxr1⟩
  let b : NonzeroPadic p :=
    nzPadicMul p
      ⟨(-1 : ℚ_[p]), by norm_num⟩
      ⟨x - 1, sub_ne_zero.mpr hx1⟩
  let q : NonzeroPadic p :=
    ⟨y / x, div_ne_zero hy hx0⟩
  have hab :
      padicSquareClassOf p a =
      padicSquareClassOf p b := by
    apply padicSquareClass_eq_of_product_square
      a.property b.property q.property
    dsimp [a, b, q, nzPadicMul]
    field_simp [hx0]
    linear_combination -hcurve
  rw [zeroTorsion_translate_x hcurve hx0]
  calc
    padicSquareClassOf p a = padicSquareClassOf p b := hab
    _ = padicSquareClassOf p
          ⟨(-1 : ℚ_[p]), by norm_num⟩
          * padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl
    _ = (localZeroKummer p).2
          * padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl

theorem oneTranslate_firstSquareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    padicSquareClassOf p
      ⟨secantSumX x y 1 0, by
        rw [oneTorsion_translate_x hcurve hx1]
        exact div_ne_zero
          (by
            intro h
            exact hxm1 (by linear_combination h))
          (sub_ne_zero.mpr hx1)⟩
      =
    (localOneKummer p).1
      * padicSquareClassOf p ⟨x, hx0⟩ := by
  have hy :=
    y_ne_zero_of_x_ne_three_torsion_roots
      hcurve hx0 hx1 hxm1
  let a : NonzeroPadic p :=
    ⟨(x + 1) / (x - 1),
      div_ne_zero
        (by
          intro h
          exact hxm1 (by linear_combination h))
        (sub_ne_zero.mpr hx1)⟩
  let b : NonzeroPadic p := ⟨x, hx0⟩
  let q : NonzeroPadic p :=
    ⟨y / (x - 1),
      div_ne_zero hy (sub_ne_zero.mpr hx1)⟩
  have hab :
      padicSquareClassOf p a =
      padicSquareClassOf p b := by
    apply padicSquareClass_eq_of_product_square
      a.property b.property q.property
    dsimp [a, b, q]
    field_simp [sub_ne_zero.mpr hx1]
    linear_combination -hcurve
  rw [oneTorsion_translate_x hcurve hx1]
  calc
    padicSquareClassOf p a = padicSquareClassOf p b := hab
    _ = (localOneKummer p).1
          * padicSquareClassOf p ⟨x, hx0⟩ := by
      simp [localOneKummer, localRationalClass]

theorem oneTranslate_secondSquareClass
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    padicSquareClassOf p
      ⟨secantSumX x y 1 0 - 1, by
        rw [oneTorsion_translate_x hcurve hx1]
        field_simp [sub_ne_zero.mpr hx1]
        norm_num⟩
      =
    (localOneKummer p).2
      * padicSquareClassOf p
          ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
  let a : NonzeroPadic p :=
    ⟨(x + 1) / (x - 1) - 1, by
      field_simp [sub_ne_zero.mpr hx1]
      norm_num⟩
  let b : NonzeroPadic p :=
    nzPadicMul p
      ⟨(2 : ℚ_[p]), by norm_num⟩
      ⟨x - 1, sub_ne_zero.mpr hx1⟩
  have hab :
      padicSquareClassOf p a =
      padicSquareClassOf p b := by
    apply padicSquareClass_eq_of_product_square
      a.property b.property (by norm_num : (2 : ℚ_[p]) ≠ 0)
    dsimp [a, b, nzPadicMul]
    field_simp [sub_ne_zero.mpr hx1]
    ring
  rw [oneTorsion_translate_x hcurve hx1]
  calc
    padicSquareClassOf p a = padicSquareClassOf p b := hab
    _ = padicSquareClassOf p
          ⟨(2 : ℚ_[p]), by norm_num⟩
          * padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl
    _ = (localOneKummer p).2
          * padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl


theorem totalLocalKummer_add_zeroTorsion_ordinary
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    totalLocalKummer p
      ((.affine x y hcurve : PadicProjectivePoint p)
        + zeroTorsionPoint p)
      =
    totalLocalKummer p (.affine x y hcurve)
      * totalLocalKummer p (zeroTorsionPoint p) := by
  have hxR0 : secantSumX x y 0 0 ≠ 0 := by
    rw [zeroTorsion_translate_x hcurve hx0]
    exact neg_ne_zero.mpr (inv_ne_zero hx0)
  have hxR1 : secantSumX x y 0 0 ≠ 1 := by
    rw [zeroTorsion_translate_x hcurve hx0]
    intro h
    have : x = -1 := by
      field_simp [hx0] at h
      linear_combination h
    exact hxm1 this
  let Pin : OrdinaryPadicKummerPoint p :=
    { x := x
    , y := y
    , onCurve := hcurve
    , x_ne_zero := hx0
    , x_ne_one := hx1 }
  let Pout : OrdinaryPadicKummerPoint p :=
    { x := secantSumX x y 0 0
    , y := secantSumY x y 0 0
    , onCurve := secantSum_onCurve hcurve (by norm_num) hx0
    , x_ne_zero := hxR0
    , x_ne_one := hxR1 }
  rw [show zeroTorsionPoint p =
      (.affine 0 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [padicProjective_secant_add hcurve (by norm_num) hx0]
  change totalLocalKummer p
      (.affine Pout.x Pout.y Pout.onCurve)
      =
    totalLocalKummer p
      (.affine Pin.x Pin.y Pin.onCurve)
      * totalLocalKummer p (.affine 0 0 (by norm_num))
  rw [totalLocalKummer_ordinary Pout,
      totalLocalKummer_ordinary Pin,
      totalLocalKummer_zeroTorsion]
  apply Prod.ext
  · simpa [Pin, Pout, mul_comm] using
      zeroTranslate_firstSquareClass hcurve hx0
  · simpa [Pin, Pout, mul_comm] using
      zeroTranslate_secondSquareClass hcurve hx0 hx1 hxm1

theorem totalLocalKummer_add_oneTorsion_ordinary
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1)
    (hxm1 : x ≠ -1) :
    totalLocalKummer p
      ((.affine x y hcurve : PadicProjectivePoint p)
        + oneTorsionPoint p)
      =
    totalLocalKummer p (.affine x y hcurve)
      * totalLocalKummer p (oneTorsionPoint p) := by
  have hxR0 : secantSumX x y 1 0 ≠ 0 := by
    rw [oneTorsion_translate_x hcurve hx1]
    exact div_ne_zero
      (by
        intro h
        exact hxm1 (by linear_combination h))
      (sub_ne_zero.mpr hx1)
  have hxR1 : secantSumX x y 1 0 ≠ 1 := by
    rw [oneTorsion_translate_x hcurve hx1]
    intro h
    field_simp [sub_ne_zero.mpr hx1] at h
    norm_num at h
  let Pin : OrdinaryPadicKummerPoint p :=
    { x := x
    , y := y
    , onCurve := hcurve
    , x_ne_zero := hx0
    , x_ne_one := hx1 }
  let Pout : OrdinaryPadicKummerPoint p :=
    { x := secantSumX x y 1 0
    , y := secantSumY x y 1 0
    , onCurve := secantSum_onCurve hcurve (by
        exact sub_ne_zero.mpr hx1) 
    , x_ne_zero := hxR0
    , x_ne_one := hxR1 }
  rw [show oneTorsionPoint p =
      (.affine 1 0 (by norm_num) : PadicProjectivePoint p) by rfl]
  rw [padicProjective_secant_add hcurve (by norm_num)
      (sub_ne_zero.mpr hx1)]
  change totalLocalKummer p
      (.affine Pout.x Pout.y Pout.onCurve)
      =
    totalLocalKummer p
      (.affine Pin.x Pin.y Pin.onCurve)
      * totalLocalKummer p (.affine 1 0 (by norm_num))
  rw [totalLocalKummer_ordinary Pout,
      totalLocalKummer_ordinary Pin,
      totalLocalKummer_one]
  apply Prod.ext
  · simpa [Pin, Pout, mul_comm] using
      oneTranslate_firstSquareClass hcurve hx0 hx1 hxm1
  · simpa [Pin, Pout, mul_comm] using
      oneTranslate_secondSquareClass hcurve hx1 hxm1

end Synthesis.Millennium.BSD
