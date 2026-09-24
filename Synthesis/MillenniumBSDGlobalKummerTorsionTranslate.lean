import Synthesis.MillenniumBSDGlobalKummerTorsionTriangle
import Mathlib.Tactic

/-!
# Translation by rational two-torsion in the global Kummer map

For an ordinary rational point P=(x,y), compute addition by T0=(0,0) and
T1=(1,0) on the actual E(Q) group and prove the corresponding Kummer
multiplication laws. Translation by T-1=(-1,0) is already an ordinary secant
case once x is distinct from -1.
-/

namespace Synthesis.Millennium.BSD

theorem rationalZeroTorsion_translate_x
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hx : x ≠ 0) :
    rationalSecantSumX x y 0 0 = -x⁻¹ := by
  unfold rationalSecantSumX rationalSecantSlope
  field_simp [hx]
  linear_combination -h

theorem rationalOneTorsion_translate_x
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hx1 : x ≠ 1) :
    rationalSecantSumX x y 1 0 = (x + 1) / (x - 1) := by
  unfold rationalSecantSumX rationalSecantSlope
  field_simp [sub_ne_zero.mpr hx1]
  linear_combination -h

theorem rational_y_ne_zero_of_x_ne_three_torsion_roots
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    y ≠ 0 := by
  intro hy
  subst y
  have hpoly : x ^ 3 - x = 0 := by simpa using h.symm
  have hfac : x * (x - 1) * (x + 1) = 0 := by
    calc
      x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfac with hleft | hplus
  · rcases mul_eq_zero.mp hleft with hx | hxminus
    · exact hx0 hx
    · exact hx1 (sub_eq_zero.mp hxminus)
  · exact hxm1 (by linear_combination hplus)

theorem rationalZeroTranslate_firstSquareClass
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hx : x ≠ 0) :
    squareClassOf
      ⟨rationalSecantSumX x y 0 0, by
        rw [rationalZeroTorsion_translate_x h hx]
        exact neg_ne_zero.mpr (inv_ne_zero hx)⟩
      =
    (torsionKummer .zero).1 * squareClassOf ⟨x, hx⟩ := by
  rw [rationalZeroTorsion_translate_x h hx]
  let a : NonzeroRat := ⟨-x⁻¹, neg_ne_zero.mpr (inv_ne_zero hx)⟩
  let b : NonzeroRat := nzRatMul negOneNZ ⟨x, hx⟩
  have hab : squareClassOf a = squareClassOf b := by
    apply ratSquareClass_eq_of_product_square
      a.property b.property (by norm_num : (1 : ℚ) ≠ 0)
    dsimp [a, b, nzRatMul, negOneNZ]
    field_simp [hx]
  calc
    squareClassOf a = squareClassOf b := hab
    _ = squareClassOf negOneNZ * squareClassOf ⟨x, hx⟩ := rfl
    _ = (torsionKummer .zero).1 * squareClassOf ⟨x, hx⟩ := rfl

theorem rationalZeroTranslate_secondSquareClass
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    squareClassOf
      ⟨rationalSecantSumX x y 0 0 - 1, by
        rw [rationalZeroTorsion_translate_x h hx0]
        intro heq
        have : x = -1 := by
          field_simp [hx0] at heq
          linear_combination heq
        exact hxm1 this⟩
      =
    (torsionKummer .zero).2 *
      squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
  have hy := rational_y_ne_zero_of_x_ne_three_torsion_roots h hx0 hx1 hxm1
  have hxr1 : -x⁻¹ - 1 ≠ 0 := by
    intro heq
    have : x = -1 := by
      field_simp [hx0] at heq
      linear_combination heq
    exact hxm1 this
  let a : NonzeroRat := ⟨-x⁻¹ - 1, hxr1⟩
  let b : NonzeroRat := nzRatMul negOneNZ
    ⟨x - 1, sub_ne_zero.mpr hx1⟩
  let q : NonzeroRat := ⟨y / x, div_ne_zero hy hx0⟩
  have hab : squareClassOf a = squareClassOf b := by
    apply ratSquareClass_eq_of_product_square a.property b.property q.property
    dsimp [a, b, q, nzRatMul, negOneNZ]
    field_simp [hx0]
    linear_combination -h
  rw [rationalZeroTorsion_translate_x h hx0]
  calc
    squareClassOf a = squareClassOf b := hab
    _ = squareClassOf negOneNZ *
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl
    _ = (torsionKummer .zero).2 *
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl

theorem rationalOneTranslate_firstSquareClass
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    squareClassOf
      ⟨rationalSecantSumX x y 1 0, by
        rw [rationalOneTorsion_translate_x h hx1]
        exact div_ne_zero
          (by intro hz; exact hxm1 (by linear_combination hz))
          (sub_ne_zero.mpr hx1)⟩
      =
    (torsionKummer .one).1 * squareClassOf ⟨x, hx0⟩ := by
  have hy := rational_y_ne_zero_of_x_ne_three_torsion_roots h hx0 hx1 hxm1
  let a : NonzeroRat :=
    ⟨(x + 1) / (x - 1),
      div_ne_zero
        (by intro hz; exact hxm1 (by linear_combination hz))
        (sub_ne_zero.mpr hx1)⟩
  let b : NonzeroRat := ⟨x, hx0⟩
  let q : NonzeroRat :=
    ⟨y / (x - 1), div_ne_zero hy (sub_ne_zero.mpr hx1)⟩
  have hab : squareClassOf a = squareClassOf b := by
    apply ratSquareClass_eq_of_product_square a.property b.property q.property
    dsimp [a, b, q]
    field_simp [sub_ne_zero.mpr hx1]
    linear_combination -h
  rw [rationalOneTorsion_translate_x h hx1]
  calc
    squareClassOf a = squareClassOf b := hab
    _ = (torsionKummer .one).1 * squareClassOf ⟨x, hx0⟩ := by
      simp [torsionKummer]

theorem rationalOneTranslate_secondSquareClass
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx1 : x ≠ 1) :
    squareClassOf
      ⟨rationalSecantSumX x y 1 0 - 1, by
        rw [rationalOneTorsion_translate_x h hx1]
        field_simp [sub_ne_zero.mpr hx1]
        norm_num⟩
      =
    (torsionKummer .one).2 *
      squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
  let a : NonzeroRat :=
    ⟨(x + 1) / (x - 1) - 1, by
      field_simp [sub_ne_zero.mpr hx1]
      norm_num⟩
  let b : NonzeroRat := nzRatMul twoNZ
    ⟨x - 1, sub_ne_zero.mpr hx1⟩
  have hab : squareClassOf a = squareClassOf b := by
    apply ratSquareClass_eq_of_product_square
      a.property b.property (by norm_num : (2 : ℚ) ≠ 0)
    dsimp [a, b, nzRatMul, twoNZ]
    field_simp [sub_ne_zero.mpr hx1]
    ring
  rw [rationalOneTorsion_translate_x h hx1]
  calc
    squareClassOf a = squareClassOf b := hab
    _ = squareClassOf twoNZ *
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl
    _ = (torsionKummer .one).2 *
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := rfl

theorem totalGlobalKummer_add_zeroTorsion_ordinary
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    totalGlobalKummer
      ((.affine x y h : RationalProjectivePoint) + rationalZeroTorsionPoint)
      = totalGlobalKummer (.affine x y h)
          * totalGlobalKummer rationalZeroTorsionPoint := by
  have hxR0 : rationalSecantSumX x y 0 0 ≠ 0 := by
    rw [rationalZeroTorsion_translate_x h hx0]
    exact neg_ne_zero.mpr (inv_ne_zero hx0)
  have hxR1 : rationalSecantSumX x y 0 0 ≠ 1 := by
    rw [rationalZeroTorsion_translate_x h hx0]
    intro heq
    have : x = -1 := by
      field_simp [hx0] at heq
      linear_combination heq
    exact hxm1 this
  rw [show rationalZeroTorsionPoint =
      (.affine 0 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [rationalProjective_secant_add h (by norm_num) hx0]
  simp only [totalGlobalKummer]
  split_ifs with hR0 hR1 h0 h1
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx0 h0).elim
  · exact (hx1 h1).elim
  · apply Prod.ext
    · simpa [mul_comm] using rationalZeroTranslate_firstSquareClass h hx0
    · simpa [mul_comm] using
        rationalZeroTranslate_secondSquareClass h hx0 hx1 hxm1

theorem totalGlobalKummer_add_oneTorsion_ordinary
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    totalGlobalKummer
      ((.affine x y h : RationalProjectivePoint) + rationalOneTorsionPoint)
      = totalGlobalKummer (.affine x y h)
          * totalGlobalKummer rationalOneTorsionPoint := by
  have hxR0 : rationalSecantSumX x y 1 0 ≠ 0 := by
    rw [rationalOneTorsion_translate_x h hx1]
    exact div_ne_zero
      (by intro hz; exact hxm1 (by linear_combination hz))
      (sub_ne_zero.mpr hx1)
  have hxR1 : rationalSecantSumX x y 1 0 ≠ 1 := by
    rw [rationalOneTorsion_translate_x h hx1]
    intro heq
    field_simp [sub_ne_zero.mpr hx1] at heq
    norm_num at heq
  rw [show rationalOneTorsionPoint =
      (.affine 1 0 (by norm_num) : RationalProjectivePoint) by rfl]
  rw [rationalProjective_secant_add h (by norm_num) (sub_ne_zero.mpr hx1)]
  simp only [totalGlobalKummer]
  split_ifs with hR0 hR1 h0 h1
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx0 h0).elim
  · exact (hx1 h1).elim
  · apply Prod.ext
    · simpa [mul_comm] using
        rationalOneTranslate_firstSquareClass h hx0 hx1 hxm1
    · simpa [mul_comm] using rationalOneTranslate_secondSquareClass h hx1

theorem totalGlobalKummer_add_minusOneTorsion_ordinary
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    totalGlobalKummer
      ((.affine x y h : RationalProjectivePoint) + rationalMinusOneTorsionPoint)
      = totalGlobalKummer (.affine x y h)
          * totalGlobalKummer rationalMinusOneTorsionPoint := by
  rw [show rationalMinusOneTorsionPoint =
      (.affine (-1) 0 (by norm_num) : RationalProjectivePoint) by rfl]
  have hx : x ≠ (-1 : ℚ) := hxm1
  have hxR0 : rationalSecantSumX x y (-1) 0 ≠ 0 := by
    have hform : rationalSecantSumX x y (-1) 0 = (1 - x) / (x + 1) := by
      unfold rationalSecantSumX rationalSecantSlope
      field_simp [show x + 1 ≠ 0 by
        intro hz; exact hxm1 (by linear_combination hz)]
      linear_combination -h
    rw [hform]
    exact div_ne_zero
      (by intro hz; exact hx1 (by linear_combination hz))
      (by intro hz; exact hxm1 (by linear_combination hz))
  have hxR1 : rationalSecantSumX x y (-1) 0 ≠ 1 := by
    have hform : rationalSecantSumX x y (-1) 0 = (1 - x) / (x + 1) := by
      unfold rationalSecantSumX rationalSecantSlope
      field_simp [show x + 1 ≠ 0 by
        intro hz; exact hxm1 (by linear_combination hz)]
      linear_combination -h
    rw [hform]
    intro heq
    have : x = 0 := by
      field_simp [show x + 1 ≠ 0 by
        intro hz; exact hxm1 (by linear_combination hz)] at heq
      linear_combination heq
    exact hx0 this
  exact totalGlobalKummer_secant_ordinary
    h (by norm_num) hx hx0 hx1 (by norm_num) (by norm_num) hxR0 hxR1

end Synthesis.Millennium.BSD
