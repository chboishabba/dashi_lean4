import Synthesis.MillenniumBSDGlobalKummerQuotientToSelmer
import Mathlib.Tactic

/-!
# Explicit half-point construction from a trivial global Kummer class

For E : y^2 = x(x-1)(x+1), triviality of the two Kummer coordinates
means x and x-1 are rational squares.  The curve equation then makes x+1
a rational square as well.  Choosing roots a,b,c with abc=-y, the classical
half-point formula is

  x_Q = x + ab + bc + ca
  y_Q = -y - (a+b+c)(ab+bc+ca).

We prove directly that Q lies on E and that the actual mathlib elliptic
doubling law sends Q to P.  This is the hard direction of ker(delta)=2E(Q)
for the literal full-2-torsion curve.
-/

namespace Synthesis.Millennium.BSD

theorem squareClass_eq_one_iff_exists_square
    (q : NonzeroRat) :
    squareClassOf q = (1 : RatSquareClass)
      ↔ ∃ r : ℚ, (q : ℚ) = r ^ 2 := by
  constructor
  · intro h
    change squareClassOf q = squareClassOf nzRatOne at h
    have hrel : SquareRel q nzRatOne := Quotient.exact h
    rcases hrel with ⟨s, t, hst⟩
    refine ⟨(t : ℚ) / (s : ℚ), ?_⟩
    apply (mul_right_cancel₀ (pow_ne_zero 2 s.property))
    calc
      (q : ℚ) * (s : ℚ) ^ 2 =
          (nzRatOne : ℚ) * (t : ℚ) ^ 2 := hst
      _ = ((t : ℚ) / (s : ℚ)) ^ 2 * (s : ℚ) ^ 2 := by
        dsimp [nzRatOne]
        field_simp [s.property]
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      simp at hr
      exact q.property hr
    apply Quotient.sound
    refine ⟨nzRatOne, ⟨r, hr0⟩, ?_⟩
    dsimp [nzRatOne]
    simpa [hr]

theorem ordinaryKummer_eq_one_square_roots
    (P : OrdinaryKummerPoint)
    (h : ordinaryKummer P =
      (1 : RatSquareClass × RatSquareClass)) :
    ∃ a b : ℚ, P.x = a ^ 2 ∧ P.x - 1 = b ^ 2 := by
  have hx := congrArg Prod.fst h
  have hx1 := congrArg Prod.snd h
  simp only [ordinaryKummer, Prod.fst, Prod.snd] at hx hx1
  obtain ⟨a, ha⟩ :=
    (squareClass_eq_one_iff_exists_square
      ⟨P.x, P.x_ne_zero⟩).mp hx
  obtain ⟨b, hb⟩ :=
    (squareClass_eq_one_iff_exists_square
      ⟨P.x - 1, sub_ne_zero.mpr P.x_ne_one⟩).mp hx1
  exact ⟨a, b, ha.symm, hb.symm⟩

theorem torsionKummer_zero_ne_one :
    torsionKummer .zero ≠
      (1 : RatSquareClass × RatSquareClass) := by
  intro h
  have hs := congrArg
    (fun z => squareClassSignBit z.1) h
  simpa [torsionKummer, negOneNZ, nzRatOne,
    signBit_neg_one, signBit_one] using hs

theorem torsionKummer_one_ne_one :
    torsionKummer .one ≠
      (1 : RatSquareClass × RatSquareClass) := by
  intro h
  have hv := congrArg
    (fun z => squareClassV2Parity z.2) h
  simpa [torsionKummer, twoNZ, nzRatOne,
    v2Parity_two, v2Parity_one] using hv

def rationalHalfX (x a b c : ℚ) : ℚ :=
  x + a * b + b * c + c * a

def rationalHalfY (y a b c : ℚ) : ℚ :=
  -y - (a + b + c) * (a * b + b * c + c * a)

theorem rationalHalfY_eq_neg_pair_product
    {y a b c : ℚ}
    (habc : a * b * c = -y) :
    rationalHalfY y a b c
      = -(a + b) * (a + c) * (b + c) := by
  unfold rationalHalfY
  rw [← habc]
  ring

theorem rationalHalfY_ne_zero
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    rationalHalfY y a b c ≠ 0 := by
  rw [rationalHalfY_eq_neg_pair_product habc]
  intro h
  have hp : (a + b) * (a + c) * (b + c) = 0 := by
    linarith
  rcases mul_eq_zero.mp hp with hab | hbc
  · rcases mul_eq_zero.mp hab with hab0 | hac0
    · have hab2 : a ^ 2 = b ^ 2 := by
        have hab' : a = -b := by linarith
        rw [hab']
        ring
      nlinarith [ha, hb, hab2]
    · have hac2 : a ^ 2 = c ^ 2 := by
        have hac' : a = -c := by linarith
        rw [hac']
        ring
      nlinarith [ha, hc, hac2]
  · have hbc2 : b ^ 2 = c ^ 2 := by
      have hbc' : b = -c := by linarith
      rw [hbc']
      ring
    nlinarith [hb, hc, hbc2]

theorem rationalHalfPoint_onCurve
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    rationalHalfY y a b c ^ 2
      = rationalHalfX x a b c ^ 3 - rationalHalfX x a b c := by
  have hx : x = a ^ 2 := ha.symm
  subst x
  have hy : y = -(a * b * c) := by linarith [habc]
  subst y
  have hB : b ^ 2 - a ^ 2 + 1 = 0 := by nlinarith [hb]
  have hC : c ^ 2 - a ^ 2 - 1 = 0 := by nlinarith [hc]
  unfold rationalHalfX rationalHalfY
  linear_combination
    (-(a + c) ^ 2 *
      (a ^ 2 - a*b - a*c - b ^ 2 - b*c - c ^ 2 + 1)) * hB
      + ((a + c) *
        (2*a ^ 3 + 2*a ^ 2*b + 2*a ^ 2*c +
          2*a*b*c - 2*a - b - c)) * hC

theorem rationalHalf_tangent_numerator
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    3 * rationalHalfX x a b c ^ 2 - 1
      + 2 * rationalHalfY y a b c * (a + b + c) = 0 := by
  have hx : x = a ^ 2 := ha.symm
  subst x
  have hy : y = -(a * b * c) := by linarith [habc]
  subst y
  have hB : b ^ 2 - a ^ 2 + 1 = 0 := by nlinarith [hb]
  have hC : c ^ 2 - a ^ 2 - 1 = 0 := by nlinarith [hc]
  unfold rationalHalfX rationalHalfY
  linear_combination
    (-(a + c) * (a + 2*b + c)) * hB
      + (-2*a ^ 2 - 2*a*b - 2*a*c - 2*b*c + 1) * hC

theorem rationalHalf_tangent_slope
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    rationalTangentSlope
      (rationalHalfX x a b c)
      (rationalHalfY y a b c)
      = -(a + b + c) := by
  have hy0 := rationalHalfY_ne_zero ha hb hc habc
  have hnum := rationalHalf_tangent_numerator ha hb hc habc
  unfold rationalTangentSlope
  field_simp [hy0]
  linear_combination hnum

theorem rationalHalf_double_x
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    rationalTangentSumX
      (rationalHalfX x a b c)
      (rationalHalfY y a b c) = x := by
  rw [show rationalTangentSlope
      (rationalHalfX x a b c)
      (rationalHalfY y a b c)
      = -(a + b + c) from
    rationalHalf_tangent_slope ha hb hc habc]
  unfold rationalTangentSumX rationalHalfX
  linear_combination ha + hb + hc

theorem rationalHalf_double_y
    {x y a b c : ℚ}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    rationalTangentSumY
      (rationalHalfX x a b c)
      (rationalHalfY y a b c) = y := by
  have hs := rationalHalf_tangent_slope ha hb hc habc
  have hx := rationalHalf_double_x ha hb hc habc
  unfold rationalTangentSumY
  rw [hs, hx]
  unfold rationalHalfX rationalHalfY
  ring

theorem rationalPoint_double_of_three_squares
    {x y a b c : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    ∃ Q : RationalProjectivePoint,
      (.affine x y hcurve : RationalProjectivePoint) = Q + Q := by
  let qx := rationalHalfX x a b c
  let qy := rationalHalfY y a b c
  have hQ : qy ^ 2 = qx ^ 3 - qx := by
    dsimp [qx, qy]
    exact rationalHalfPoint_onCurve ha hb hc habc
  have hqy : qy ≠ 0 := by
    dsimp [qy]
    exact rationalHalfY_ne_zero ha hb hc habc
  let Q : RationalProjectivePoint := .affine qx qy hQ
  refine ⟨Q, ?_⟩
  have hd := rationalProjective_tangent_double hQ hqy
  have hx2 : rationalTangentSumX qx qy = x := by
    dsimp [qx, qy]
    exact rationalHalf_double_x ha hb hc habc
  have hy2 : rationalTangentSumY qx qy = y := by
    dsimp [qx, qy]
    exact rationalHalf_double_y ha hb hc habc
  rw [hd, hx2, hy2]

theorem trivialOrdinaryKummer_implies_double
    (P : OrdinaryKummerPoint)
    (h : ordinaryKummer P =
      (1 : RatSquareClass × RatSquareClass)) :
    ∃ Q : RationalProjectivePoint,
      (.affine P.x P.y P.onCurve : RationalProjectivePoint) = Q + Q := by
  obtain ⟨a, b, ha, hb⟩ := ordinaryKummer_eq_one_square_roots P h
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp at ha
    exact P.x_ne_zero ha
  have hb0 : b ≠ 0 := by
    intro hz
    subst b
    simp at hb
    exact P.x_ne_one (by linarith [hb])
  let c : ℚ := -P.y / (a * b)
  have hc : c ^ 2 = P.x + 1 := by
    dsimp [c]
    calc
      (-P.y / (a * b)) ^ 2 =
          P.y ^ 2 / (a * b) ^ 2 := by ring
      _ = (P.x ^ 3 - P.x) / (P.x * (P.x - 1)) := by
        rw [P.onCurve, mul_pow, ha, hb]
      _ = P.x + 1 := by
        field_simp [P.x_ne_zero, sub_ne_zero.mpr P.x_ne_one]
        ring
  have habc : a * b * c = -P.y := by
    dsimp [c]
    field_simp [ha0, hb0]
  exact rationalPoint_double_of_three_squares
    P.onCurve ha hb hc habc

theorem totalGlobalKummer_eq_one_implies_double
    (P : RationalProjectivePoint)
    (h : totalGlobalKummer P =
      (1 : RatSquareClass × RatSquareClass)) :
    ∃ Q : RationalProjectivePoint, P = Q + Q := by
  cases P with
  | infinity =>
      refine ⟨0, ?_⟩
      rw [← rationalProjective_zero_eq_infinity]
      simp
  | affine x y hcurve =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_zero hcurve rfl
        subst y
        exfalso
        apply torsionKummer_zero_ne_one
        simpa [totalGlobalKummer] using h
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_one hcurve rfl
        subst y
        exfalso
        apply torsionKummer_one_ne_one
        simpa [totalGlobalKummer] using h
      · let OP : OrdinaryKummerPoint :=
          { x := x, y := y, onCurve := hcurve,
            x_ne_zero := hx0, x_ne_one := hx1 }
        have hOP : ordinaryKummer OP =
            (1 : RatSquareClass × RatSquareClass) := by
          simpa [totalGlobalKummer, hx0, hx1, OP] using h
        simpa [OP] using trivialOrdinaryKummer_implies_double OP hOP

end Synthesis.Millennium.BSD
