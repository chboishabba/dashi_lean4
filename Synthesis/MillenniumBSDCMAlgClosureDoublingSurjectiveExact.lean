import Synthesis.MillenniumBSDActualAlgClosureTwoTorsionExact
import Synthesis.MillenniumBSDGlobalKummerKernelHalfPoint
import BSDCohomology.EllipticKummerDivisibilityReduction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-!
# Selected CM curve: multiplication by two is surjective over Qbar

For the literal curve

  E : y² = x³ - x

over `RatAlgClosure = AlgebraicClosure ℚ`, this file lifts the already-proved
rational half-point algebra to the algebraic closure.  Algebraic closedness
supplies square roots of `x`, `x-1`, and `x+1`; after choosing signs so that
`abc = -y`, the same classical half-point formula gives a point Q with 2Q=P.

This pays the geometric Kummer-surjectivity gate for the actual selected
curve, without assuming a `DivisibleBy` instance and without introducing a
synthetic point carrier.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

------------------------------------------------------------------------
-- Half-point algebra over Qbar.
------------------------------------------------------------------------

def algClosureHalfX
    (x a b c : RatAlgClosure) : RatAlgClosure :=
  x + a * b + b * c + c * a

def algClosureHalfY
    (y a b c : RatAlgClosure) : RatAlgClosure :=
  -y - (a + b + c) * (a * b + b * c + c * a)

theorem algClosureHalfY_eq_neg_pair_product
    {y a b c : RatAlgClosure}
    (habc : a * b * c = -y) :
    algClosureHalfY y a b c =
      -(a + b) * (a + c) * (b + c) := by
  unfold algClosureHalfY
  rw [← habc]
  ring

theorem algClosureHalfPoint_onCurve
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    algClosureHalfY y a b c ^ 2 =
      algClosureHalfX x a b c ^ 3 - algClosureHalfX x a b c := by
  have hx : x = a ^ 2 := ha.symm
  subst x
  have hy : y = -(a * b * c) := by
    rw [← neg_eq_iff_eq_neg]
    simpa [mul_assoc] using habc
  subst y
  have hB : b ^ 2 - a ^ 2 + 1 = 0 := by
    linear_combination hb
  have hC : c ^ 2 - a ^ 2 - 1 = 0 := by
    linear_combination hc
  unfold algClosureHalfX algClosureHalfY
  linear_combination
    (-(a + c) ^ 2 *
      (a ^ 2 - a*b - a*c - b ^ 2 - b*c - c ^ 2 + 1)) * hB
      + ((a + c) *
        (2*a ^ 3 + 2*a ^ 2*b + 2*a ^ 2*c +
          2*a*b*c - 2*a - b - c)) * hC

theorem algClosureHalfY_ne_zero
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    algClosureHalfY y a b c ≠ 0 := by
  rw [algClosureHalfY_eq_neg_pair_product habc]
  intro h
  have hp : (a + b) * (a + c) * (b + c) = 0 := by
    simpa using neg_eq_zero.mp h
  rcases mul_eq_zero.mp hp with hab | hbc
  · rcases mul_eq_zero.mp hab with hab0 | hac0
    · have hab' : a = -b := by linear_combination hab0
      have hab2 : a ^ 2 = b ^ 2 := by rw [hab']; ring
      have hone : (1 : RatAlgClosure) = 0 := by
        linear_combination ha - hb - hab2
      exact one_ne_zero hone
    · have hac' : a = -c := by linear_combination hac0
      have hac2 : a ^ 2 = c ^ 2 := by rw [hac']; ring
      have hone : (1 : RatAlgClosure) = 0 := by
        linear_combination hc - ha + hac2
      exact one_ne_zero hone
  · have hbc' : b = -c := by linear_combination hbc
    have hbc2 : b ^ 2 = c ^ 2 := by rw [hbc']; ring
    have htwo : (2 : RatAlgClosure) = 0 := by
      linear_combination hc - hb + hbc2
    norm_num at htwo

------------------------------------------------------------------------
-- Tangent doubling formulas over Qbar, on the actual base-changed curve.
------------------------------------------------------------------------

def algClosureTangentSlope (x y : RatAlgClosure) : RatAlgClosure :=
  (3 * x ^ 2 - 1) / (2 * y)

def algClosureTangentSumX (x y : RatAlgClosure) : RatAlgClosure :=
  algClosureTangentSlope x y ^ 2 - 2 * x

def algClosureTangentSumY (x y : RatAlgClosure) : RatAlgClosure :=
  -(algClosureTangentSlope x y *
      (algClosureTangentSumX x y - x) + y)

theorem cmAlgClosure_negY_eq_neg (x y : RatAlgClosure) :
    cmAlgClosureWeierstrass.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY,
    cmAlgClosureWeierstrass, cmWeierstrass]

theorem cmAlgClosure_y_ne_negY_of_ne_zero
    {x y : RatAlgClosure} (hy : y ≠ 0) :
    y ≠ cmAlgClosureWeierstrass.toAffine.negY x y := by
  rw [cmAlgClosure_negY_eq_neg]
  intro h
  have h2 : (2 : RatAlgClosure) * y = 0 := by linear_combination h
  exact hy (mul_eq_zero.mp h2 |>.resolve_left (by norm_num))

theorem cmAlgClosure_tangent_slope_eq
    {x y : RatAlgClosure} (hy : y ≠ 0) :
    cmAlgClosureWeierstrass.toAffine.slope x x y y =
      algClosureTangentSlope x y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (cmAlgClosure_y_ne_negY_of_ne_zero hy)]
  simp [algClosureTangentSlope, cmAlgClosureWeierstrass,
    cmWeierstrass, WeierstrassCurve.Affine.negY]
  ring

theorem cmAlgClosure_tangent_addX_eq
    {x y : RatAlgClosure} (hy : y ≠ 0) :
    cmAlgClosureWeierstrass.toAffine.addX x x
      (cmAlgClosureWeierstrass.toAffine.slope x x y y) =
      algClosureTangentSumX x y := by
  rw [cmAlgClosure_tangent_slope_eq hy]
  simp [algClosureTangentSumX, WeierstrassCurve.Affine.addX,
    cmAlgClosureWeierstrass, cmWeierstrass]

theorem cmAlgClosure_tangent_addY_eq
    {x y : RatAlgClosure} (hy : y ≠ 0) :
    cmAlgClosureWeierstrass.toAffine.addY x x y
      (cmAlgClosureWeierstrass.toAffine.slope x x y y) =
      algClosureTangentSumY x y := by
  rw [cmAlgClosure_tangent_slope_eq hy]
  simp [algClosureTangentSumY, algClosureTangentSumX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    cmAlgClosureWeierstrass, cmWeierstrass]

theorem algClosureTangentSum_onCurve
    {x y : RatAlgClosure}
    (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    algClosureTangentSumY x y ^ 2 =
      algClosureTangentSumX x y ^ 3 - algClosureTangentSumX x y := by
  have heq := (cmAlgClosure_equation_iff x y).mpr h
  have hadd := WeierstrassCurve.Affine.equation_add
    heq heq (fun hxy => (cmAlgClosure_y_ne_negY_of_ne_zero hy) hxy.2)
  rw [cmAlgClosure_tangent_addX_eq hy,
      cmAlgClosure_tangent_addY_eq hy] at hadd
  exact (cmAlgClosure_equation_iff
    (algClosureTangentSumX x y)
    (algClosureTangentSumY x y)).mp hadd

theorem cmAlgClosureProjective_tangent_double
    {x y : RatAlgClosure}
    (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    (.affine x y h : CMAlgClosureProjectivePoint) + .affine x y h =
      .affine (algClosureTangentSumX x y) (algClosureTangentSumY x y)
        (algClosureTangentSum_onCurve h hy) := by
  apply cmAlgClosurePointEquivMathlib.injective
  rw [cmAlgClosurePointAddEquivMathlib.map_add]
  simp only [cmAlgClosurePointEquivMathlib]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (cmAlgClosure_y_ne_negY_of_ne_zero hy)]
  congr
  · exact cmAlgClosure_tangent_addX_eq hy
  · exact cmAlgClosure_tangent_addY_eq hy

------------------------------------------------------------------------
-- The half-point formula doubles to the requested affine point.
------------------------------------------------------------------------

theorem algClosureHalf_tangent_numerator
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    3 * algClosureHalfX x a b c ^ 2 - 1 +
      2 * algClosureHalfY y a b c * (a + b + c) = 0 := by
  have hx : x = a ^ 2 := ha.symm
  subst x
  have hy : y = -(a * b * c) := by
    rw [← neg_eq_iff_eq_neg]
    simpa [mul_assoc] using habc
  subst y
  have hB : b ^ 2 - a ^ 2 + 1 = 0 := by linear_combination hb
  have hC : c ^ 2 - a ^ 2 - 1 = 0 := by linear_combination hc
  unfold algClosureHalfX algClosureHalfY
  linear_combination
    (-(a + c) * (a + 2*b + c)) * hB
      + (-2*a ^ 2 - 2*a*b - 2*a*c - 2*b*c + 1) * hC

theorem algClosureHalf_tangent_slope
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    algClosureTangentSlope
      (algClosureHalfX x a b c)
      (algClosureHalfY y a b c) = -(a + b + c) := by
  have hy0 := algClosureHalfY_ne_zero ha hb hc habc
  have hnum := algClosureHalf_tangent_numerator ha hb hc habc
  unfold algClosureTangentSlope
  field_simp [hy0]
  linear_combination hnum

theorem algClosureHalf_double_x
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    algClosureTangentSumX
      (algClosureHalfX x a b c)
      (algClosureHalfY y a b c) = x := by
  rw [show algClosureTangentSlope
      (algClosureHalfX x a b c)
      (algClosureHalfY y a b c) = -(a + b + c) from
    algClosureHalf_tangent_slope ha hb hc habc]
  unfold algClosureTangentSumX algClosureHalfX
  linear_combination ha + hb + hc

theorem algClosureHalf_double_y
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    algClosureTangentSumY
      (algClosureHalfX x a b c)
      (algClosureHalfY y a b c) = y := by
  have hs := algClosureHalf_tangent_slope ha hb hc habc
  have hx := algClosureHalf_double_x ha hb hc habc
  unfold algClosureTangentSumY
  rw [hs, hx]
  unfold algClosureHalfX algClosureHalfY
  ring

theorem cmAlgClosure_affine_is_double
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x) :
    ∃ Q : CMAlgClosureProjectivePoint,
      (.affine x y hcurve : CMAlgClosureProjectivePoint) = Q + Q := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (x - 1) (by norm_num : 0 < 2)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (x + 1) (by norm_num : 0 < 2)
  have hsq : (a * b * c) ^ 2 = y ^ 2 := by
    rw [mul_pow, mul_pow, ha, hb, hc, hcurve]
    ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with habcPos | habcNeg
  · let a' := -a
    have ha' : a' ^ 2 = x := by dsimp [a']; simpa using ha
    have habc' : a' * b * c = -y := by
      dsimp [a']
      rw [habcPos]
      ring
    let qx := algClosureHalfX x a' b c
    let qy := algClosureHalfY y a' b c
    have hQ : qy ^ 2 = qx ^ 3 - qx := by
      dsimp [qx, qy]
      exact algClosureHalfPoint_onCurve ha' hb hc habc'
    have hqy : qy ≠ 0 := by
      dsimp [qy]
      exact algClosureHalfY_ne_zero ha' hb hc habc'
    let Q : CMAlgClosureProjectivePoint := .affine qx qy hQ
    refine ⟨Q, ?_⟩
    have hd := cmAlgClosureProjective_tangent_double hQ hqy
    have hx2 : algClosureTangentSumX qx qy = x := by
      dsimp [qx, qy]
      exact algClosureHalf_double_x ha' hb hc habc'
    have hy2 : algClosureTangentSumY qx qy = y := by
      dsimp [qx, qy]
      exact algClosureHalf_double_y ha' hb hc habc'
    rw [hd, hx2, hy2]
  · let qx := algClosureHalfX x a b c
    let qy := algClosureHalfY y a b c
    have hQ : qy ^ 2 = qx ^ 3 - qx := by
      dsimp [qx, qy]
      exact algClosureHalfPoint_onCurve ha hb hc habcNeg
    have hqy : qy ≠ 0 := by
      dsimp [qy]
      exact algClosureHalfY_ne_zero ha hb hc habcNeg
    let Q : CMAlgClosureProjectivePoint := .affine qx qy hQ
    refine ⟨Q, ?_⟩
    have hd := cmAlgClosureProjective_tangent_double hQ hqy
    have hx2 : algClosureTangentSumX qx qy = x := by
      dsimp [qx, qy]
      exact algClosureHalf_double_x ha hb hc habcNeg
    have hy2 : algClosureTangentSumY qx qy = y := by
      dsimp [qx, qy]
      exact algClosureHalf_double_y ha hb hc habcNeg
    rw [hd, hx2, hy2]

/-- Multiplication by two is surjective on the actual algebraic-closure point
group of the selected CM elliptic curve. -/
theorem cmAlgClosure_doubling_surjective :
    Function.Surjective
      (fun P : CMAlgClosureProjectivePoint => (2 : ℕ) • P) := by
  intro P
  cases P with
  | infinity =>
      refine ⟨0, ?_⟩
      simp [cmAlgClosure_zero_eq_infinity]
  | affine x y hcurve =>
      obtain ⟨Q, hQ⟩ := cmAlgClosure_affine_is_double hcurve
      exact ⟨Q, by simpa [two_nsmul] using hQ.symm⟩

/-- Same theorem transported to the literal Mathlib geometric point carrier
used by the cohomological Kummer lane. -/
theorem cmGeometricDoubling_surjective :
    Function.Surjective
      (BSDCohomology.geometricDoubling cmWeierstrass) := by
  intro P
  let P' : CMAlgClosureProjectivePoint :=
    cmAlgClosurePointEquivMathlib.symm P
  obtain ⟨Q', hQ'⟩ := cmAlgClosure_doubling_surjective P'
  refine ⟨cmAlgClosurePointEquivMathlib Q', ?_⟩
  change (2 : ℕ) • cmAlgClosurePointEquivMathlib Q' = P
  rw [← cmAlgClosurePointAddEquivMathlib.map_nsmul]
  rw [hQ']
  exact cmAlgClosurePointEquivMathlib.apply_symm_apply P

/-!
MAX-CUT STATUS

PAID:
* actual algebraic-closure square roots;
* literal half-point construction on the selected curve;
* actual Mathlib elliptic group law used for doubling;
* surjectivity of `[2]` on the selected curve's genuine geometric points.

NEXT:
* feed `cmGeometricDoubling_surjective` into the existing group Kummer exactness
  owner;
* package inclusion/doubling as equivariant continuous TopRep morphisms;
* construct the H⁰/H¹ connecting map and localization naturality.

The general theorem for every elliptic curve over every algebraically closed
field remains separate; this file pays exactly the selected-curve BSD bridge.
-/

end Synthesis.Millennium.BSD
