import Synthesis.MillenniumBSDCMTorsionTranslationExact
import Mathlib.Tactic

/-!
# Selected CM curve: finite root-sign / E[2] translation table

For the explicit half of

  E : y² = x³ - x

chosen from square roots

  a² = x,  b² = x-1,  c² = x+1,  abc = -y,

the three nontrivial even root-sign flips are now identified with the literal
Mathlib elliptic-group translations by `(0,0)`, `(1,0)`, and `(-1,0)`.

The proof deliberately uses the already-paid objects on both sides:

* `MillenniumBSDCMHalfSignActionExact` gives the three exact x-coordinate
  involution identities for the sign-flipped halves;
* `MillenniumBSDCMTorsionTranslationExact` gives the same involutions for
  actual addition by the three rational two-torsion points;
* Mathlib's `Point.xRep_eq_xRep_iff` reduces equal x-coordinate representatives
  to equality or negation;
* both candidates double to the same target point, and `y ≠ 0` rules out the
  negation branch.

Thus this is a same-object point equality, not merely a matching table of
Möbius formulas.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- The literal explicit half as a point of the already-selected Qbar group. -/
def cmExplicitHalfPoint
    (x y a b c : RatAlgClosure)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) : CMAlgClosureProjectivePoint :=
  .affine
    (algClosureHalfX x a b c)
    (algClosureHalfY y a b c)
    (algClosureHalfPoint_onCurve ha hb hc habc)

/-- Every explicit half really doubles to its target on the actual selected
elliptic group. -/
theorem cmExplicitHalfPoint_double
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    (2 : ℕ) • cmExplicitHalfPoint x y a b c ha hb hc habc =
      (.affine x y hcurve : CMAlgClosureProjectivePoint) := by
  rw [two_nsmul]
  unfold cmExplicitHalfPoint
  have hQ := algClosureHalfPoint_onCurve ha hb hc habc
  have hQy := algClosureHalfY_ne_zero ha hb hc habc
  rw [cmAlgClosureProjective_tangent_double hQ hQy]
  have hx := algClosureHalf_double_x ha hb hc habc
  have hy := algClosureHalf_double_y ha hb hc habc
  simp only at hx hy
  rw [hx, hy]

/-- A selected affine target with nonzero y-coordinate is not its own inverse,
so it is not a two-torsion point. -/
theorem cmAlgClosure_affine_ne_neg_self_of_y_ne_zero
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (.affine x y hcurve : CMAlgClosureProjectivePoint) ≠
      -(.affine x y hcurve : CMAlgClosureProjectivePoint) := by
  intro h
  rw [cmAlgClosure_neg_affine] at h
  injection h with _ hyneg
  apply hy
  linarith

/-- Equal x-representatives plus equality of doubles identify actual selected
Qbar points as long as the common double is not two-torsion. -/
theorem cmAlgClosure_eq_of_xRep_eq_of_same_double
    {A B P : CMAlgClosureProjectivePoint}
    (hx :
      (cmAlgClosurePointAddEquivMathlib A).xRep =
        (cmAlgClosurePointAddEquivMathlib B).xRep)
    (hA : (2 : ℕ) • A = P)
    (hB : (2 : ℕ) • B = P)
    (hP : P ≠ -P) :
    A = B := by
  rcases WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff.mp hx with h | h
  · exact cmAlgClosurePointAddEquivMathlib.injective h
  · have hAB : A = -B := by
      apply cmAlgClosurePointAddEquivMathlib.injective
      simpa using h
    have hd := congrArg (fun R : CMAlgClosureProjectivePoint => (2 : ℕ) • R) hAB
    rw [hA, nsmul_neg, hB] at hd
    exact (hP hd).elim

/-- The `(b,c)` sign flip has exactly the x-representative of translation by
`(0,0)`. -/
theorem cmExplicitHalf_flip_bc_xRep_eq_add_torsion0
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let hb' : (-b) ^ 2 = x - 1 := by simpa using hb
    let hc' : (-c) ^ 2 = x + 1 := by simpa using hc
    let habc' : a * (-b) * (-c) = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).1
    let Qbc := cmExplicitHalfPoint x y a (-b) (-c) ha hb' hc' habc'
    (cmAlgClosurePointAddEquivMathlib
      (Q + actualZeroTorsionSubgroupPoint.1)).xRep =
      (cmAlgClosurePointAddEquivMathlib Qbc).xRep := by
  dsimp
  have hQ := algClosureHalfPoint_onCurve ha hb hc habc
  have hQy := algClosureHalfY_ne_zero ha hb hc habc
  have hQx0 := cmAlgClosure_x_ne_zero_of_y_ne_zero hQ hQy
  have hprod := algClosureHalfX_flip_bc_product ha hb hc
  have hxflip :
      algClosureHalfX x a (-b) (-c) =
        -1 / algClosureHalfX x a b c := by
    apply (eq_div_iff hQx0).2
    simpa [mul_comm] using hprod
  rw [cmAlgClosurePointAddEquivMathlib.map_add]
  change
    (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x a b c)
        (algClosureHalfY y a b c) _ +
      WeierstrassCurve.Affine.Point.some 0 0 _).xRep =
      (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x a (-b) (-c))
        (algClosureHalfY y a (-b) (-c)) _).xRep
  rw [cmAlgClosure_add_torsion0_xRep hQ hQy]
  simp [WeierstrassCurve.Affine.Point.xRep_some, hxflip]

/-- Full x-representative formula for translation by `(1,0)`. -/
theorem cmAlgClosure_add_torsion1_xRep_exact
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y
        ((cmAlgClosure_equation_iff x y).mpr hcurve) +
      WeierstrassCurve.Affine.Point.some 1 0
        ((cmAlgClosure_equation_iff 1 0).mpr (by norm_num))).xRep
      = ![(x + 1) / (x - 1), 1] := by
  have hx1 := cmAlgClosure_x_ne_one_of_y_ne_zero hcurve hy
  rw [WeierstrassCurve.Affine.Point.xRep_add_of_X_ne
    ((cmAlgClosure_equation_iff x y).mpr hcurve)
    ((cmAlgClosure_equation_iff 1 0).mpr (by norm_num)) hx1]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  field_simp [hx1]
  nlinarith [hcurve]

/-- Full x-representative formula for translation by `(-1,0)`. -/
theorem cmAlgClosure_add_torsionNeg1_xRep_exact
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y
        ((cmAlgClosure_equation_iff x y).mpr hcurve) +
      WeierstrassCurve.Affine.Point.some (-1) 0
        ((cmAlgClosure_equation_iff (-1) 0).mpr (by norm_num))).xRep
      = ![(1 - x) / (x + 1), 1] := by
  have hxn1 := cmAlgClosure_x_ne_neg_one_of_y_ne_zero hcurve hy
  rw [WeierstrassCurve.Affine.Point.xRep_add_of_X_ne
    ((cmAlgClosure_equation_iff x y).mpr hcurve)
    ((cmAlgClosure_equation_iff (-1) 0).mpr (by norm_num)) hxn1]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  field_simp [hxn1]
  nlinarith [hcurve]

/-- The `(a,c)` sign flip has exactly the x-representative of translation by
`(1,0)`. -/
theorem cmExplicitHalf_flip_ac_xRep_eq_add_torsion1
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let ha' : (-a) ^ 2 = x := by simpa using ha
    let hc' : (-c) ^ 2 = x + 1 := by simpa using hc
    let habc' : (-a) * b * (-c) = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).2.1
    let Qac := cmExplicitHalfPoint x y (-a) b (-c) ha' hb hc' habc'
    (cmAlgClosurePointAddEquivMathlib
      (Q + actualOneTorsionSubgroupPoint.1)).xRep =
      (cmAlgClosurePointAddEquivMathlib Qac).xRep := by
  dsimp
  have hQ := algClosureHalfPoint_onCurve ha hb hc habc
  have hQy := algClosureHalfY_ne_zero ha hb hc habc
  have hx1 := cmAlgClosure_x_ne_one_of_y_ne_zero hQ hQy
  have hprod := algClosureHalfX_flip_ac_sub_one_product ha hb hc
  have hxflip :
      algClosureHalfX x (-a) b (-c) =
        (algClosureHalfX x a b c + 1) /
          (algClosureHalfX x a b c - 1) := by
    have hne : algClosureHalfX x a b c - 1 ≠ 0 := sub_ne_zero.mpr hx1
    apply (eq_div_iff hne).2
    have hp :
        (algClosureHalfX x a b c - 1) *
          (algClosureHalfX x (-a) b (-c) - 1) = 2 := hprod
    field_simp [hne]
    nlinarith [hp]
  rw [cmAlgClosurePointAddEquivMathlib.map_add]
  change
    (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x a b c)
        (algClosureHalfY y a b c) _ +
      WeierstrassCurve.Affine.Point.some 1 0 _).xRep =
      (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x (-a) b (-c))
        (algClosureHalfY y (-a) b (-c)) _).xRep
  rw [cmAlgClosure_add_torsion1_xRep_exact hQ hQy]
  simp [WeierstrassCurve.Affine.Point.xRep_some, hxflip]

/-- The `(a,b)` sign flip has exactly the x-representative of translation by
`(-1,0)`. -/
theorem cmExplicitHalf_flip_ab_xRep_eq_add_torsionNeg1
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let ha' : (-a) ^ 2 = x := by simpa using ha
    let hb' : (-b) ^ 2 = x - 1 := by simpa using hb
    let habc' : (-a) * (-b) * c = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).2.2
    let Qab := cmExplicitHalfPoint x y (-a) (-b) c ha' hb' hc habc'
    (cmAlgClosurePointAddEquivMathlib
      (Q + actualMinusOneTorsionSubgroupPoint.1)).xRep =
      (cmAlgClosurePointAddEquivMathlib Qab).xRep := by
  dsimp
  have hQ := algClosureHalfPoint_onCurve ha hb hc habc
  have hQy := algClosureHalfY_ne_zero ha hb hc habc
  have hxn1 := cmAlgClosure_x_ne_neg_one_of_y_ne_zero hQ hQy
  have hprod := algClosureHalfX_flip_ab_add_one_product ha hb hc
  have hxflip :
      algClosureHalfX x (-a) (-b) c =
        (1 - algClosureHalfX x a b c) /
          (algClosureHalfX x a b c + 1) := by
    have hne : algClosureHalfX x a b c + 1 ≠ 0 := by
      exact add_ne_zero.mpr (by simpa [eq_comm] using hxn1)
    apply (eq_div_iff hne).2
    have hp :
        (algClosureHalfX x a b c + 1) *
          (algClosureHalfX x (-a) (-b) c + 1) = 2 := hprod
    field_simp [hne]
    nlinarith [hp]
  rw [cmAlgClosurePointAddEquivMathlib.map_add]
  change
    (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x a b c)
        (algClosureHalfY y a b c) _ +
      WeierstrassCurve.Affine.Point.some (-1) 0 _).xRep =
      (WeierstrassCurve.Affine.Point.some
        (algClosureHalfX x (-a) (-b) c)
        (algClosureHalfY y (-a) (-b) c) _).xRep
  rw [cmAlgClosure_add_torsionNeg1_xRep_exact hQ hQy]
  simp [WeierstrassCurve.Affine.Point.xRep_some, hxflip]

/-- First nontrivial row of the finite table: flip `(b,c)` is actual addition
by `(0,0)`. -/
theorem cmExplicitHalf_flip_bc_eq_add_torsion0
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let hb' : (-b) ^ 2 = x - 1 := by simpa using hb
    let hc' : (-c) ^ 2 = x + 1 := by simpa using hc
    let habc' : a * (-b) * (-c) = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).1
    Q + actualZeroTorsionSubgroupPoint.1 =
      cmExplicitHalfPoint x y a (-b) (-c) ha hb' hc' habc' := by
  dsimp
  apply cmAlgClosure_eq_of_xRep_eq_of_same_double
  · exact cmExplicitHalf_flip_bc_xRep_eq_add_torsion0 ha hb hc habc
  · rw [nsmul_add]
    rw [cmExplicitHalfPoint_double hcurve ha hb hc habc]
    rw [actualZeroTorsionSubgroupPoint.2]
    exact add_zero _
  · apply cmExplicitHalfPoint_double hcurve
  · exact cmAlgClosure_affine_ne_neg_self_of_y_ne_zero hcurve hy

/-- Second nontrivial row: flip `(a,c)` is actual addition by `(1,0)`. -/
theorem cmExplicitHalf_flip_ac_eq_add_torsion1
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let ha' : (-a) ^ 2 = x := by simpa using ha
    let hc' : (-c) ^ 2 = x + 1 := by simpa using hc
    let habc' : (-a) * b * (-c) = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).2.1
    Q + actualOneTorsionSubgroupPoint.1 =
      cmExplicitHalfPoint x y (-a) b (-c) ha' hb hc' habc' := by
  dsimp
  apply cmAlgClosure_eq_of_xRep_eq_of_same_double
  · exact cmExplicitHalf_flip_ac_xRep_eq_add_torsion1 ha hb hc habc
  · rw [nsmul_add]
    rw [cmExplicitHalfPoint_double hcurve ha hb hc habc]
    rw [actualOneTorsionSubgroupPoint.2]
    exact add_zero _
  · apply cmExplicitHalfPoint_double hcurve
  · exact cmAlgClosure_affine_ne_neg_self_of_y_ne_zero hcurve hy

/-- Third nontrivial row: flip `(a,b)` is actual addition by `(-1,0)`. -/
theorem cmExplicitHalf_flip_ab_eq_add_torsionNeg1
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    let ha' : (-a) ^ 2 = x := by simpa using ha
    let hb' : (-b) ^ 2 = x - 1 := by simpa using hb
    let habc' : (-a) * (-b) * c = -y :=
      (algClosureHalf_even_sign_flips_preserve_product habc).2.2
    Q + actualMinusOneTorsionSubgroupPoint.1 =
      cmExplicitHalfPoint x y (-a) (-b) c ha' hb' hc habc' := by
  dsimp
  apply cmAlgClosure_eq_of_xRep_eq_of_same_double
  · exact cmExplicitHalf_flip_ab_xRep_eq_add_torsionNeg1 ha hb hc habc
  · rw [nsmul_add]
    rw [cmExplicitHalfPoint_double hcurve ha hb hc habc]
    rw [actualMinusOneTorsionSubgroupPoint.2]
    exact add_zero _
  · apply cmExplicitHalfPoint_double hcurve
  · exact cmAlgClosure_affine_ne_neg_self_of_y_ne_zero hcurve hy

/-- Four-row finite table in the repository's literal `(Z/2)^2` orientation.
The nontrivial rows are `(1,0) ↦ (0,0)`, `(0,1) ↦ (1,0)`, and
`(1,1) ↦ (-1,0)`. -/
theorem cmExplicitHalf_even_sign_E2_table :
    (cmAlgClosureTwoTorsionEquiv (0, 0) = 0) ∧
    (cmAlgClosureTwoTorsionEquiv (1, 0) = actualZeroTorsionSubgroupPoint) ∧
    (cmAlgClosureTwoTorsionEquiv (0, 1) = actualOneTorsionSubgroupPoint) ∧
    (cmAlgClosureTwoTorsionEquiv (1, 1) = actualMinusOneTorsionSubgroupPoint) := by
  simp

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* an explicit selected half on the actual Qbar elliptic group;
* exact doubling of that half;
* full x-representative translation formulas for all three nonzero E[2] points;
* point equality, not only x-coordinate equality, for all three even root-sign
  flips under the non-torsion affine hypothesis `y ≠ 0`;
* the literal four-row `(Z/2)^2` orientation table.

The remaining global comparison is no longer an E[2]-identification problem.
It is the Galois-character packaging step: apply this table to the action of
`σ` on the chosen square roots, then include the four rational two-torsion
boundary points already handled by `totalGlobalKummer`.
-/

end

end Synthesis.Millennium.BSD
