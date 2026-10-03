import Synthesis.MillenniumBSDCMQuarterPointTransportExact
import Synthesis.MillenniumBSDCMGlobalKummerBoundaryCompilerExact
import Synthesis.MillenniumBSDRationalQuadraticKummerHom
import Mathlib.Tactic

/-!
# Selected CM curve: explicit quarter-point boundary cases

The remaining global points are O, (0,0), (1,0), and (-1,0).  We choose
literal Qbar halves using the canonical scalar Kummer roots:

* sqrt(-1) for (0,0);
* sqrt(2) for (1,0);
* sqrt(-1) and sqrt(-2) for (-1,0).

For a conjugated half we identify `σQ-Q` by its actual Mathlib x-coordinate.
`Point.xRep_sub_of_X_ne` computes that coordinate directly.  Since the target
is a literal E[2] point and every E[2] point is self-negative, the usual
`xRep = xRep ↔ P=Q ∨ P=-Q` ambiguity collapses to exact equality.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

------------------------------------------------------------------------
-- Canonical radicals used by the finite boundary.
------------------------------------------------------------------------

noncomputable abbrev cmSqrtNegOne : RatAlgClosure :=
  rationalKummerRoot negOneNZ

noncomputable abbrev cmSqrtTwo : RatAlgClosure :=
  rationalKummerRoot twoNZ

noncomputable abbrev cmSqrtNegTwo : RatAlgClosure :=
  rationalKummerRoot negTwoNZ

@[simp] theorem cmSqrtNegOne_sq : cmSqrtNegOne ^ 2 = (-1 : RatAlgClosure) := by
  have h := rationalKummerRoot_spec negOneNZ
  simpa [cmSqrtNegOne, negOneNZ, pow_two] using h

@[simp] theorem cmSqrtTwo_sq : cmSqrtTwo ^ 2 = (2 : RatAlgClosure) := by
  have h := rationalKummerRoot_spec twoNZ
  simpa [cmSqrtTwo, twoNZ, pow_two] using h

@[simp] theorem cmSqrtNegTwo_sq : cmSqrtNegTwo ^ 2 = (-2 : RatAlgClosure) := by
  have h := rationalKummerRoot_spec negTwoNZ
  simpa [cmSqrtNegTwo, negTwoNZ, pow_two] using h

@[simp] theorem cmSqrtNegOne_ne_zero : cmSqrtNegOne ≠ 0 :=
  rationalKummerRoot_ne_zero negOneNZ

@[simp] theorem cmSqrtTwo_ne_zero : cmSqrtTwo ≠ 0 :=
  rationalKummerRoot_ne_zero twoNZ

@[simp] theorem cmSqrtNegTwo_ne_zero : cmSqrtNegTwo ≠ 0 :=
  rationalKummerRoot_ne_zero negTwoNZ

------------------------------------------------------------------------
-- A tiny xRep-to-E[2] eliminator.
------------------------------------------------------------------------

private theorem customPoint_eq_twoTorsion_of_xRep_eq
    (D : CMAlgClosureProjectivePoint)
    (T : cmAlgClosureTwoTorsionSubgroup)
    (hx :
      (cmAlgClosurePointAddEquivMathlib D).xRep =
        (cmAlgClosurePointAddEquivMathlib T.1).xRep) :
    D = T.1 := by
  rcases WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff.mp hx with h | h
  · exact cmAlgClosurePointAddEquivMathlib.injective h
  · have hself : -T.1 = T.1 := by
      apply neg_eq_iff_add_eq_zero.mpr
      change T.1 + T.1 = 0
      simpa [two_nsmul] using T.2
    apply cmAlgClosurePointAddEquivMathlib.injective
    simpa [← cmAlgClosurePointAddEquivMathlib.map_neg, hself] using h

------------------------------------------------------------------------
-- (0,0): Q = half(0,0; 0,sqrt(-1),1).
------------------------------------------------------------------------

noncomputable def cmZeroQuarterPoint : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint 0 0 0 cmSqrtNegOne 1
    (by norm_num)
    (by simpa using cmSqrtNegOne_sq)
    (by norm_num)
    (by ring)

noncomputable def cmZeroQuarterPointConjugate : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint 0 0 0 (-cmSqrtNegOne) 1
    (by norm_num)
    (by simpa using cmSqrtNegOne_sq)
    (by norm_num)
    (by ring)

@[simp] theorem cmZeroQuarterPoint_double :
    (2 : ℕ) • cmZeroQuarterPoint =
      cmRationalPointToAlgClosure rationalZeroTorsionPoint := by
  have h := cmExplicitHalfPoint_double
    (x := (0 : RatAlgClosure)) (y := 0)
    (a := 0) (b := cmSqrtNegOne) (c := 1)
    (by norm_num)
    (by norm_num)
    (by simpa using cmSqrtNegOne_sq)
    (by norm_num)
    (by ring)
  simpa [cmZeroQuarterPoint, rationalZeroTorsionPoint,
    cmRationalPointToAlgClosure] using h

private theorem cmZeroQuarterPointConjugate_sub :
    cmZeroQuarterPointConjugate - cmZeroQuarterPoint =
      actualMinusOneTorsionSubgroupPoint.1 := by
  apply customPoint_eq_twoTorsion_of_xRep_eq
    (cmZeroQuarterPointConjugate - cmZeroQuarterPoint)
    actualMinusOneTorsionSubgroupPoint
  rw [cmAlgClosurePointAddEquivMathlib.map_sub]
  change
    (WeierstrassCurve.Affine.Point.some
        (-cmSqrtNegOne) (1 + cmSqrtNegOne) _ -
      WeierstrassCurve.Affine.Point.some
        cmSqrtNegOne (1 - cmSqrtNegOne) _).xRep =
      (WeierstrassCurve.Affine.Point.some (-1) 0 _).xRep
  have hne : -cmSqrtNegOne ≠ cmSqrtNegOne := by
    intro h
    exact cmSqrtNegOne_ne_zero ((CharZero.neg_eq_self_iff).mp h)
  rw [WeierstrassCurve.Affine.Point.xRep_sub_of_X_ne _ _ hne]
  simp only [WeierstrassCurve.Affine.Point.xRep_some]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  field_simp [cmSqrtNegOne_ne_zero]
  linear_combination 4 * cmSqrtNegOne_sq

private theorem cmZeroQuarterPoint_galoisDifference
    (σ : RationalAbsoluteGalois) :
    cmAlgClosureGaloisAction σ cmZeroQuarterPoint - cmZeroQuarterPoint =
      (cmAlgClosureTwoTorsionEquiv
        (rationalKummerBit negOneNZ σ,
          rationalKummerBit negOneNZ σ)).1 := by
  rcases galois_kummerRoot_eq_or_neg negOneNZ σ with hfix | hneg
  · have hk : rationalKummerBit negOneNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff negOneNZ σ).2 hfix
    have hQ : cmAlgClosureGaloisAction σ cmZeroQuarterPoint =
        cmZeroQuarterPoint := by
      simp [cmZeroQuarterPoint, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY, cmAlgClosureGaloisAction, hfix]
    rw [hQ, sub_self, hk]
    simp
  · have hk : rationalKummerBit negOneNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff negOneNZ σ).2 hneg
    have hQ : cmAlgClosureGaloisAction σ cmZeroQuarterPoint =
        cmZeroQuarterPointConjugate := by
      simp [cmZeroQuarterPoint, cmZeroQuarterPointConjugate,
        cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY,
        cmAlgClosureGaloisAction, hneg]
    rw [hQ, hk]
    simpa using cmZeroQuarterPointConjugate_sub

------------------------------------------------------------------------
-- (1,0): Q = half(1,0; 1,0,sqrt(2)).
------------------------------------------------------------------------

noncomputable def cmOneQuarterPoint : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint 1 0 1 0 cmSqrtTwo
    (by norm_num)
    (by norm_num)
    (by simpa using cmSqrtTwo_sq)
    (by ring)

noncomputable def cmOneQuarterPointConjugate : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint 1 0 1 0 (-cmSqrtTwo)
    (by norm_num)
    (by norm_num)
    (by simpa using cmSqrtTwo_sq)
    (by ring)

@[simp] theorem cmOneQuarterPoint_double :
    (2 : ℕ) • cmOneQuarterPoint =
      cmRationalPointToAlgClosure rationalOneTorsionPoint := by
  have h := cmExplicitHalfPoint_double
    (x := (1 : RatAlgClosure)) (y := 0)
    (a := 1) (b := 0) (c := cmSqrtTwo)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by simpa using cmSqrtTwo_sq)
    (by ring)
  simpa [cmOneQuarterPoint, rationalOneTorsionPoint,
    cmRationalPointToAlgClosure] using h

private theorem cmOneQuarterPointConjugate_sub :
    cmOneQuarterPointConjugate - cmOneQuarterPoint =
      actualZeroTorsionSubgroupPoint.1 := by
  apply customPoint_eq_twoTorsion_of_xRep_eq
    (cmOneQuarterPointConjugate - cmOneQuarterPoint)
    actualZeroTorsionSubgroupPoint
  rw [cmAlgClosurePointAddEquivMathlib.map_sub]
  change
    (WeierstrassCurve.Affine.Point.some
        (1 - cmSqrtTwo) (cmSqrtTwo - 2) _ -
      WeierstrassCurve.Affine.Point.some
        (1 + cmSqrtTwo) (-cmSqrtTwo - 2) _).xRep =
      (WeierstrassCurve.Affine.Point.some 0 0 _).xRep
  have hne : 1 - cmSqrtTwo ≠ 1 + cmSqrtTwo := by
    intro h
    have : (2 : RatAlgClosure) * cmSqrtTwo = 0 := by linear_combination h
    exact cmSqrtTwo_ne_zero (mul_eq_zero.mp this |>.resolve_left (by norm_num))
  rw [WeierstrassCurve.Affine.Point.xRep_sub_of_X_ne _ _ hne]
  simp only [WeierstrassCurve.Affine.Point.xRep_some]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  field_simp [cmSqrtTwo_ne_zero]
  linear_combination 8 * cmSqrtTwo_sq

private theorem cmOneQuarterPoint_galoisDifference
    (σ : RationalAbsoluteGalois) :
    cmAlgClosureGaloisAction σ cmOneQuarterPoint - cmOneQuarterPoint =
      (cmAlgClosureTwoTorsionEquiv
        (rationalKummerBit twoNZ σ, 0)).1 := by
  rcases galois_kummerRoot_eq_or_neg twoNZ σ with hfix | hneg
  · have hk : rationalKummerBit twoNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff twoNZ σ).2 hfix
    have hQ : cmAlgClosureGaloisAction σ cmOneQuarterPoint =
        cmOneQuarterPoint := by
      simp [cmOneQuarterPoint, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY, cmAlgClosureGaloisAction, hfix]
    rw [hQ, sub_self, hk]
    simp
  · have hk : rationalKummerBit twoNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff twoNZ σ).2 hneg
    have hQ : cmAlgClosureGaloisAction σ cmOneQuarterPoint =
        cmOneQuarterPointConjugate := by
      simp [cmOneQuarterPoint, cmOneQuarterPointConjugate,
        cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY,
        cmAlgClosureGaloisAction, hneg]
    rw [hQ, hk]
    simpa using cmOneQuarterPointConjugate_sub

------------------------------------------------------------------------
-- (-1,0): Q = half(-1,0; sqrt(-1),sqrt(-2),0).
------------------------------------------------------------------------

noncomputable def cmMinusOneQuarterPoint : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint (-1) 0 cmSqrtNegOne cmSqrtNegTwo 0
    (by simpa using cmSqrtNegOne_sq)
    (by simpa using cmSqrtNegTwo_sq)
    (by norm_num)
    (by ring)

noncomputable def cmMinusOneQuarterPointFlipB : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint (-1) 0 cmSqrtNegOne (-cmSqrtNegTwo) 0
    (by simpa using cmSqrtNegOne_sq)
    (by simpa using cmSqrtNegTwo_sq)
    (by norm_num)
    (by ring)

noncomputable def cmMinusOneQuarterPointFlipA : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint (-1) 0 (-cmSqrtNegOne) cmSqrtNegTwo 0
    (by simpa using cmSqrtNegOne_sq)
    (by simpa using cmSqrtNegTwo_sq)
    (by norm_num)
    (by ring)

noncomputable def cmMinusOneQuarterPointFlipAB : CMAlgClosureProjectivePoint :=
  cmExplicitHalfPoint (-1) 0 (-cmSqrtNegOne) (-cmSqrtNegTwo) 0
    (by simpa using cmSqrtNegOne_sq)
    (by simpa using cmSqrtNegTwo_sq)
    (by norm_num)
    (by ring)

@[simp] theorem cmMinusOneQuarterPoint_double :
    (2 : ℕ) • cmMinusOneQuarterPoint =
      cmRationalPointToAlgClosure rationalMinusOneTorsionPoint := by
  have h := cmExplicitHalfPoint_double
    (x := (-1 : RatAlgClosure)) (y := 0)
    (a := cmSqrtNegOne) (b := cmSqrtNegTwo) (c := 0)
    (by norm_num)
    (by simpa using cmSqrtNegOne_sq)
    (by simpa using cmSqrtNegTwo_sq)
    (by norm_num)
    (by ring)
  simpa [cmMinusOneQuarterPoint, rationalMinusOneTorsionPoint,
    cmRationalPointToAlgClosure] using h

private theorem cmMinusOneQuarterPointFlipB_sub :
    cmMinusOneQuarterPointFlipB - cmMinusOneQuarterPoint =
      actualZeroTorsionSubgroupPoint.1 := by
  apply customPoint_eq_twoTorsion_of_xRep_eq
    (cmMinusOneQuarterPointFlipB - cmMinusOneQuarterPoint)
    actualZeroTorsionSubgroupPoint
  rw [cmAlgClosurePointAddEquivMathlib.map_sub]
  let d : RatAlgClosure := cmSqrtNegOne * cmSqrtNegTwo
  have hd0 : d ≠ 0 := mul_ne_zero cmSqrtNegOne_ne_zero cmSqrtNegTwo_ne_zero
  change
    (WeierstrassCurve.Affine.Point.some
        (-1 - d) (-cmSqrtNegTwo + 2 * cmSqrtNegOne) _ -
      WeierstrassCurve.Affine.Point.some
        (-1 + d) (cmSqrtNegTwo + 2 * cmSqrtNegOne) _).xRep =
      (WeierstrassCurve.Affine.Point.some 0 0 _).xRep
  have hne : -1 - d ≠ -1 + d := by
    intro h
    have : (2 : RatAlgClosure) * d = 0 := by linear_combination h
    exact hd0 (mul_eq_zero.mp this |>.resolve_left (by norm_num))
  rw [WeierstrassCurve.Affine.Point.xRep_sub_of_X_ne _ _ hne]
  simp only [WeierstrassCurve.Affine.Point.xRep_some]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  dsimp [d]
  field_simp [cmSqrtNegOne_ne_zero, cmSqrtNegTwo_ne_zero]
  ring_nf
  rw [cmSqrtNegOne_sq, cmSqrtNegTwo_sq]
  norm_num

private theorem cmMinusOneQuarterPointFlipA_sub :
    cmMinusOneQuarterPointFlipA - cmMinusOneQuarterPoint =
      actualOneTorsionSubgroupPoint.1 := by
  apply customPoint_eq_twoTorsion_of_xRep_eq
    (cmMinusOneQuarterPointFlipA - cmMinusOneQuarterPoint)
    actualOneTorsionSubgroupPoint
  rw [cmAlgClosurePointAddEquivMathlib.map_sub]
  let d : RatAlgClosure := cmSqrtNegOne * cmSqrtNegTwo
  have hd0 : d ≠ 0 := mul_ne_zero cmSqrtNegOne_ne_zero cmSqrtNegTwo_ne_zero
  change
    (WeierstrassCurve.Affine.Point.some
        (-1 - d) (cmSqrtNegTwo - 2 * cmSqrtNegOne) _ -
      WeierstrassCurve.Affine.Point.some
        (-1 + d) (cmSqrtNegTwo + 2 * cmSqrtNegOne) _).xRep =
      (WeierstrassCurve.Affine.Point.some 1 0 _).xRep
  have hne : -1 - d ≠ -1 + d := by
    intro h
    have : (2 : RatAlgClosure) * d = 0 := by linear_combination h
    exact hd0 (mul_eq_zero.mp this |>.resolve_left (by norm_num))
  rw [WeierstrassCurve.Affine.Point.xRep_sub_of_X_ne _ _ hne]
  simp only [WeierstrassCurve.Affine.Point.xRep_some]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  dsimp [d]
  field_simp [cmSqrtNegOne_ne_zero, cmSqrtNegTwo_ne_zero]
  ring_nf
  rw [cmSqrtNegOne_sq, cmSqrtNegTwo_sq]
  norm_num

private theorem cmMinusOneQuarterPointFlipAB_sub :
    cmMinusOneQuarterPointFlipAB - cmMinusOneQuarterPoint =
      actualMinusOneTorsionSubgroupPoint.1 := by
  have hneg : cmMinusOneQuarterPointFlipAB = -cmMinusOneQuarterPoint := by
    rw [cmAlgClosure_neg_affine]
    simp [cmMinusOneQuarterPoint, cmMinusOneQuarterPointFlipAB,
      cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY]
  rw [hneg]
  have hdouble := cmMinusOneQuarterPoint_double
  have ht :
      cmRationalPointToAlgClosure rationalMinusOneTorsionPoint =
        actualMinusOneTorsionSubgroupPoint.1 := by
    rfl
  rw [← ht, ← hdouble]
  abel

private theorem cmMinusOneQuarterPoint_galoisDifference
    (σ : RationalAbsoluteGalois) :
    cmAlgClosureGaloisAction σ cmMinusOneQuarterPoint - cmMinusOneQuarterPoint =
      (cmAlgClosureTwoTorsionEquiv
        (rationalKummerBit negTwoNZ σ,
          rationalKummerBit negOneNZ σ)).1 := by
  rcases galois_kummerRoot_eq_or_neg negOneNZ σ with haFix | haNeg <;>
  rcases galois_kummerRoot_eq_or_neg negTwoNZ σ with hbFix | hbNeg
  · have haBit : rationalKummerBit negOneNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff negOneNZ σ).2 haFix
    have hbBit : rationalKummerBit negTwoNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff negTwoNZ σ).2 hbFix
    have hQ : cmAlgClosureGaloisAction σ cmMinusOneQuarterPoint =
        cmMinusOneQuarterPoint := by
      simp [cmMinusOneQuarterPoint, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY, cmAlgClosureGaloisAction,
        haFix, hbFix]
    rw [hQ, sub_self, haBit, hbBit]
    simp
  · have haBit : rationalKummerBit negOneNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff negOneNZ σ).2 haFix
    have hbBit : rationalKummerBit negTwoNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff negTwoNZ σ).2 hbNeg
    have hQ : cmAlgClosureGaloisAction σ cmMinusOneQuarterPoint =
        cmMinusOneQuarterPointFlipB := by
      simp [cmMinusOneQuarterPoint, cmMinusOneQuarterPointFlipB,
        cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY,
        cmAlgClosureGaloisAction, haFix, hbNeg]
    rw [hQ, haBit, hbBit]
    simpa using cmMinusOneQuarterPointFlipB_sub
  · have haBit : rationalKummerBit negOneNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff negOneNZ σ).2 haNeg
    have hbBit : rationalKummerBit negTwoNZ σ = 0 :=
      (rationalKummerBit_eq_zero_iff negTwoNZ σ).2 hbFix
    have hQ : cmAlgClosureGaloisAction σ cmMinusOneQuarterPoint =
        cmMinusOneQuarterPointFlipA := by
      simp [cmMinusOneQuarterPoint, cmMinusOneQuarterPointFlipA,
        cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY,
        cmAlgClosureGaloisAction, haNeg, hbFix]
    rw [hQ, haBit, hbBit]
    simpa using cmMinusOneQuarterPointFlipA_sub
  · have haBit : rationalKummerBit negOneNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff negOneNZ σ).2 haNeg
    have hbBit : rationalKummerBit negTwoNZ σ = 1 :=
      (rationalKummerBit_eq_one_iff negTwoNZ σ).2 hbNeg
    have hQ : cmAlgClosureGaloisAction σ cmMinusOneQuarterPoint =
        cmMinusOneQuarterPointFlipAB := by
      simp [cmMinusOneQuarterPoint, cmMinusOneQuarterPointFlipAB,
        cmExplicitHalfPoint, algClosureHalfX, algClosureHalfY,
        cmAlgClosureGaloisAction, haNeg, hbNeg]
    rw [hQ, haBit, hbBit]
    simpa using cmMinusOneQuarterPointFlipAB_sub

------------------------------------------------------------------------
-- Character-pair packaging.
------------------------------------------------------------------------

private theorem cmZeroQuarterPoint_characterPair :
    cmTwoTorsionContinuousCharacterMulEquivPair
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed rationalZeroTorsionPoint)
        (cmCustomRationalGeometricHalfData rationalZeroTorsionPoint
          cmZeroQuarterPoint cmZeroQuarterPoint_double)) =
      (rationalQuadraticKummerCharacter negOneNZ,
        rationalQuadraticKummerCharacter negOneNZ) := by
  apply Prod.ext
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalZeroTorsionPoint cmZeroQuarterPoint cmZeroQuarterPoint_double σ
      (rationalKummerBit negOneNZ σ, rationalKummerBit negOneNZ σ)
      (cmZeroQuarterPoint_galoisDifference σ)
    exact congrArg Prod.fst h
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalZeroTorsionPoint cmZeroQuarterPoint cmZeroQuarterPoint_double σ
      (rationalKummerBit negOneNZ σ, rationalKummerBit negOneNZ σ)
      (cmZeroQuarterPoint_galoisDifference σ)
    exact congrArg Prod.snd h

private theorem cmOneQuarterPoint_characterPair :
    cmTwoTorsionContinuousCharacterMulEquivPair
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed rationalOneTorsionPoint)
        (cmCustomRationalGeometricHalfData rationalOneTorsionPoint
          cmOneQuarterPoint cmOneQuarterPoint_double)) =
      (rationalQuadraticKummerCharacter twoNZ,
        rationalQuadraticKummerCharacter nzRatOne) := by
  apply Prod.ext
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalOneTorsionPoint cmOneQuarterPoint cmOneQuarterPoint_double σ
      (rationalKummerBit twoNZ σ, 0)
      (cmOneQuarterPoint_galoisDifference σ)
    exact congrArg Prod.fst h
  · rw [rationalQuadraticKummerCharacter_one]
    apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalOneTorsionPoint cmOneQuarterPoint cmOneQuarterPoint_double σ
      (rationalKummerBit twoNZ σ, 0)
      (cmOneQuarterPoint_galoisDifference σ)
    simpa using congrArg Prod.snd h

private theorem cmMinusOneQuarterPoint_characterPair :
    cmTwoTorsionContinuousCharacterMulEquivPair
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed rationalMinusOneTorsionPoint)
        (cmCustomRationalGeometricHalfData rationalMinusOneTorsionPoint
          cmMinusOneQuarterPoint cmMinusOneQuarterPoint_double)) =
      (rationalQuadraticKummerCharacter negTwoNZ,
        rationalQuadraticKummerCharacter negOneNZ) := by
  apply Prod.ext
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalMinusOneTorsionPoint cmMinusOneQuarterPoint
      cmMinusOneQuarterPoint_double σ
      (rationalKummerBit negTwoNZ σ, rationalKummerBit negOneNZ σ)
      (cmMinusOneQuarterPoint_galoisDifference σ)
    exact congrArg Prod.fst h
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
      rationalMinusOneTorsionPoint cmMinusOneQuarterPoint
      cmMinusOneQuarterPoint_double σ
      (rationalKummerBit negTwoNZ σ, rationalKummerBit negOneNZ σ)
      (cmMinusOneQuarterPoint_galoisDifference σ)
    exact congrArg Prod.snd h

private theorem characterPair_to_repoSquareClasses
    (a b : NonzeroRat) :
    quadraticCharacterPairMulEquivRatSquareClasses
      (rationalQuadraticKummerCharacter a,
        rationalQuadraticKummerCharacter b) =
      (squareClassOf a, squareClassOf b) := by
  apply ratSquareClassPairMulEquivQuadraticCharacters.injective
  simp [ratSquareClassPairMulEquivQuadraticCharacters,
    rationalQuadraticKummerCharacterPairMulEquiv,
    rationalQuadraticKummerCharacterMulEquiv,
    rationalSquareClassKummerHom_mk]

------------------------------------------------------------------------
-- The three nonzero finite boundary equalities.
------------------------------------------------------------------------

theorem cmRationalCohomologicalKummer_zeroTorsion_boundary :
    cmRationalCohomologicalKummerSquareClass rationalZeroTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalZeroTorsionPoint) := by
  rw [cmRationalCohomologicalKummerSquareClass_eq_of_custom_characterPair
    rationalZeroTorsionPoint cmZeroQuarterPoint cmZeroQuarterPoint_double
    (rationalQuadraticKummerCharacter negOneNZ,
      rationalQuadraticKummerCharacter negOneNZ)
    cmZeroQuarterPoint_characterPair]
  rw [characterPair_to_repoSquareClasses]
  simp [rationalZeroTorsionPoint, totalGlobalKummer, torsionKummer,
    ratSquareClassPairSwap]

theorem cmRationalCohomologicalKummer_oneTorsion_boundary :
    cmRationalCohomologicalKummerSquareClass rationalOneTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalOneTorsionPoint) := by
  rw [cmRationalCohomologicalKummerSquareClass_eq_of_custom_characterPair
    rationalOneTorsionPoint cmOneQuarterPoint cmOneQuarterPoint_double
    (rationalQuadraticKummerCharacter twoNZ,
      rationalQuadraticKummerCharacter nzRatOne)
    cmOneQuarterPoint_characterPair]
  rw [characterPair_to_repoSquareClasses]
  simp [rationalOneTorsionPoint, totalGlobalKummer, torsionKummer,
    ratSquareClassPairSwap]

theorem cmRationalCohomologicalKummer_minusOneTorsion_boundary :
    cmRationalCohomologicalKummerSquareClass rationalMinusOneTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalMinusOneTorsionPoint) := by
  rw [cmRationalCohomologicalKummerSquareClass_eq_of_custom_characterPair
    rationalMinusOneTorsionPoint cmMinusOneQuarterPoint
    cmMinusOneQuarterPoint_double
    (rationalQuadraticKummerCharacter negTwoNZ,
      rationalQuadraticKummerCharacter negOneNZ)
    cmMinusOneQuarterPoint_characterPair]
  rw [characterPair_to_repoSquareClasses]
  simp [rationalMinusOneTorsionPoint, totalGlobalKummer, torsionKummer,
    ordinaryKummer, minusOnePoint, ratSquareClassPairSwap]

------------------------------------------------------------------------
-- Infinity uses the literal zero half.
------------------------------------------------------------------------

theorem cmRationalCohomologicalKummer_infinity_boundary :
    cmRationalCohomologicalKummerSquareClass
        (.infinity : RationalProjectivePoint) =
      ratSquareClassPairSwap
        (totalGlobalKummer (.infinity : RationalProjectivePoint)) := by
  let Q : CMAlgClosureProjectivePoint := 0
  have hdouble :
      (2 : ℕ) • Q =
        cmRationalPointToAlgClosure (.infinity : RationalProjectivePoint) := by
    simp [Q, cmRationalPointToAlgClosure, cmAlgClosure_zero_eq_infinity]
  have hchar :
      cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter
          (cmRationalGeometricPoint_isGaloisFixed
            (.infinity : RationalProjectivePoint))
          (cmCustomRationalGeometricHalfData
            (.infinity : RationalProjectivePoint) Q hdouble)) =
        (1, 1) := by
    apply Prod.ext
    · apply ContinuousMonoidHom.ext
      intro σ
      apply Multiplicative.toAdd_injective
      have hdiff : cmAlgClosureGaloisAction σ Q - Q =
          (cmAlgClosureTwoTorsionEquiv (0, 0)).1 := by
        simp [Q, cmAlgClosureGaloisAction]
      have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
        (.infinity : RationalProjectivePoint) Q hdouble σ (0, 0) hdiff
      simpa using congrArg Prod.fst h
    · apply ContinuousMonoidHom.ext
      intro σ
      apply Multiplicative.toAdd_injective
      have hdiff : cmAlgClosureGaloisAction σ Q - Q =
          (cmAlgClosureTwoTorsionEquiv (0, 0)).1 := by
        simp [Q, cmAlgClosureGaloisAction]
      have h := cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
        (.infinity : RationalProjectivePoint) Q hdouble σ (0, 0) hdiff
      simpa using congrArg Prod.snd h
  rw [cmRationalCohomologicalKummerSquareClass_eq_of_custom_characterPair
    (.infinity : RationalProjectivePoint) Q hdouble (1, 1) hchar]
  simp [totalGlobalKummer, torsionKummer, ratSquareClassPairSwap]

/-- All four finite boundary fields are now inhabited. -/
theorem cmGeometricXTKummerFiniteBoundary_paid :
    CMGeometricXTKummerFiniteBoundary where
  infinity := cmRationalCohomologicalKummer_infinity_boundary
  zeroTorsion := cmRationalCohomologicalKummer_zeroTorsion_boundary
  oneTorsion := cmRationalCohomologicalKummer_oneTorsion_boundary
  minusOneTorsion := cmRationalCohomologicalKummer_minusOneTorsion_boundary

/-- Full selected-curve raw geometric/x-T orientation theorem. -/
theorem cmGeometricXTKummerOrientation_paid :
    CMGeometricXTKummerOrientationTheorem :=
  cmGeometricXTKummerOrientation_of_finiteBoundary
    cmGeometricXTKummerFiniteBoundary_paid

/-- Full selected-curve geometric Kummer equality in x-T order. -/
theorem cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_paid
    (P : RationalProjectivePoint) :
    cmRationalCohomologicalKummerXTSquareClass P = totalGlobalKummer P :=
  cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_of_finiteBoundary
    cmGeometricXTKummerFiniteBoundary_paid P

/-!
MAX-CUT STATUS

SUBJECT TO EXACT-HEAD LEAN CERTIFICATION, THE SELECTED-CURVE GLOBAL KUMMER
COMPARISON IS CLOSED:

  forall P : E(Q), delta_geom^raw(P) = swap(delta_x-T(P)),

and therefore the x-T-oriented geometric Kummer map equals the repository's
literal `totalGlobalKummer` on every rational point.

The next arithmetic theorem is local scalar Kummer compatibility at each
place.  No additional global Kummer/H¹ architecture is required.
-/

end

end Synthesis.Millennium.BSD
