import Synthesis.MillenniumBSDCMRootSignDifferenceExact
import Synthesis.MillenniumBSDCMGeometricKummerContinuousH1Exact
import Synthesis.MillenniumBSDCMRationalToGeometricKummerExact
import Mathlib.Tactic

/-!
# Selected CM curve: the explicit half produces the raw x-T Kummer character

The finite arithmetic theorem now computes the custom Qbar difference

  σQ-Q = E2Equiv(KummerBit(x-1), KummerBit(x)).

This owner inserts that *same* explicit half into the generic
`GeometricHalfData` carrier and follows the already-existing same-object
point/E[2] equivalences used by `cmGeometricKummerTrivialCharacter`.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

/-- The explicit algebraic-closure half, viewed as the exact geometric half of
the embedded rational point. -/
noncomputable def cmExplicitRationalGeometricHalfData
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    {a b c : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1)
    (hc : c ^ 2 = (x : RatAlgClosure) + 1)
    (habc : a * b * c = -(y : RatAlgClosure)) :
    GeometricHalfData cmWeierstrass
      (cmRationalGeometricPoint (.affine x y hcurve)) where
  half := cmAlgClosurePointAddEquivMathlib
    (cmExplicitHalfPoint (x : RatAlgClosure) (y : RatAlgClosure)
      a b c ha hb hc habc)
  double_half := by
    change (2 : ℕ) • cmAlgClosurePointAddEquivMathlib
        (cmExplicitHalfPoint (x : RatAlgClosure) (y : RatAlgClosure)
          a b c ha hb hc habc) =
      cmAlgClosurePointEquivMathlib
        (cmRationalPointToAlgClosure (.affine x y hcurve))
    rw [← map_nsmul]
    have hcurve' :
        (y : RatAlgClosure) ^ 2 =
          (x : RatAlgClosure) ^ 3 - (x : RatAlgClosure) := by
      exact_mod_cast hcurve
    rw [cmExplicitHalfPoint_double hcurve' ha hb hc habc]
    rfl

/-- On the explicit half, the generic geometric character transported back to
`(Z/2)^2` is literally the paid scalar Kummer bit pair in raw geometric order. -/
theorem cmExplicitRationalGeometricHalf_trivialCharacter_apply
    (σ : RationalAbsoluteGalois)
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    {a b c : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1)
    (hc : c ^ 2 = (x : RatAlgClosure) + 1)
    (habc : a * b * c = -(y : RatAlgClosure)) :
    Multiplicative.toAdd
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed (.affine x y hcurve))
        (cmExplicitRationalGeometricHalfData hcurve ha hb hc habc) σ) =
      (rationalKummerBit ⟨x - 1, sub_ne_zero.mpr hx1⟩ σ,
        rationalKummerBit ⟨x, hx0⟩ σ) := by
  let Qc : CMAlgClosureProjectivePoint :=
    cmExplicitHalfPoint (x : RatAlgClosure) (y : RatAlgClosure)
      a b c ha hb hc habc
  let bits : CMTwoTorsionCarrier :=
    (rationalKummerBit ⟨x - 1, sub_ne_zero.mpr hx1⟩ σ,
      rationalKummerBit ⟨x, hx0⟩ σ)
  apply cmAlgClosureTwoTorsionEquiv.injective
  apply Subtype.ext
  change cmAlgClosurePointAddEquivMathlib.symm
      (galoisPointMap cmWeierstrass σ
          (cmAlgClosurePointAddEquivMathlib Qc) -
        cmAlgClosurePointAddEquivMathlib Qc) =
    (cmAlgClosureTwoTorsionEquiv bits).1
  rw [map_sub]
  have hcomm := cmAlgClosurePointEquiv_galoisAction σ Qc
  change cmAlgClosurePointAddEquivMathlib
      (cmAlgClosureGaloisAction σ Qc) =
    galoisPointMap cmWeierstrass σ
      (cmAlgClosurePointAddEquivMathlib Qc) at hcomm
  rw [← hcomm]
  simp only [AddEquiv.symm_apply_apply]
  change cmAlgClosureGaloisAction σ Qc - Qc =
    (cmAlgClosureTwoTorsionEquiv bits).1
  dsimp [Qc, bits]
  exact cmExplicitHalf_galoisDifference_eq_paidKummerBits
    σ hcurve hy0 hx0 hx1 ha hb hc habc

/-- Therefore the two scalar characters obtained from the literal geometric
Kummer character are exactly `(χ_{x-1}, χ_x)`. -/
theorem cmExplicitRationalGeometricHalf_characterPair
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    {a b c : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1)
    (hc : c ^ 2 = (x : RatAlgClosure) + 1)
    (habc : a * b * c = -(y : RatAlgClosure)) :
    cmTwoTorsionContinuousCharacterMulEquivPair
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed (.affine x y hcurve))
        (cmExplicitRationalGeometricHalfData hcurve ha hb hc habc)) =
      cmRawGeometricQuadraticCharacterPair x hx0 hx1 := by
  apply Prod.ext
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmExplicitRationalGeometricHalf_trivialCharacter_apply
      σ hcurve hy0 hx0 hx1 ha hb hc habc
    exact congrArg Prod.fst h
  · apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    have h := cmExplicitRationalGeometricHalf_trivialCharacter_apply
      σ hcurve hy0 hx0 hx1 ha hb hc habc
    exact congrArg Prod.snd h

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the explicit Qbar half is a literal `GeometricHalfData` for the embedded
  rational point;
* the generic point action transported through the already-paid same-object
  E[2] equivalences reduces to the custom σQ-Q calculation;
* the resulting trivial-E[2] character pair is exactly `(χ_{x-1},χ_x)`.

Combined with `MillenniumBSDCMGlobalKummerCharacterCompilerExact`, this pays
the ordinary non-two-torsion raw orientation theorem.  Half-choice
independence then transfers the result to the repository's canonical chosen
geometric half.  The only global cases not covered here are infinity and the
three rational two-torsion boundary points.
-/

end

end Synthesis.Millennium.BSD
