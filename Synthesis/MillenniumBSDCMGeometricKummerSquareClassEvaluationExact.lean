import Synthesis.MillenniumBSDCMExplicitGeometricHalfCharacterExact
import Synthesis.MillenniumBSDCMGenericE2H1SquareClassExact
import Mathlib.Tactic

/-!
# Selected CM curve: evaluate the paid H¹/square-class equivalence on a geometric Kummer class

All arithmetic has already been reduced to the underlying continuous E[2]
character.  This owner records the coherence of the repository's existing map
stack: generic E[2] H¹ -> actual E[2] H¹ -> trivial E[2] H¹ -> continuous
character -> two scalar characters -> square classes.
-/

namespace Synthesis.Millennium.BSD

open BSDCohomology

noncomputable section

/-- The generic geometric H¹ class evaluates under the paid square-class
comparison exactly by splitting its underlying trivial-E[2] character and then
applying the paid scalar quadratic Kummer inverse. -/
theorem cmGeometricKummerGenericE2H1_squareClass_evaluation
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    cmGenericKummerE2H1MulEquivRatSquareClasses
        (Multiplicative.ofAdd (cmGeometricKummerGenericE2H1 hP Q)) =
      quadraticCharacterPairMulEquivRatSquareClasses
        (cmTwoTorsionContinuousCharacterMulEquivPair
          (cmGeometricKummerTrivialCharacter hP Q)) := by
  change
    quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmTrivialE2H1ContinuousHomMulEquiv
          (Multiplicative.ofAdd
            (cmActualE2H1ToTrivial
              (cmGenericKummerE2H1ToActual
                (cmActualE2H1ToGenericKummer
                  (cmE2H1ToActual
                    (cmGeometricKummerTrivialH1 hP Q)))))))) = _
  have hgeneric := congrArg
    (fun f => f (cmE2H1ToActual (cmGeometricKummerTrivialH1 hP Q)))
    cmGenericKummerE2H1_maps_inverse_backward
  have hactual := congrArg
    (fun f => f (cmGeometricKummerTrivialH1 hP Q))
    cmE2H1_maps_inverse_forward
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hgeneric hactual
  rw [hgeneric, hactual]
  change
    quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmContinuousOneCocycleToCharacter
          (cmCharacterToContinuousOneCocycle
            (cmGeometricKummerTrivialCharacter hP Q)))) = _
  rw [cmContinuousOneCocycleToCharacter_leftInverse]

/-- On an explicit ordinary half, the raw square-class image is therefore the
swapped x-T pair. -/
theorem cmExplicitRationalGeometricHalf_rawSquareClasses
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    {a b c : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1)
    (hc : c ^ 2 = (x : RatAlgClosure) + 1)
    (habc : a * b * c = -(y : RatAlgClosure)) :
    cmGenericKummerE2H1MulEquivRatSquareClasses
      (Multiplicative.ofAdd
        (cmGeometricKummerGenericE2H1
          (cmRationalGeometricPoint_isGaloisFixed (.affine x y hcurve))
          (cmExplicitRationalGeometricHalfData hcurve ha hb hc habc))) =
      ratSquareClassPairSwap
        (squareClassOf ⟨x, hx0⟩,
          squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  rw [cmGeometricKummerGenericE2H1_squareClass_evaluation]
  rw [cmExplicitRationalGeometricHalf_characterPair
    hcurve hy0 hx0 hx1 ha hb hc habc]
  exact cmRawGeometricQuadraticCharacterPair_toSquareClasses x hx0 hx1

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the complete generic-H¹ -> actual-H¹ -> trivial-H¹ -> character -> scalar
  character -> square-class stack is evaluated on geometric Kummer classes;
* the explicit ordinary half maps to exactly `swap([x],[x-1])` in the raw
  geometric basis.

The remaining ordinary global step is only to replace the explicit half by the
canonical chosen half `cmRationalGeometricHalfData`; this follows from the
already-proved character-level half independence.  Infinity and rational
2-torsion remain the finite exceptional cases.
-/

end

end Synthesis.Millennium.BSD
