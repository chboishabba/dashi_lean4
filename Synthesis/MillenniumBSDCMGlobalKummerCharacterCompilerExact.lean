import Synthesis.MillenniumBSDCMRationalToGeometricKummerExact
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction
import Synthesis.MillenniumBSDQuadraticKummerPair
import Mathlib.Tactic

/-!
# Selected CM curve: character-level compiler for the global Kummer weld

The difficult arithmetic content of the selected-curve global comparison is
pointwise: the geometric Kummer character of an explicit half must be the pair
of quadratic characters of x and x-1 in the already-fixed `(bit b, bit a)`
orientation.

Once that is known, the existing low-degree H¹ normalization and paid scalar
Kummer equivalence force the square-class output to be exactly
`([x],[x-1])`.  This owner packages that second implication, so the remaining
proof obligation is only the pointwise character identity.
-/

namespace Synthesis.Millennium.BSD

open BSDCohomology

noncomputable section

/-- The literal quadratic-character pair attached to the ordinary x-T
coordinates of a rational point. -/
noncomputable def cmXTQuadraticCharacterPair
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    RationalQuadraticCharacter × RationalQuadraticCharacter :=
  (rationalQuadraticKummerCharacter ⟨x, hx0⟩,
    rationalQuadraticKummerCharacter ⟨x - 1, sub_ne_zero.mpr hx1⟩)

/-- The inverse paid quadratic-Kummer equivalence sends that character pair
back to the literal x-T square classes. -/
theorem cmXTQuadraticCharacterPair_toSquareClasses
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    quadraticCharacterPairMulEquivRatSquareClasses
        (cmXTQuadraticCharacterPair x hx0 hx1) =
      (squareClassOf ⟨x, hx0⟩,
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  apply ratSquareClassPairMulEquivQuadraticCharacters.injective
  simp [cmXTQuadraticCharacterPair,
    ratSquareClassPairMulEquivQuadraticCharacters,
    quadraticCharacterPairMulEquivRatSquareClasses,
    rationalQuadraticKummerCharacterPairMulEquiv,
    rationalQuadraticKummerCharacterMulEquiv]

/-- Character-level equality is sufficient for the selected ordinary-point
square-class comparison.  The left character is the actual character used to
construct geometric H¹; the right side is the paid scalar Kummer pair. -/
theorem cmGeometricKummer_character_to_xT_squareClasses
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P)
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hchar :
      cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter hP Q) =
      cmXTQuadraticCharacterPair x hx0 hx1) :
    quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter hP Q)) =
      (squareClassOf ⟨x, hx0⟩,
        squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  rw [hchar]
  exact cmXTQuadraticCharacterPair_toSquareClasses x hx0 hx1

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the exact x-T quadratic-character pair on the repository's paid scalar
  Kummer character;
* its inverse image under the paid character/square-class equivalence is
  literally `([x],[x-1])`;
* once the geometric Kummer character is identified with that pair, no H¹ or
  square-class architecture remains in the global ordinary-point comparison.

ONLY ACTIVE GLOBAL ARITHMETIC OBLIGATION:
prove the character identity `hchar` from the literal point table in
`MillenniumBSDCMGaloisHalfPointTableExact` plus root-choice invariance in
`MillenniumBSDRationalQuadraticKummerDescent`.
-/

end

end Synthesis.Millennium.BSD
