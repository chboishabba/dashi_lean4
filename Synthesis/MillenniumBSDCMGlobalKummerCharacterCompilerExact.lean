import Synthesis.MillenniumBSDCMRationalToGeometricKummerExact
import Synthesis.MillenniumBSDCMXTOrientationExact
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction
import Synthesis.MillenniumBSDQuadraticKummerPair
import Mathlib.Tactic

/-!
# Selected CM curve: character-level compiler for the global Kummer weld

The actual geometric E[2] basis is

  (1,0) ↦ (0,0),   (0,1) ↦ (1,0).

The half-point calculation therefore gives the raw character order

  (χ_{x-1}, χ_x),

while explicit x-T is written `([x],[x-1])`.  The repository's existing
`ratSquareClassPairSwap` is exactly the orientation correction.  This owner
packages the purely functorial part: once the geometric Kummer character is
the raw root-sign pair, its paid H¹/square-class image is the swap of the
explicit x-T pair.
-/

namespace Synthesis.Millennium.BSD

open BSDCohomology

noncomputable section

/-- Quadratic-character pair in the literal raw geometric E[2] basis order:
first the sign of b²=x-1, then the sign of a²=x. -/
noncomputable def cmRawGeometricQuadraticCharacterPair
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    RationalQuadraticCharacter × RationalQuadraticCharacter :=
  (rationalQuadraticKummerCharacter ⟨x - 1, sub_ne_zero.mpr hx1⟩,
    rationalQuadraticKummerCharacter ⟨x, hx0⟩)

/-- The inverse paid quadratic-Kummer equivalence sends the raw geometric
character order to the swapped explicit x-T square-class pair. -/
theorem cmRawGeometricQuadraticCharacterPair_toSquareClasses
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    quadraticCharacterPairMulEquivRatSquareClasses
        (cmRawGeometricQuadraticCharacterPair x hx0 hx1) =
      ratSquareClassPairSwap
        (squareClassOf ⟨x, hx0⟩,
          squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  apply ratSquareClassPairMulEquivQuadraticCharacters.injective
  simp [cmRawGeometricQuadraticCharacterPair,
    ratSquareClassPairSwap,
    ratSquareClassPairMulEquivQuadraticCharacters,
    quadraticCharacterPairMulEquivRatSquareClasses,
    rationalQuadraticKummerCharacterPairMulEquiv,
    rationalQuadraticKummerCharacterMulEquiv]

/-- Character-level equality is sufficient for the selected ordinary-point
raw geometric square-class comparison. -/
theorem cmGeometricKummer_character_to_raw_xT_squareClasses
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P)
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hchar :
      cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter hP Q) =
      cmRawGeometricQuadraticCharacterPair x hx0 hx1) :
    quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter hP Q)) =
      ratSquareClassPairSwap
        (squareClassOf ⟨x, hx0⟩,
          squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  rw [hchar]
  exact cmRawGeometricQuadraticCharacterPair_toSquareClasses x hx0 hx1

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the geometric basis orientation is respected rather than silently assumed;
* the raw quadratic-character pair is `(χ_{x-1},χ_x)`;
* its inverse image under the paid character/square-class equivalence is
  exactly `swap([x],[x-1])`, matching `CMGeometricXTKummerOrientationTheorem`;
* once the pointwise geometric character is identified with this pair, no H¹
  or square-class architecture remains in the ordinary-point comparison.

ONLY ACTIVE GLOBAL ARITHMETIC OBLIGATION:
prove `hchar` from `MillenniumBSDCMGaloisHalfPointTableExact` plus the paid
root-choice invariance theorem `rationalKummerBitOfRoot_independent`.
Exceptional rational two-torsion points are then the separate finite boundary
cases already represented by `totalGlobalKummer`.
-/

end

end Synthesis.Millennium.BSD
