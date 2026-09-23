import Synthesis.MillenniumBSDRationalQuadraticKummerSurjective
import Synthesis.MillenniumBSDRatSquareClassMathlibWeld

/-!
# Pair-valued quadratic Kummer equivalence

The scalar Kummer map is now proved bijective.  This file upgrades that paid
bijection to an actual `Equiv`, then takes its product so the two coordinates
of the CM curve's trivial `E[2] ≃ (Z/2)^2` representation have the exact
square-class carrier used by the explicit descent lane.

No continuous-H¹ theorem is asserted here.  The output of this file is the
right-hand side of that theorem, fully paid.
-/

namespace Synthesis.Millennium.BSD

/-- The paid scalar equivalence
`Qˣ/(Qˣ)^2 ≃ Hom_cont(G_Q,C₂)`. -/
noncomputable def rationalQuadraticKummerCharacterEquiv :
    MathlibRatSquareClass ≃ RationalQuadraticCharacter :=
  Equiv.ofBijective rationalSquareClassKummerHom
    rationalQuadraticKummerCharacterBijection_paid

@[simp] theorem rationalQuadraticKummerCharacterEquiv_apply
    (a : MathlibRatSquareClass) :
    rationalQuadraticKummerCharacterEquiv a =
      rationalSquareClassKummerHom a := rfl

/-- Componentwise paid Kummer equivalence on the canonical mathlib
square-class carrier. -/
noncomputable def rationalQuadraticKummerCharacterPairEquiv :
    (MathlibRatSquareClass × MathlibRatSquareClass) ≃
      (RationalQuadraticCharacter × RationalQuadraticCharacter) :=
  rationalQuadraticKummerCharacterEquiv.prodCongr
    rationalQuadraticKummerCharacterEquiv

/-- The same componentwise equivalence on the repository's literal
cross-multiplied square-class quotient. -/
noncomputable def ratSquareClassPairEquivQuadraticCharacters :
    (RatSquareClass × RatSquareClass) ≃
      (RationalQuadraticCharacter × RationalQuadraticCharacter) :=
  ratKummerPairEquivMathlib.trans rationalQuadraticKummerCharacterPairEquiv

/-- Reverse direction used by the BA4 H¹ reduction. -/
noncomputable def quadraticCharacterPairEquivRatSquareClasses :
    (RationalQuadraticCharacter × RationalQuadraticCharacter) ≃
      (RatSquareClass × RatSquareClass) :=
  ratSquareClassPairEquivQuadraticCharacters.symm

theorem ratSquareClassPairEquivQuadraticCharacters_bijective :
    Function.Bijective ratSquareClassPairEquivQuadraticCharacters :=
  ratSquareClassPairEquivQuadraticCharacters.bijective

end Synthesis.Millennium.BSD
