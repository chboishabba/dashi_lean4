import Synthesis.MillenniumBSDCMGenericE2SameObjectExact
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Selected CM curve: the generic Kummer E[2] H¹ is the paid square-class H¹

The genuine Kummer exact-sequence lane uses

  BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass.

The explicit x-T descent lane had already paid continuous H¹ <-> rational
square-class pairs for `cmActualE2Representation`.  The previous owner proves
these two coefficient representations are the same object up to a literal
TopRep isomorphism.  This file transports H¹ across that isomorphism and
therefore puts the generic Kummer coefficient object on the exact square-class
target already used by explicit descent.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory

noncomputable section

abbrev CMGenericKummerE2TopRep :=
  BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass

noncomputable def cmGenericKummerE2H1ToActual :
    continuousCohomology 1 CMGenericKummerE2TopRep ⟶
      continuousCohomology 1 cmActualE2Representation :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    cmGenericKummerE2ToActualTopRep 1

noncomputable def cmActualE2H1ToGenericKummer :
    continuousCohomology 1 cmActualE2Representation ⟶
      continuousCohomology 1 CMGenericKummerE2TopRep :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    cmActualE2ToGenericKummerTopRep 1

theorem cmGenericKummerE2H1_maps_inverse_forward :
    cmGenericKummerE2H1ToActual ≫ cmActualE2H1ToGenericKummer = 𝟙 _ := by
  rw [← ContinuousCohomology.map_comp]
  simpa [cmGenericKummerE2H1ToActual, cmActualE2H1ToGenericKummer] using
    ContinuousCohomology.map_id CMGenericKummerE2TopRep 1

theorem cmGenericKummerE2H1_maps_inverse_backward :
    cmActualE2H1ToGenericKummer ≫ cmGenericKummerE2H1ToActual = 𝟙 _ := by
  rw [← ContinuousCohomology.map_comp]
  simpa [cmGenericKummerE2H1ToActual, cmActualE2H1ToGenericKummer] using
    ContinuousCohomology.map_id cmActualE2Representation 1

noncomputable def cmGenericKummerE2H1IsoActual :
    continuousCohomology 1 CMGenericKummerE2TopRep ≅
      continuousCohomology 1 cmActualE2Representation where
  hom := cmGenericKummerE2H1ToActual
  inv := cmActualE2H1ToGenericKummer
  hom_inv_id := cmGenericKummerE2H1_maps_inverse_forward
  inv_hom_id := cmGenericKummerE2H1_maps_inverse_backward

/-- Full group-law-preserving comparison from H¹ of the *generic Kummer E[2]
object* to the literal square-class pair used by x-T descent. -/
noncomputable def cmGenericKummerE2H1MulEquivRatSquareClasses :
    Multiplicative (continuousCohomology 1 CMGenericKummerE2TopRep) ≃*
      (RatSquareClass × RatSquareClass) :=
  (AddEquiv.toMultiplicative
    cmGenericKummerE2H1IsoActual.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv).trans
      cmActualE2H1MulEquivRatSquareClasses_paid

/-- Plain equivalence form for consumers that do not need the group law. -/
noncomputable def cmGenericKummerE2H1EquivRatSquareClasses :
    (continuousCohomology 1 CMGenericKummerE2TopRep) ≃
      (RatSquareClass × RatSquareClass) :=
  cmGenericKummerE2H1IsoActual.toContinuousLinearEquiv.toEquiv.trans
    cmActualE2H1EquivRatSquareClasses_paid

/-!
MAX-CUT STATUS

PAID:
* H¹ of the exact coefficient object appearing in the genuine Kummer sequence
  is now identified with the exact rational square-class pair used by explicit
  descent;
* the comparison preserves the group law.

NEXT:
* construct delta(P) geometrically from a half Q and prove its image under
  `cmGenericKummerE2H1MulEquivRatSquareClasses` is the already-existing
  `totalGlobalKummer P`;
* then prove the analogous local statements and localization naturality.
-/

end

end Synthesis.Millennium.BSD
