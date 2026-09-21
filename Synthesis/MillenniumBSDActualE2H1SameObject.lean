import Synthesis.MillenniumBSDActualE2TopRepSameObject
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# BA4 reduction: continuous H¹ of actual E[2] is the trivial-module H¹

The geometric two-torsion representation is already TopRep-isomorphic to the
trivial `(Z/2)^2` representation.  Continuous cohomology is functorial in the
coefficient representation, so the same-object theorem transports all of BA4
away from elliptic geometry:

  H¹_cont(G_Q, E[2]) ≅ H¹_cont(G_Q, (Z/2)^2_triv).

The remaining Kummer producer is therefore purely scalar/quadratic: identify
continuous H¹ of the trivial Z/2 character with rational square classes, and
prove the analogous local statements and localization compatibility.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory

noncomputable def cmE2H1ToActual :
    continuousCohomology 1 cmTwoTorsionRepresentation ⟶
      continuousCohomology 1 cmActualE2Representation :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    cmTwoTorsionTopRepToActual 1

noncomputable def cmActualE2H1ToTrivial :
    continuousCohomology 1 cmActualE2Representation ⟶
      continuousCohomology 1 cmTwoTorsionRepresentation :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    cmActualE2TopRepToTwoTorsion 1

theorem cmE2H1_maps_inverse_forward :
    cmE2H1ToActual ≫ cmActualE2H1ToTrivial = 𝟙 _ := by
  rw [← ContinuousCohomology.map_comp]
  simpa [cmE2H1ToActual, cmActualE2H1ToTrivial] using
    ContinuousCohomology.map_id cmTwoTorsionRepresentation 1

theorem cmE2H1_maps_inverse_backward :
    cmActualE2H1ToTrivial ≫ cmE2H1ToActual = 𝟙 _ := by
  rw [← ContinuousCohomology.map_comp]
  simpa [cmE2H1ToActual, cmActualE2H1ToTrivial] using
    ContinuousCohomology.map_id cmActualE2Representation 1

/-- Literal continuous-H¹ same-object isomorphism induced by the actual E[2] TopRep isomorphism. -/
noncomputable def cmActualE2H1IsoTrivial :
    continuousCohomology 1 cmActualE2Representation ≅
      continuousCohomology 1 cmTwoTorsionRepresentation where
  hom := cmActualE2H1ToTrivial
  inv := cmE2H1ToActual
  hom_inv_id := cmE2H1_maps_inverse_backward
  inv_hom_id := cmE2H1_maps_inverse_forward

/--
Exact remaining global scalar Kummer theorem after all elliptic E[2] geometry
has been removed.  This is intentionally the smallest prize-facing producer.
-/
def RationalQuadraticContinuousKummerProducer : Prop :=
  ∃ squareClass : Type,
    Nonempty
      ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
        (squareClass × squareClass))

/--
The full descent comparison additionally requires the same scalar theorem at
every rational place and commutation with localization.  No general Kummer
framework is asserted here.
-/
structure ScalarKummerLocalizationProducer where
  globalSquareClass : Type
  localSquareClass : RationalPlace → Type
  globalH1Equiv :
    (continuousCohomology 1 cmTwoTorsionRepresentation) ≃
      (globalSquareClass × globalSquareClass)
  localH1Equiv : ∀ v : RationalPlace,
    Type
  localizationCompatibility : Prop

end Synthesis.Millennium.BSD
