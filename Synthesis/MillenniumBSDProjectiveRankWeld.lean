import Synthesis.MillenniumBSDUniversalRankWeld
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.GroupTheory.Torsion

/-!
# BSD affine/projective Mordell--Weil rank weld

The DASHI BSD core binds the algebraic rank to Mathlib's affine point group.
LeanDojo's Clay surface measures the same rational curve on the projective point
group.  Mathlib already supplies an additive equivalence between those two
models.  This file pays that carrier seam explicitly and leaves no independent
"affine versus projective rank" obligation in the BSD max-cut.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

/-- The literal Mathlib equivalence between projective and affine points of the
same rational Weierstrass curve. -/
noncomputable def projectiveAffinePointEquiv (E : RationalEllipticCurve) :
    E.1.toProjective.Point ≃+ E.1.toAffine.Point :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv E.1.toProjective

/-- Mordell--Weil finite generation on DASHI's affine carrier transports to the
projective carrier used by the Clay-facing rank definition. -/
theorem BSDMordellWeilFiniteGeneration.projective_fg
    (m : BSDMordellWeilFiniteGeneration)
    (E : RationalEllipticCurve) :
    AddGroup.FG E.1.toProjective.Point := by
  letI : E.1.IsElliptic := E.2
  letI : AddGroup.FG E.1.toAffine.Point := m.fg E
  exact AddGroup.fg_of_surjective
    (f := (projectiveAffinePointEquiv E).symm.toAddMonoidHom)
    (projectiveAffinePointEquiv E).symm.surjective

/-- The finitely-generated free rank is invariant under the exact
projective-to-affine additive equivalence.  Hence the two algebraic-rank
carriers are not a remaining BSD mathematical seam. -/
theorem BSDMordellWeilFiniteGeneration.projective_freeRank_eq_affine
    (m : BSDMordellWeilFiniteGeneration)
    (E : RationalEllipticCurve) :
    @AddCommGroup.freeRank E.1.toProjective.Point _ (m.projective_fg E) =
      @AddCommGroup.freeRank E.1.toAffine.Point _ (m.fg E) := by
  letI : E.1.IsElliptic := E.2
  letI hProj : AddGroup.FG E.1.toProjective.Point := m.projective_fg E
  letI hAff : AddGroup.FG E.1.toAffine.Point := m.fg E
  exact AddCommGroup.freeRank_congr (projectiveAffinePointEquiv E)

/-- Same-object algebraic max-cut receipt: once a Mordell--Weil binding exists,
there is no additional rank theorem hidden in the choice of affine versus
projective coordinates. -/
theorem projective_rank_carrier_paid
    (m : BSDMordellWeilFiniteGeneration) :
    ∀ E : RationalEllipticCurve,
      @AddCommGroup.freeRank E.1.toProjective.Point _ (m.projective_fg E) =
        @AddCommGroup.freeRank E.1.toAffine.Point _ (m.fg E) :=
  m.projective_freeRank_eq_affine

end Synthesis.Millennium.BSD
