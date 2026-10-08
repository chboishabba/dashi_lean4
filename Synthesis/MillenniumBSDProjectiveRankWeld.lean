import Synthesis.MillenniumBSDUniversalRankWeld
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.GroupTheory.Torsion

/-!
# BSD affine/projective Mordell--Weil free-rank weld

Submission max-cut rule: do not introduce a new rank premise.  Mathlib already
supplies the additive equivalence between projective and affine points of the
same Weierstrass curve, so finite generation and finitely-generated free rank
transport across that equivalence mechanically.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable def projectiveAffinePointEquiv (E : RationalEllipticCurve) :
    E.1.toProjective.Point ≃+ E.1.toAffine.Point :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv E.1.toProjective

theorem BSDMordellWeilFiniteGeneration.projective_fg
    (m : BSDMordellWeilFiniteGeneration)
    (E : RationalEllipticCurve) :
    AddGroup.FG E.1.toProjective.Point := by
  letI : E.1.IsElliptic := E.2
  letI : AddGroup.FG E.1.toAffine.Point := m.fg E
  exact AddGroup.fg_of_surjective
    (f := (projectiveAffinePointEquiv E).symm.toAddMonoidHom)
    (projectiveAffinePointEquiv E).symm.surjective

theorem BSDMordellWeilFiniteGeneration.projective_freeRank_eq_affine
    (m : BSDMordellWeilFiniteGeneration)
    (E : RationalEllipticCurve) :
    @AddCommGroup.freeRank E.1.toProjective.Point _ (m.projective_fg E) =
      @AddCommGroup.freeRank E.1.toAffine.Point _ (m.fg E) := by
  letI : E.1.IsElliptic := E.2
  letI hProj : AddGroup.FG E.1.toProjective.Point := m.projective_fg E
  letI hAff : AddGroup.FG E.1.toAffine.Point := m.fg E
  exact AddCommGroup.freeRank_congr (projectiveAffinePointEquiv E)

theorem projective_rank_carrier_paid
    (m : BSDMordellWeilFiniteGeneration) :
    ∀ E : RationalEllipticCurve,
      @AddCommGroup.freeRank E.1.toProjective.Point _ (m.projective_fg E) =
        @AddCommGroup.freeRank E.1.toAffine.Point _ (m.fg E) :=
  m.projective_freeRank_eq_affine

end Synthesis.Millennium.BSD
