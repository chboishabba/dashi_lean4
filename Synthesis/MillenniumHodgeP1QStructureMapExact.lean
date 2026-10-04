import Synthesis.MillenniumHodgeP1QBaseRingExact

/-!
# Hodge max-cut: the selected Proj is displayed over Spec Q

`MillenniumHodgeP1QBaseRingExact` identifies the degree-zero piece of the
ordinary grading on Q[X₀,X₁] with Q as a ring.  Because `Spec` is
contravariant, the inverse ring equivalence induces the scheme isomorphism

  Spec ((Q[X₀,X₁]_•)₀) ≅ Spec Q.

Composing this isomorphism with `Proj.toSpecZero` gives the literal structure
morphism of the selected P¹_Q regression object over Spec Q.  This removes the
last base-object ambiguity before constructing the rational section [1:0].
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open CategoryTheory

/-- The exact scheme isomorphism induced by the paid grade-zero ring
identification `(P1QGrading 0) ≃+* Q`. -/
noncomputable def p1QGradeZeroSpecIso :
    Spec ↧(P1QGrading 0) ≅ Spec (.of ℚ) :=
  Scheme.Spec.mapIso p1QGradeZeroRingEquiv.symm.toCommRingCatIso.op

/-- The displayed structure morphism of the selected projective line over
`Spec Q`.  It is the canonical Proj structure map followed by the actual
base-ring `Spec` isomorphism. -/
noncomputable def p1QToSpecQ :
    P1QScheme ⟶ Spec (.of ℚ) :=
  p1QToGradeZeroSpec ≫ p1QGradeZeroSpecIso.hom

@[simp, reassoc] theorem p1QToSpecQ_factorization :
    p1QToGradeZeroSpec ≫ p1QGradeZeroSpecIso.hom = p1QToSpecQ :=
  rfl

/-- The old self-product over the literal degree-zero spectrum is canonically
identified with a self-product over `Spec Q` at the level of the displayed
base map.  Downstream ruling constructors should consume `p1QToSpecQ`; no
parallel projective-line carrier is introduced. -/
theorem p1QToSpecQ_is_canonical :
    p1QToSpecQ = p1QToGradeZeroSpec ≫ p1QGradeZeroSpecIso.hom :=
  rfl

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* `Spec ((P1QGrading 0)) ≅ Spec Q` on the actual Mathlib schemes;
* the literal selected `P1QScheme` structure morphism to `Spec Q`;
* no synthetic base scheme or projective-line wrapper.

NEXT:
* construct `[1:0] : Spec Q ⟶ P1QScheme` and prove
  `[1:0] ≫ p1QToSpecQ = 𝟙 _`;
* instantiate the generic relative rulings over this exact base map;
* push their fundamental cycles and prove the factor-swap (-1)-eigencycle.
-/

end Synthesis.Millennium.Hodge
