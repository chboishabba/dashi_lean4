import BSDStoll.ClaySameCurveArithmeticResponse
import EllipticCurves.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Every rational elliptic curve admits Stoll's normal-form arithmetic donor

Rather than ASSUMING every curve's a₁ and a₃ vanish, use Mathlib's literal
normalization
  C = E.toCharNeTwoNF : VariableChange ℚ
  E_nf = C • E, with a₁(E_nf)=a₃(E_nf)=0.

Stoll's `Affine.Point.equivVariableChange E C` is an actual group
equivalence between E_nf(ℚ) and E(ℚ), not merely a cardinality comparison.

The independently defined genuine all-place 2-Selmer group is then
constructed on E_nf for every original literal rational elliptic curve.

This gives a canonical descent PRESENTATION for arbitrary rational curves,
but does not yet transport the full cohomological Sha[2] definition or the
Hasse-Weil L-function through the coordinate isomorphism.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- A genuine admissible coordinate change, defined from the coefficients
of the SAME originally supplied rational elliptic curve. -/
noncomputable def rationalCurveNormalizingChange
    (E : RationalEllipticCurve) :
    VariableChange ℚ :=
  E.1.toCharNeTwoNF

/-- The actual normalized rational Weierstrass model. -/
noncomputable def normalizedRationalEllipticCurve
    (E : RationalEllipticCurve) :
    RationalEllipticCurve := by
  letI : E.1.IsElliptic := E.2
  exact ⟨(rationalCurveNormalizingChange E) • E.1, inferInstance⟩

/-- The normal-form hypothesis required by Stoll's x-T Kummer map is
NOW PROVED from the input coefficients for EVERY curve over ℚ. -/
theorem normalizedRationalCurve_isCharNeTwoNF
    (E : RationalEllipticCurve) :
    (normalizedRationalEllipticCurve E).1.toAffine.IsCharNeTwoNF := by
  change
    ((E.1.toCharNeTwoNF • E.1).toAffine).IsCharNeTwoNF
  infer_instance

/-- Real point-group transport under the SAME normalizing coordinate
change. This is a genuine additive group equivalence and so retains the
Mordell–Weil group, not only its set cardinality. -/
noncomputable def normalizedPointGroupEquiv
    (E : RationalEllipticCurve) :
    (normalizedRationalEllipticCurve E).1.toAffine.Point
      ≃+
    E.1.toAffine.Point := by
  letI : E.1.IsElliptic := E.2
  exact E.1.toAffine.Point.equivVariableChange
    E.1
    (rationalCurveNormalizingChange E)

/-- In particular the normalization intertwines the literal doubling
maps. This is the first same-curve input needed for transporting the
global Kummer source and its rational two-torsion correction. -/
theorem normalizedPointGroupEquiv_commutes_with_double
    (E : RationalEllipticCurve)
    (P : (normalizedRationalEllipticCurve E).1.toAffine.Point) :
    normalizedPointGroupEquiv E (2 • P) =
      2 • normalizedPointGroupEquiv E P := by
  exact map_nsmul (normalizedPointGroupEquiv E) 2 P

/-- For every rational elliptic curve, return the ACTUAL arithmetic
Selmer subgroup of its explicitly isomorphic normal form. -/
noncomputable def allCurveNormalizedTwoSelmer
    (E : RationalEllipticCurve) :
    Subgroup (normalizedRationalEllipticCurve E).1.toAffine.M := by
  letI : (normalizedRationalEllipticCurve E).1.toAffine.IsCharNeTwoNF :=
    normalizedRationalCurve_isCharNeTwoNF E
  exact actualNormalFormTwoSelmer (normalizedRationalEllipticCurve E)

/-- The combined all-place obstruction map has precisely the normalized
arithmetic Selmer group as its kernel for any supplied E/ℚ. -/
theorem allCurveNormalizedArithmeticResponseKernel
    (E : RationalEllipticCurve) :
    letI : (normalizedRationalEllipticCurve E).1.toAffine.IsCharNeTwoNF :=
      normalizedRationalCurve_isCharNeTwoNF E
    (actualClayNormalFormCompleteResponse
      (normalizedRationalEllipticCurve E)).ker
      =
    allCurveNormalizedTwoSelmer E := by
  letI : (normalizedRationalEllipticCurve E).1.toAffine.IsCharNeTwoNF :=
    normalizedRationalCurve_isCharNeTwoNF E
  exact
    actualClayNormalFormResponseKernel_isSelmer
      (normalizedRationalEllipticCurve E)

/-!
A cohomological comparison must still prove that the normalized model's
Selmer presentation agrees with the desired invariant Sel_2(E) and that
its quotient by the point-image represents Sha(E)[2]. A change of variables
on point groups alone does not identify Tate–Shafarevich groups.

Analytic order-of-vanishing comparison remains a SEPARATE theorem.
-/

end

end Synthesis.Millennium.BSD
