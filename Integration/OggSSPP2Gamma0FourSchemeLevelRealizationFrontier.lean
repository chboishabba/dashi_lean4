import Integration.OggSSPP2BanerjeeAffineCurveScheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
import Integration.OggSSPP2Gamma0FourCanonicalRawFlag

/-!
# Scheme-level finite-flat Gamma_0(4) realization frontier

The current p=2 arithmetic sockets use typed carriers with finite-flat receipts.
Mathlib can state the stronger scheme-level property directly.

A genuine realization of the canonical raw flag should contain a nested diagram

  C₂ -> C₄ -> E -> S

over the deformation base S, with C₂ and C₄ finite and flat over S and with
the obvious triangles commuting.

This file pays that exact TARGET SHAPE. It does not construct:
* the scheme E attached to Banerjee's computational Weierstrass curve;
* group laws on E, C₂, or C₄;
* subgroup-scheme monomorphisms;
* the Frobenius-kernel identification;
* the Gamma_0(4) local-model marking.

Those are now the genuine implementation wall.
-/

namespace Integration.OggSSPP2Gamma0FourSchemeLevelRealizationFrontier

open CategoryTheory
open AlgebraicGeometry

namespace Banerjee := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace RawFlag := Integration.OggSSPP2Gamma0FourCanonicalRawFlag

/--
Scheme-level nested finite-flat flag.

This is deliberately stronger than the existing type/rank receipt: finiteness
and flatness are Mathlib scheme-morphism predicates.
-/
structure SchemeLevelFiniteFlatFlag where
  Base : Scheme
  Curve : Scheme
  OrderTwo : Scheme
  OrderFour : Scheme

  curveToBase : Curve ⟶ Base
  orderFourToCurve : OrderFour ⟶ Curve
  orderTwoToOrderFour : OrderTwo ⟶ OrderFour

  orderFourToBase : OrderFour ⟶ Base
  orderTwoToBase : OrderTwo ⟶ Base

  orderFourTriangle :
    orderFourToCurve ≫ curveToBase = orderFourToBase

  orderTwoTriangle :
    orderTwoToOrderFour ≫ orderFourToBase = orderTwoToBase

  orderFourFinite :
    AlgebraicGeometry.IsFinite orderFourToBase

  orderFourFlat :
    AlgebraicGeometry.Flat orderFourToBase

  orderTwoFinite :
    AlgebraicGeometry.IsFinite orderTwoToBase

  orderTwoFlat :
    AlgebraicGeometry.Flat orderTwoToBase

/--
Comparison layer still required to connect the scheme-level flag to the
concrete Banerjee deformation family and the source-backed canonical raw flag.
-/
structure BanerjeeSchemeComparison
    (flag : SchemeLevelFiniteFlatFlag) where
  computationalUniversalCurve :
    WeierstrassCurve Banerjee.F4DeformationBase

  computationalUniversalCurveIsBanerjee :
    computationalUniversalCurve = Banerjee.universalCurve

  rawFlag : RawFlag.RawGamma0FourFlag

  rawFlagIsCanonical :
    rawFlag.orderTwo = RawFlag.canonicalRawFlag.orderTwo ∧
      rawFlag.orderFour = RawFlag.canonicalRawFlag.orderFour

  /--
  Still open: identify the scheme-level curve with the computational
  Weierstrass family over the same deformation base.
  -/
  curveSchemeMatchesComputationalFamily : Prop

  /--
  Still open: identify the two finite-flat pieces with the Frobenius kernels
  ker(F) and ker(F²), including subgroup/group-law semantics.
  -/
  finiteFlatFlagMatchesFrobeniusKernels : Prop

/--
Full scheme-level realization grade required before the current typed
Gamma_0(4) enhancement may be called a constructed finite-flat subgroup flag.
-/
structure Realization where
  flag : SchemeLevelFiniteFlatFlag
  comparison : BanerjeeSchemeComparison flag

  curveSchemeMatchesComputationalFamilyProof :
    comparison.curveSchemeMatchesComputationalFamily

  finiteFlatFlagMatchesFrobeniusKernelsProof :
    comparison.finiteFlatFlagMatchesFrobeniusKernels

inductive Residual
  | missingProjectiveEllipticSchemeCompactification
  | missingFiniteFlatFrobeniusKernelSubgroupSchemes
  | missingGamma0FourLocalModelMarking
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingProjectiveEllipticSchemeCompactification

structure Boundary where
  actualAffineBanerjeeSchemeConstructed : Bool
  actualAffineCurveOverWittBaseConstructed : Bool
  mathlibSchemeCarrierAvailable : Bool
  mathlibFiniteMorphismPredicateAvailable : Bool
  mathlibFlatMorphismPredicateAvailable : Bool
  nestedC2C4SchemeDiagramTyped : Bool
  finiteFlatRequirementsAreActualSchemePredicates : Bool
  banerjeeComputationalCurvePromotedToScheme : Bool
  frobeniusKernelSubgroupSchemesConstructed : Bool
  groupSchemeSubgroupSemanticsConstructed : Bool
  gamma0FourLocalModelMarkingConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualAffineBanerjeeSchemeConstructed := true
  actualAffineCurveOverWittBaseConstructed := true
  mathlibSchemeCarrierAvailable := true
  mathlibFiniteMorphismPredicateAvailable := true
  mathlibFlatMorphismPredicateAvailable := true
  nestedC2C4SchemeDiagramTyped := true
  finiteFlatRequirementsAreActualSchemePredicates := true
  banerjeeComputationalCurvePromotedToScheme := false
  frobeniusKernelSubgroupSchemesConstructed := false
  groupSchemeSubgroupSemanticsConstructed := false
  gamma0FourLocalModelMarkingConstructed := false

end Integration.OggSSPP2Gamma0FourSchemeLevelRealizationFrontier
