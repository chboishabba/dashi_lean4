import Integration.EisensteinLatticeCountingRegression
import Integration.EisensteinCMOrderActionExact
import Integration.EisensteinJZeroInertPrimeLocalFactorExact
import Integration.EisensteinJZeroCanonicalCubicCharacterExact
import Integration.EisensteinJZeroSplitJacobiCyclotomicExact
import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
import Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact
import Integration.EisensteinJZeroAllGoodPrimeLocalExact
import Integration.EisensteinJZeroBadPrimeThreeExact

/-!
# Eisenstein arithmetic -> CM terminal max-cut

This is the machine-readable terminal owner for the original Eisenstein
programme.  The old visual target

    Cantor/radix scale series ?= Eisenstein norm-shell series

remains retired.  The exact arithmetic chain is

    (a,b) in Z^2
      -> a+b*omega in Z[omega]
      -> N(a+b*omega)=a^2-a*b+b^2
      -> universal norm-shell / chi_-3 divisor formula
      -> 6*zeta*L(chi_-3) on Re(s)>1.

On the SAME integral carrier the CM chain is

    Z[omega]
      -> Frac(Z[omega])
      -> E : y^2=x^3+1, j(E)=0
      -> Phi(x,y)=(omega*x,y)
      -> Phi^2+Phi+1=0 on Mathlib's native point group
      -> Z[omega] -> End(E(Frac(Z[omega]))).

The finite/local arithmetic branch is source-written for every good prime
`p > 3`.

INERT (`p % 3 = 2`)
    chi_-3(p) = -1,
    #E(F_p)=p+1,
    a_p=0,
    P_p(T)=1+p*T^2.

SPLIT (`p % 3 = 1`)
    canonical order-three character
      -> literal cube-fibre certificate
      -> Mathlib Jacobi trace
      -> J in Z[zeta_6]
      -> J*conj(J)=p
      -> explicit Z[zeta_6]=Z[omega] carrier weld
      -> z_p=a+b*omega : EisensteinQA
      -> N(z_p)=p
      -> a_p=-(2*a-b)
      -> P_p(T)=1+(2*a-b)T+p*T^2
      -> exact existing six-unit x split-choice normal form.

At the bad prime 3 the literal reduced cubic is also inspected: `(2,0)` is an
explicit singular point, both formal partials vanish there, and the affine /
naive-projective counts are exact.  Those facts are NOT promoted to a
bad-prime elliptic local factor: that requires reduction-type/conductor
semantics (Neron/Kodaira or an equivalent owner), absent from pinned Mathlib.

Thus the split finite-field/Frobenius branch is no longer a blocker.  The
remaining global arithmetic promotion is to pay the bad-prime local factor,
package the same local data as a Groessencharacter/Hecke object, prove the
same-curve Euler product identification, and only then derive global
elliptic/Hecke L-function agreement.

Independently, the geometric CM track still requires an elliptic
morphism/isogeny-degree carrier, faithfulness of the geometric Eisenstein-order
embedding, and degree(a+b*omega)=N(a+b*omega).  A point-group action alone does
not pay those geometric statements.

Attribution boundary:
* Mathlib owns its generic affine elliptic point group, quadratic algebra,
  finite-field, multiplicative-character, primitive-root, Jacobi-sum,
  conjugation and complex-norm infrastructure.
* DASHI/Lean owns the specialisations/compositions and same-object welds in
  this repository.
* No external scientific source authority is manufactured by library imports.
* The arithmetic `6*zeta*L(chi_-3)` series is not relabelled as `L(E,s)`.
-/

namespace Integration.EisensteinArithmeticCMTerminalMaxCutExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroCMConcreteExact
open Integration.EisensteinCMOrderActionExact
open Integration.EisensteinJZeroInertPrimeLocalFactorExact
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact
open Integration.EisensteinJZeroSplitJacobiCyclotomicExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact
open Integration.EisensteinJZeroAllGoodPrimeLocalExact
open Integration.EisensteinJZeroBadPrimeThreeExact

inductive EisensteinArithmeticCMBlocker
  | missingGeometricIsogenyDegreeCarrier
  | missingFaithfulGeometricCMEmbedding
  | missingEndomorphismDegreeNormTheorem
  | missingBadPrimeReductionTypeAndLocalFactor
  | missingGroessencharacterGlobalization
  | missingSameCurveEulerProductAgreement
  | missingEllipticHeckeLSeriesAgreement
  | missingExactHeadKernelReceipt
  deriving DecidableEq, Repr

open EisensteinArithmeticCMBlocker

structure EisensteinArithmeticCMTerminalStatus where
  finiteGraphRadiusSeparatedFromNormShell : Bool
  cantorRadixGeometryRetainedAsDistinctObservable : Bool
  cantorScaleSeriesIdentifiedWithNormShellSeries : Bool

  standardEisensteinIntegralCarrierPaid : Bool
  euclideanDomainAndUfdPaid : Bool
  universalNormShellFormulaPaid : Bool
  arithmeticDirichletFactorizationPaid : Bool

  sameCarrierFractionFieldPaid : Bool
  nativeJZeroCurvePaid : Bool
  nativeJZeroPointGroupPaid : Bool
  orderThreePointGroupEndomorphismPaid : Bool
  eisensteinQuadraticEndomorphismRelationPaid : Bool
  sameIntegralCarrierOrderActionPaid : Bool

  inertPrimeSamePrimeWeldPaid : Bool
  inertPrimeTraceZeroPaid : Bool
  inertPrimeLocalEulerShapePaid : Bool

  canonicalCubeFibreCharacterCertificatePaid : Bool
  genericCubicJacobiTraceCompilerPaid : Bool
  splitJacobiSixthCyclotomicIntegralityPaid : Bool
  splitJacobiNormSquarePrimePaid : Bool
  sixthCyclotomicToLiteralEisensteinCarrierPaid : Bool
  splitJacobiPulledBackToLiteralEisensteinQAPaid : Bool
  splitJacobiLiteralNormEqualsPrimePaid : Bool
  splitPrimeFrobeniusFormulaPaid : Bool
  splitPrimeLocalEulerPolynomialPaid : Bool
  splitPrimeSixUnitNormalizationPaid : Bool
  allGoodPrimeSameCurveLocalClassificationPaid : Bool

  badPrimeThreeLiteralReductionPaid : Bool
  badPrimeThreeSingularityPaid : Bool
  badPrimeThreePointCountPaid : Bool
  badPrimeReductionTypePaid : Bool
  badPrimeEllipticLocalFactorPaid : Bool

  rationalPointActionFaithfulnessInferred : Bool
  faithfulGeometricCMEmbeddingPaid : Bool
  endomorphismDegreeEqualsNormPaid : Bool
  groessencharacterPaid : Bool
  sameCurveEulerProductAgreementPaid : Bool
  ellipticLSeriesAgreementPaid : Bool

  dirichletLocalFactorIdentifiedWithEllipticEulerFactor : Bool
  arithmeticShellLSeriesIdentifiedWithEllipticLSeries : Bool
  chemistryOrMonsterStateSpaceIdentityPromoted : Bool
  oggOrMoonshineSemanticsPromoted : Bool
  e6F3IdentityPromoted : Bool
  physicalMechanismPromotedFromSharedC3 : Bool

  firstGeometricBlocker : EisensteinArithmeticCMBlocker
  firstGlobalArithmeticBlocker : EisensteinArithmeticCMBlocker

/-- Machine-readable terminal status after the local split-prime max-cut. -/
def terminalStatus : EisensteinArithmeticCMTerminalStatus where
  finiteGraphRadiusSeparatedFromNormShell := true
  cantorRadixGeometryRetainedAsDistinctObservable := true
  cantorScaleSeriesIdentifiedWithNormShellSeries := false

  standardEisensteinIntegralCarrierPaid := true
  euclideanDomainAndUfdPaid := true
  universalNormShellFormulaPaid := true
  arithmeticDirichletFactorizationPaid := true

  sameCarrierFractionFieldPaid := true
  nativeJZeroCurvePaid := true
  nativeJZeroPointGroupPaid := true
  orderThreePointGroupEndomorphismPaid := true
  eisensteinQuadraticEndomorphismRelationPaid := true
  sameIntegralCarrierOrderActionPaid := true

  inertPrimeSamePrimeWeldPaid := true
  inertPrimeTraceZeroPaid := true
  inertPrimeLocalEulerShapePaid := true

  canonicalCubeFibreCharacterCertificatePaid := true
  genericCubicJacobiTraceCompilerPaid := true
  splitJacobiSixthCyclotomicIntegralityPaid := true
  splitJacobiNormSquarePrimePaid := true
  sixthCyclotomicToLiteralEisensteinCarrierPaid := true
  splitJacobiPulledBackToLiteralEisensteinQAPaid := true
  splitJacobiLiteralNormEqualsPrimePaid := true
  splitPrimeFrobeniusFormulaPaid := true
  splitPrimeLocalEulerPolynomialPaid := true
  splitPrimeSixUnitNormalizationPaid := true
  allGoodPrimeSameCurveLocalClassificationPaid := true

  badPrimeThreeLiteralReductionPaid := true
  badPrimeThreeSingularityPaid := true
  badPrimeThreePointCountPaid := true
  badPrimeReductionTypePaid := false
  badPrimeEllipticLocalFactorPaid := false

  rationalPointActionFaithfulnessInferred := false
  faithfulGeometricCMEmbeddingPaid := false
  endomorphismDegreeEqualsNormPaid := false
  groessencharacterPaid := false
  sameCurveEulerProductAgreementPaid := false
  ellipticLSeriesAgreementPaid := false

  dirichletLocalFactorIdentifiedWithEllipticEulerFactor := false
  arithmeticShellLSeriesIdentifiedWithEllipticLSeries := false
  chemistryOrMonsterStateSpaceIdentityPromoted := false
  oggOrMoonshineSemanticsPromoted := false
  e6F3IdentityPromoted := false
  physicalMechanismPromotedFromSharedC3 := false

  firstGeometricBlocker := missingGeometricIsogenyDegreeCarrier
  firstGlobalArithmeticBlocker := missingBadPrimeReductionTypeAndLocalFactor

------------------------------------------------------------------------
-- Exact donor surfaces.
------------------------------------------------------------------------

def arithmeticToCMAction : EisensteinQA →+*
    AddMonoid.End eisensteinJZeroCurve.Point :=
  eisensteinOrderAction

theorem arithmeticOmega_is_CMrotation :
    arithmeticToCMAction (QuadraticAlgebra.omega : EisensteinQA) =
      eisensteinCMEndomorphism :=
  eisensteinOrderAction_omega

theorem coordinatePair_to_CMaction (a b : Int) :
    arithmeticToCMAction (asQuadraticAlgebra a b) =
      a • (1 : AddMonoid.End eisensteinJZeroCurve.Point) +
        b • eisensteinCMEndomorphism :=
  eisensteinOrderAction_coordinates a b

def inertPrimeSameObjectWeld
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 2) :
    InertPrimeArithmeticEllipticWeld p :=
  inertPrimeArithmeticEllipticWeld p hp2 hp3

def splitPrimeLiteralEisensteinElement
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    EisensteinQA :=
  splitJacobiEisensteinElement p hp2 hp3

theorem splitPrimeLiteralEisensteinElement_norm
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    QuadraticAlgebra.norm (splitPrimeLiteralEisensteinElement p hp2 hp3) = p :=
  splitJacobiEisensteinElement_norm p hp2 hp3

theorem splitPrimeLiteralEisenstein_trace
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p)
      = -(2 * (splitPrimeLiteralEisensteinElement p hp2 hp3).re
          - (splitPrimeLiteralEisensteinElement p hp2 hp3).im) :=
  splitPrime_jZero_trace_formula p hp2 hp3

def localDataAtGoodPrime
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    GoodPrimeLocalData p :=
  goodPrimeLocalData p hp3

------------------------------------------------------------------------
-- Productive cross-pollination firewall.
------------------------------------------------------------------------

structure C3DownstreamConsumerBoundary where
  explicitIntertwinerRequired : Bool := true
  consumerFactorizationRequired : Bool := true
  sameObjectRequiredForSemanticTransfer : Bool := true
  sharedGroupNameSufficient : Bool := false
  sharedCardinalitySufficient : Bool := false
  sharedPhaseRowsSufficientForStateIdentity : Bool := false

def canonicalC3DownstreamBoundary : C3DownstreamConsumerBoundary := {}

end Integration.EisensteinArithmeticCMTerminalMaxCutExact
