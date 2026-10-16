import Integration.EisensteinLatticeCountingRegression
import Integration.EisensteinCMOrderActionExact
import Integration.EisensteinJZeroInertPrimeLocalFactorExact
import Integration.EisensteinJZeroCanonicalCubicCharacterExact
import Integration.EisensteinJZeroSplitJacobiCyclotomicExact
import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
import Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact
import Integration.EisensteinJZeroAllGoodPrimeLocalExact
import Integration.EisensteinJZeroBadPrimeTwoExact
import Integration.EisensteinJZeroBadPrimeThreeExact
import Integration.EisensteinJZero36a1ExternalSourceReceipt

/-!
# Eisenstein arithmetic -> CM terminal max-cut

This is the machine-readable terminal owner for the original Eisenstein
programme.  The obsolete visual target

    Cantor/radix scale series ?= Eisenstein norm-shell series

remains retired.

ARITHMETIC SHELL LANE

    (a,b) in Z^2
      -> a+b*omega in Z[omega]
      -> N(a+b*omega)=a^2-a*b+b^2
      -> universal norm-shell / chi_-3 divisor formula
      -> 6*zeta*L(chi_-3) on Re(s)>1.

SAME-CARRIER POINT-GROUP CM LANE

    Z[omega]
      -> Frac(Z[omega])
      -> E : y^2=x^3+1, j(E)=0
      -> Phi(x,y)=(omega*x,y)
      -> Phi^2+Phi+1=0 on Mathlib's native point group
      -> Z[omega] -> End(E(Frac(Z[omega]))).

GOOD-PRIME LOCAL LANE (`p > 3`)

INERT (`p % 3 = 2`)
    chi_-3(p) = -1,
    #E(F_p)=p+1,
    a_p=0,
    P_p(T)=1+p*T^2.

SPLIT (`p % 3 = 1`)
    exact order-three character
      -> cube subgroup = character kernel
      -> literal cube-fibre certificate
      -> Mathlib Jacobi trace
      -> J in Z[zeta_6]
      -> J*conj(J)=p
      -> explicit Z[zeta_6]=Z[omega] carrier weld
      -> z_p=a+b*omega : EisensteinQA
      -> N(z_p)=p
      -> a_p=-(2*a-b)
      -> P_p(T)=1+(2*a-b)T+p*T^2
      -> existing six-unit x split-choice normal form.

BAD-PRIME REDUCTION LANE

External provenance identifies the concrete rational curve as Cremona 36a1
and records conductor 36 / short-model discriminant -432; those metadata stay
external-source attributed and are not used as kernel proof authority.

The repository independently proves literal singular reductions over BOTH
`F_2` and `F_3`, explicit singular points, formal derivative vanishing, and
finite affine/naive-projective counts.  Those literal facts are not promoted
to elliptic local L-factors: reduction-type/conductor semantics (Neron/Kodaira
or an equivalent formal owner) are still missing from pinned Mathlib.

GLOBAL ARITHMETIC FRONTIER

The finite good-prime branch is no longer a blocker.  Remaining payments are:

    bad-prime 2/3 reduction types + elliptic local factors
      -> same-curve Groessencharacter/Hecke globalization
      -> Euler-product agreement
      -> global elliptic/Hecke L-function agreement.

GEOMETRIC CM FRONTIER

Independently, the point-group ring action does not yet give a faithful
geometric CM embedding.  The remaining geometric chain is

    elliptic morphism/isogeny-degree carrier
      -> faithful geometric Z[omega] embedding
      -> degree(a+b*omega)=N(a+b*omega).

Attribution boundary:
* Mathlib owns generic affine elliptic point-group, quadratic-algebra,
  finite-field, multiplicative-character, primitive-root, Jacobi-sum,
  conjugation and complex-norm infrastructure.
* DASHI/Lean owns the specialisations/compositions and same-object welds.
* Stein/Cremona-derived table and PARI/GP manual metadata remain externally
  attributed in `EisensteinJZero36a1ExternalSourceReceipt`.
* No external source is promoted into a kernel proof object.
* `6*zeta*L(chi_-3)` is not silently relabelled as `L(E,s)`.
-/

namespace Integration.EisensteinArithmeticCMTerminalMaxCutExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroCMConcreteExact
open Integration.EisensteinCMOrderActionExact
open Integration.EisensteinJZeroInertPrimeLocalFactorExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact
open Integration.EisensteinJZeroSplitJacobiCyclotomicExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact
open Integration.EisensteinJZeroAllGoodPrimeLocalExact

inductive EisensteinArithmeticCMBlocker
  | missingGeometricIsogenyDegreeCarrier
  | missingFaithfulGeometricCMEmbedding
  | missingEndomorphismDegreeNormTheorem
  | missingBadPrimeReductionTypesAndLocalFactors
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

  arbitraryOrderThreeKernelEqualsCubesPaid : Bool
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

  external36a1MetadataReceiptRecorded : Bool
  badPrimeTwoLiteralReductionPaid : Bool
  badPrimeTwoSingularityPaid : Bool
  badPrimeTwoPointCountPaid : Bool
  badPrimeThreeLiteralReductionPaid : Bool
  badPrimeThreeSingularityPaid : Bool
  badPrimeThreePointCountPaid : Bool
  badPrimeReductionTypesPaid : Bool
  badPrimeEllipticLocalFactorsPaid : Bool

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

/-- Machine-readable terminal status after the finite/local max-cut. -/
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

  arbitraryOrderThreeKernelEqualsCubesPaid := true
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

  external36a1MetadataReceiptRecorded := true
  badPrimeTwoLiteralReductionPaid := true
  badPrimeTwoSingularityPaid := true
  badPrimeTwoPointCountPaid := true
  badPrimeThreeLiteralReductionPaid := true
  badPrimeThreeSingularityPaid := true
  badPrimeThreePointCountPaid := true
  badPrimeReductionTypesPaid := false
  badPrimeEllipticLocalFactorsPaid := false

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
  firstGlobalArithmeticBlocker := missingBadPrimeReductionTypesAndLocalFactors

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
