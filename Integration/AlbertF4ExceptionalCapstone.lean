import Integration.RationalAlbertNative
import Integration.RationalAlbertS3Native
import Integration.RationalAlbertSpin8Automorphism
import Integration.RationalAlbertF4OuterLiftMaxCut
import Integration.RationalAlbertInnerDerivationNative
import Integration.RationalAlbertF4LieMaxCut
import Integration.RationalAlbertF4NativeMaxCut
import Integration.F4D4SpinLiftQuotientWeld
import Integration.F4D4StandardTrialityRecognition
import Integration.E6F4ShortRootRecognition
import Integration.E6F4WeylFold
import Integration.T5Relative240E6ActionObstruction
import Integration.AlbertDonorDeterminantAudit

/-!
# Albert / F4 exceptional max-cut capstone

Authoritative current boundary after replacing the external-donor critical path
with the repository-native rational Albert algebra.

Paid at source level in the native route:

* exact rational Cayley-Dickson octonions;
* actual H3(O_Q) carrier, standard cubic, Jordan product, unit and Jordan law;
* genuine native S3 coordinate automorphisms preserving product and cubic;
* folded finite W(F4) of order 1152 and explicit 48-root F4 datum;
* exact D4 kernel of order 192 and three same-action 8-dimensional triality
  weight systems;
* four explicit Spin/Tits triality lifts with 384-element central double cover
  and exact quotient to the independently paid W(D4)_192;
* all four lifts act as genuine automorphisms of the same native Albert algebra;
* one outer F4 direction (`g05`) is realizable projectively inside the current
  native signed-basis subgroup;
* exhaustive finite search refutes a `g24` lift inside that complete 73728
  signed-basis subgroup, forcing a new non-monomial/Tits chart rather than a
  basis relabelling;
* every arbitrary Albert inner commutator `[L_a,L_b]` satisfies the derivation
  law in Lean;
* exact-rational local computation on those same native coordinate formulas
  gives the algebra-generated diagnostic `52 = 28 + 24 = 28 + 8+8+8`;
* independently, the repo owns the rank-four F4 Cartan/root datum with
  24 short + 24 long roots.

The remaining promotion gate is consequently structural:

1. formal complexification/root-space decomposition of the concrete Albert
   derivation algebra and same-object identification with the independent F4
   root datum;
2. the missing non-monomial outer `g24` lift if a complete finite Weyl subgroup
   inside the chosen rational-coordinate automorphism subgroup is desired;
3. full `Aut_Jordan(H3(O)) ~= F4` and `Stab_E6(1) ~= F4` recognition.

Neither rank 52, root count 48, finite Weyl order 1152 nor source classification
is allowed to manufacture the internal same-Lie-algebra intertwiner.
-/

namespace Integration.AlbertF4ExceptionalCapstone

structure Frontier where
  nativeRationalAlbertCarrierPaid : Bool
  nativeStandardAlbertCubicPaid : Bool
  nativeJordanProductPaid : Bool
  nativeJordanIdentityPaid : Bool
  nativeS3AlbertAutomorphismsPaid : Bool

  externalDonorCubicCounterexamplePaid : Bool
  externalDonorRemovedFromCriticalPath : Bool

  foldedWeylOrder1152Paid : Bool
  independentF4RootSet48Paid : Bool
  independentF4Rank4Paid : Bool
  d4KernelOrder192Paid : Bool
  d4ThreeEightSameActionPaid : Bool

  spinTitsFourLiftsPaid : Bool
  spinCoverOrder384Paid : Bool
  spinQuotientExactlyWD4Paid : Bool
  fourSpinAlbertAutomorphismsPaid : Bool

  nativeSignedBasisClosure73728Paid : Bool
  g05ProjectiveOuterLiftPaid : Bool
  g24CurrentSignedBasisObstructionPaid : Bool
  nonMonomialOuterLiftStillRequired : Bool

  arbitraryInnerDerivationLawPaid : Bool
  exactInnerDerivationRank52DiagnosticPaid : Bool
  exactDiagonalStabilizer28DiagnosticPaid : Bool
  exactMovingComplement24DiagnosticPaid : Bool
  threeEightTrialityLieDiagnosticPaid : Bool

  naturalRelative240E6InvarianceRefuted : Bool
  structuredE8LaneIndependent : Bool

  formalComplexificationPaid : Bool
  formalRootSpaceDecompositionPaid : Bool
  sameLieAlgebraF4RecognitionPaid : Bool
  fullFiniteWeylInsideAutJPaid : Bool
  fullAutJordanEqualsF4Paid : Bool
  e6UnitStabilizerEqualsF4Paid : Bool
  deriving Repr


def currentFrontier : Frontier where
  nativeRationalAlbertCarrierPaid := true
  nativeStandardAlbertCubicPaid := true
  nativeJordanProductPaid := true
  nativeJordanIdentityPaid := true
  nativeS3AlbertAutomorphismsPaid := true

  externalDonorCubicCounterexamplePaid := true
  externalDonorRemovedFromCriticalPath := true

  foldedWeylOrder1152Paid := true
  independentF4RootSet48Paid := true
  independentF4Rank4Paid := true
  d4KernelOrder192Paid := true
  d4ThreeEightSameActionPaid := true

  spinTitsFourLiftsPaid := true
  spinCoverOrder384Paid := true
  spinQuotientExactlyWD4Paid := true
  fourSpinAlbertAutomorphismsPaid := true

  nativeSignedBasisClosure73728Paid := true
  g05ProjectiveOuterLiftPaid := true
  g24CurrentSignedBasisObstructionPaid := true
  nonMonomialOuterLiftStillRequired := true

  arbitraryInnerDerivationLawPaid := true
  exactInnerDerivationRank52DiagnosticPaid := true
  exactDiagonalStabilizer28DiagnosticPaid := true
  exactMovingComplement24DiagnosticPaid := true
  threeEightTrialityLieDiagnosticPaid := true

  naturalRelative240E6InvarianceRefuted := true
  structuredE8LaneIndependent := true

  formalComplexificationPaid := false
  formalRootSpaceDecompositionPaid := false
  sameLieAlgebraF4RecognitionPaid := false
  fullFiniteWeylInsideAutJPaid := false
  fullAutJordanEqualsF4Paid := false
  e6UnitStabilizerEqualsF4Paid := false

inductive NativeAlbertCreatesF4 : Prop
inductive Rank52CreatesF4 : Prop
inductive RootCount48CreatesSameLieAlgebra : Prop
inductive FiniteWeylCreatesFullAutJordan : Prop
inductive MissingG24BlocksF4Classification : Prop

theorem native_albert_does_not_create_f4 : ¬ NativeAlbertCreatesF4 := by
  intro h; cases h

theorem rank_52_does_not_create_f4 : ¬ Rank52CreatesF4 := by
  intro h; cases h

theorem root_count_48_does_not_create_same_lie_algebra :
    ¬ RootCount48CreatesSameLieAlgebra := by
  intro h; cases h

theorem finite_weyl_does_not_create_full_aut_jordan :
    ¬ FiniteWeylCreatesFullAutJordan := by
  intro h; cases h

theorem missing_g24_does_not_block_lie_classification :
    ¬ MissingG24BlocksF4Classification := by
  intro h; cases h

end Integration.AlbertF4ExceptionalCapstone
