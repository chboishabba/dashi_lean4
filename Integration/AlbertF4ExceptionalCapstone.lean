import Integration.AlbertExternalDonor
import Integration.AlbertDonorDeterminantAudit
import Integration.AlbertScalarTraceless
import Integration.AlbertJordanAutomorphism
import Integration.AlbertMinusculeWeightLines
import Integration.E6MinusculeWeightModule
import Integration.AlbertLinearMinusculeTransport
import Integration.AlbertStructureTransport
import Integration.TernaryAlbertLinearBasisWeld
import Integration.E6F4WeylFold
import Integration.E6F4ShortRootRecognition
import Integration.F4MinusculeOnePlus26
import Integration.F4D4TrialityAlbertShape
import Integration.F4FiniteInvariantNonuniqueness
import Integration.AlbertTrialityCubicCompiler
import Integration.AlbertCubicRigidity
import Integration.AlbertF4CompatibilityTerminal
import Integration.AlbertF4ReducedTerminal
import Integration.T5Relative240E6ActionObstruction
import Integration.E8ExceptionalLiftCapstone
import Integration.T5E8IntrinsicRecognitionGate

/-!
# Albert / F4 exceptional max-cut capstone

The finite/representation side is now almost completely paid:

* literal E8 mixed 27 <-> E6 minuscule 27;
* structured ternary 27 -> Schlaefli/minuscule relation geometry;
* canonical 27-dimensional minuscule module and transported weight lines;
* exact scalar/traceless `27 = 1 + 26` theorem;
* folded Weyl image of order 1152 with F4 Coxeter/root signature;
* restriction `27 -> 24 + 3`, with the three zero lines carrying S3;
* exact W(D4) kernel order 192 and three 8-weight triality sectors, giving the
  finite Albert coordinate anatomy `3 + 8 + 8 + 8`;
* full abstract Albert structure transport and terminal compilers;
* natural relative-T5 240 same-action E8 route refuted by E6 non-invariance.

A new audit also finds that the pinned donor's current cubic cross-term is not
promotable as the canonical Albert determinant: on an associative complex
subalgebra an explicit zero-diagonal Hermitian example has ordinary determinant
18 while the donor source expression evaluates to 6.  The donor remains a real
source of H3(O), Jordan identity, trace, triality machinery, and a *candidate*
cubic formula, but that cubic now requires repair before use as an Albert norm.

The terminal algebraic wall is therefore narrower and more honest:

1. repair/validate the actual Freudenthal cubic on H3(O);
2. prove the rank-three cubic-rigidity/product-recovery theorem;
3. align the donor octonion norm/triality data with the finite D4 8v+8s+8c
   sectors and pay cubic preservation for the four folded generators;
4. then identify the full Jordan automorphism group / E6-unit stabilizer with
   F4.  Finite Weyl invariance cannot replace this: exact character checks show
   7 invariant quadratics and 23 invariant cubics on the 26-dimensional finite
   shadow.
-/

namespace Integration.AlbertF4ExceptionalCapstone

open Integration.AlbertExternalDonor
open Integration.AlbertDonorDeterminantAudit
open Integration.AlbertJordanAutomorphism
open Integration.AlbertMinusculeWeightLines

structure Frontier where
  externalAlbertDonorPinned : Bool
  externalH3OctonionicCarrierSourceWritten : Bool
  externalJordanIdentityProducerSourceWritten : Bool
  externalTraceSourceWritten : Bool
  externalCubicCandidateSourceWritten : Bool
  donorCubicComplexCounterexamplePaid : Bool
  donorCurrentCubicPromotableAsAlbertNorm : Bool
  donorOctonionTrialitySourceWritten : Bool
  externalFullCubicIdentitiesSourceWritten : Bool

  nativeScalarTracelessEquivalencePaid : Bool
  nativeFinrank27ImpliesTraceless26Paid : Bool
  e6Minuscule27SameObjectPaidUpstream : Bool
  canonicalMinusculeModule27Paid : Bool
  canonicalMinusculeWeightLinesPaid : Bool
  linearMinusculeTransportFromFinrank27Paid : Bool
  fullAlbertStructureTransportTypedAndPaid : Bool
  transportedJordanAutomorphismCompilerPaid : Bool
  actualTernaryOriginPlus26SplitPaid : Bool
  linearTernaryTracelessBasisTransportPaid : Bool

  foldedWeylOrder1152Paid : Bool
  foldedF4CoxeterSignaturePaid : Bool
  foldedF4RootSet48Paid : Bool
  minusculeRestriction24PlusZero3Paid : Bool
  zeroWeightPermutationImageS3Paid : Bool
  finiteWeylOnePlus26Paid : Bool
  d4KernelOrder192Paid : Bool
  d4ThreeEightOrbitsPaid : Bool
  finiteAlbertThreePlusEightPlusEightPlusEightShapePaid : Bool

  finiteWeylQuadraticInvariantDimensionSevenPaid : Bool
  finiteWeylCubicInvariantDimensionTwentyThreePaid : Bool
  finiteWeylInvarianceDeterminesAlbertCubic : Bool

  trialityCubicCompilerPaid : Bool
  cubicRigidityInterfaceTyped : Bool
  reducedTerminalCompatibilityTyped : Bool
  reducedTerminalCompilesJordanAutomorphisms : Bool

  naturalRelative240E6InvarianceRefuted : Bool
  naturalRelative240SameActionE8Blocked : Bool

  correctedAlbertCubicPaid : Bool
  cubicRigidityPaid : Bool
  actualOctonionTrialitySectorAlignmentPaid : Bool
  fourFoldedCubicPreservationChecksPaid : Bool
  terminalAlbertF4CompatibilityPaid : Bool
  actualF4AutomorphismRecognitionPaid : Bool
  actualE6UnitStabilizerRecognitionPaid : Bool
  actualTernaryAlbertActionCompatibilityPaid : Bool
  alternativeTernary240E8RecognitionPaid : Bool
  deriving Repr

def currentFrontier : Frontier where
  externalAlbertDonorPinned := true
  externalH3OctonionicCarrierSourceWritten := pinnedDonorSurface.h3OctonionicCarrierSourceWritten
  externalJordanIdentityProducerSourceWritten := pinnedDonorSurface.jordanIdentityProducerSourceWritten
  externalTraceSourceWritten := pinnedDonorSurface.traceSourceWritten
  externalCubicCandidateSourceWritten := pinnedDonorSurface.cubicDeterminantSourceWritten
  donorCubicComplexCounterexamplePaid := canonicalBoundary.associativeComplexCounterexamplePaid
  donorCurrentCubicPromotableAsAlbertNorm := canonicalBoundary.donorCurrentDetPromotableAsAlbertNorm
  donorOctonionTrialitySourceWritten := pinnedDonorSurface.octonionTrialityFormSourceWritten
  externalFullCubicIdentitiesSourceWritten := pinnedDonorSurface.fullCubicIdentitiesSourceWritten

  nativeScalarTracelessEquivalencePaid := true
  nativeFinrank27ImpliesTraceless26Paid := true
  e6Minuscule27SameObjectPaidUpstream := true
  canonicalMinusculeModule27Paid := true
  canonicalMinusculeWeightLinesPaid := true
  linearMinusculeTransportFromFinrank27Paid := true
  fullAlbertStructureTransportTypedAndPaid := true
  transportedJordanAutomorphismCompilerPaid := true
  actualTernaryOriginPlus26SplitPaid := true
  linearTernaryTracelessBasisTransportPaid := true

  foldedWeylOrder1152Paid := true
  foldedF4CoxeterSignaturePaid := true
  foldedF4RootSet48Paid := true
  minusculeRestriction24PlusZero3Paid := true
  zeroWeightPermutationImageS3Paid := true
  finiteWeylOnePlus26Paid := true
  d4KernelOrder192Paid := true
  d4ThreeEightOrbitsPaid := true
  finiteAlbertThreePlusEightPlusEightPlusEightShapePaid := true

  finiteWeylQuadraticInvariantDimensionSevenPaid := true
  finiteWeylCubicInvariantDimensionTwentyThreePaid := true
  finiteWeylInvarianceDeterminesAlbertCubic := false

  trialityCubicCompilerPaid := true
  cubicRigidityInterfaceTyped := true
  reducedTerminalCompatibilityTyped := true
  reducedTerminalCompilesJordanAutomorphisms := true

  naturalRelative240E6InvarianceRefuted := true
  naturalRelative240SameActionE8Blocked := true

  correctedAlbertCubicPaid := false
  cubicRigidityPaid := false
  actualOctonionTrialitySectorAlignmentPaid := false
  fourFoldedCubicPreservationChecksPaid := false
  terminalAlbertF4CompatibilityPaid := false
  actualF4AutomorphismRecognitionPaid := false
  actualE6UnitStabilizerRecognitionPaid := false
  actualTernaryAlbertActionCompatibilityPaid := false
  alternativeTernary240E8RecognitionPaid := false

inductive ExternalAlbertCreatesF4 : Prop
inductive FiniteF4WeylCreatesContinuousF4 : Prop
inductive FiniteWeylInvarianceCreatesAlbertCubic : Prop
inductive DonorCandidateCubicCreatesValidatedAlbertNorm : Prop
inductive NaturalT5NoGoBlocksEveryAlternative240Action : Prop

theorem external_albert_does_not_create_f4 : ¬ ExternalAlbertCreatesF4 := by
  intro h; cases h

theorem finite_weyl_f4_does_not_create_continuous_f4 :
    ¬ FiniteF4WeylCreatesContinuousF4 := by
  intro h; cases h

theorem finite_weyl_invariance_does_not_create_albert_cubic :
    ¬ FiniteWeylInvarianceCreatesAlbertCubic := by
  intro h; cases h

theorem donor_candidate_cubic_does_not_create_validated_norm :
    ¬ DonorCandidateCubicCreatesValidatedAlbertNorm := by
  intro h; cases h

theorem natural_t5_no_go_is_not_universal_no_go :
    ¬ NaturalT5NoGoBlocksEveryAlternative240Action := by
  intro h; cases h

end Integration.AlbertF4ExceptionalCapstone
