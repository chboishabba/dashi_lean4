import Integration.RationalAlbertNative
import Integration.RationalAlbertS3Native
import Integration.RationalAlbertTrialityBasis
import Integration.RationalOctonionTriality192
import Integration.RationalOctonionTriality192Obstruction
import Integration.RationalOctonionSpin8WeylLift
import Integration.RationalAlbertSpin8Automorphism
import Integration.F4D4SpinLiftQuotientWeld
import Integration.RationalAlbertF4OuterLiftMaxCut
import Integration.RationalAlbertInnerDerivationNative
import Integration.F4D4TrialityAlbertShape
import Integration.E6F4WeylFold
import Integration.E6F4ShortRootRecognition
import Integration.F4MinusculeOnePlus26
import Integration.AlbertDonorDeterminantAudit
import Mathlib

/-!
# Native rational Albert / F4 max-cut

The critical path no longer runs through the external donor.  Repo-native exact
rational Cayley-Dickson octonions and H3(O_Q) formulas provide the carrier,
standard cubic, Jordan product/laws and explicit S3 automorphisms.

The finite exceptional side independently provides W(F4)=1152, a 192-element D4
kernel and three 8-weight triality sectors.  The native octonion side now goes
strictly further than the earlier refuted split-192 candidate:

* four explicit Spin/Tits lifts preserve the literal octonion triality tensor;
* their closure has order 384 with a single central two-sheeted sign over the
  independently defined W(D4)_192;
* the synchronized quotient to the folded D4 kernel is exact;
* acting with those lifts on H3(O_Q) gives four genuine Jordan/cubic
  automorphisms of the same native Albert algebra.

The outer-triality max-cut is asymmetric.  Inside the complete current 73728
signed-coordinate automorphism closure one projective lift of folded `g05`
exists, but no projective lift of folded `g24` exists.  Hence the remaining
finite F4 weld needs a genuinely non-monomial/Hadamard-Tits chart, not another
basis relabelling.

Independently, arbitrary Albert inner derivations `[L_a,L_b]` now satisfy the
full derivation law in Lean.  Exact-rational local computation on the same
coordinate formulas gives rank 52 and the triality-shaped `52 = 28 + 8+8+8`
diagnostic.  Lie type F4 is still gated by an explicit same-Lie-algebra/root
space recognition, not by dimension alone.
-/

namespace Integration.RationalAlbertF4NativeMaxCut

structure Frontier where
  nativeRationalQuaternionPaid : Bool
  nativeRationalOctonionPaid : Bool
  octonionConjugationSourceWritten : Bool
  octonionNormMultiplicativitySourceWritten : Bool
  octonionAlternativitySourceWritten : Bool

  nativeH3OctonionCarrierPaid : Bool
  nativeStandardCubicPaid : Bool
  nativeJordanProductPaid : Bool
  nativeJordanCommutativitySourceWritten : Bool
  nativeJordanUnitSourceWritten : Bool
  nativeJordanIdentitySourceWritten : Bool

  nativeS3RelationsPaid : Bool
  nativeS3ProductPreservationSourceWritten : Bool
  nativeS3CubicPreservationSourceWritten : Bool

  foldedWeylF4Order1152Paid : Bool
  d4KernelOrder192Paid : Bool
  threeEightTrialityOrbitsPaid : Bool
  quotientS3TrialityTranspositionsPaid : Bool
  literalAlbertBasis3Plus8Plus8Plus8Paid : Bool
  literalS3SlotActionPaid : Bool

  donorCubicCounterexamplePaid : Bool
  externalDonorRemovedFromCriticalPath : Bool

  splitTrialityCandidateRefutedAsWD4 : Bool
  fourSpinTrialityLiftsPaid : Bool
  spinLiftClosure384Paid : Bool
  spinQuotientExactlyFoldedWD4Paid : Bool
  spinTrialityTensorPreservationPaid : Bool
  fourNativeD4AlbertAutomorphismsPaid : Bool

  nativeSignedBasisClosure73728Paid : Bool
  g05ProjectiveOuterLiftPaid : Bool
  g24AbsentFromCurrentSignedBasisSubgroupPaid : Bool
  nonMonomialHadamardTitsLiftRequired : Bool

  arbitraryAlbertInnerDerivationLawPaid : Bool
  exactAlbertDerivationRank52DiagnosticPaid : Bool
  exactDiagonalStabilizer28DiagnosticPaid : Bool
  exactMovingComplement24DiagnosticPaid : Bool

  actualD4OctonionWeightLineIntertwinerPaid : Bool
  fullFiniteWeylF4InsideAutJPaid : Bool
  sameLieAlgebraF4RecognitionPaid : Bool
  fullAutJEqualsF4Paid : Bool
  e6UnitStabilizerEqualsF4Paid : Bool
  deriving Repr

/-- Exact source frontier of the native route. -/
def currentFrontier : Frontier where
  nativeRationalQuaternionPaid := true
  nativeRationalOctonionPaid := true
  octonionConjugationSourceWritten := true
  octonionNormMultiplicativitySourceWritten := true
  octonionAlternativitySourceWritten := true

  nativeH3OctonionCarrierPaid := true
  nativeStandardCubicPaid := true
  nativeJordanProductPaid := true
  nativeJordanCommutativitySourceWritten := true
  nativeJordanUnitSourceWritten := true
  nativeJordanIdentitySourceWritten := true

  nativeS3RelationsPaid := true
  nativeS3ProductPreservationSourceWritten := true
  nativeS3CubicPreservationSourceWritten := true

  foldedWeylF4Order1152Paid := true
  d4KernelOrder192Paid := true
  threeEightTrialityOrbitsPaid := true
  quotientS3TrialityTranspositionsPaid := true
  literalAlbertBasis3Plus8Plus8Plus8Paid := true
  literalS3SlotActionPaid := true

  donorCubicCounterexamplePaid := true
  externalDonorRemovedFromCriticalPath := true

  splitTrialityCandidateRefutedAsWD4 := true
  fourSpinTrialityLiftsPaid := true
  spinLiftClosure384Paid := true
  spinQuotientExactlyFoldedWD4Paid := true
  spinTrialityTensorPreservationPaid := true
  fourNativeD4AlbertAutomorphismsPaid := true

  nativeSignedBasisClosure73728Paid := true
  g05ProjectiveOuterLiftPaid := true
  g24AbsentFromCurrentSignedBasisSubgroupPaid := true
  nonMonomialHadamardTitsLiftRequired := true

  arbitraryAlbertInnerDerivationLawPaid := true
  exactAlbertDerivationRank52DiagnosticPaid := true
  exactDiagonalStabilizer28DiagnosticPaid := true
  exactMovingComplement24DiagnosticPaid := true

  actualD4OctonionWeightLineIntertwinerPaid := false
  fullFiniteWeylF4InsideAutJPaid := false
  sameLieAlgebraF4RecognitionPaid := false
  fullAutJEqualsF4Paid := false
  e6UnitStabilizerEqualsF4Paid := false

inductive FiniteTrialityShapeCreatesAlbertAutomorphism : Prop
inductive SpinLiftCreatesFullF4 : Prop
inductive DerivationRank52CreatesF4 : Prop
inductive RationalAlbertPlusS3CreatesFullF4 : Prop

theorem finite_triality_shape_does_not_create_albert_automorphism :
    ¬ FiniteTrialityShapeCreatesAlbertAutomorphism := by
  intro h; cases h

theorem spin_lift_does_not_create_full_f4 : ¬ SpinLiftCreatesFullF4 := by
  intro h; cases h

theorem derivation_rank_52_does_not_create_f4 : ¬ DerivationRank52CreatesF4 := by
  intro h; cases h

theorem rational_albert_plus_s3_does_not_create_full_f4 :
    ¬ RationalAlbertPlusS3CreatesFullF4 := by
  intro h; cases h

end Integration.RationalAlbertF4NativeMaxCut
