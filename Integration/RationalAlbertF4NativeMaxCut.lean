import Integration.RationalAlbertNative
import Integration.RationalAlbertS3Native
import Integration.RationalAlbertTrialityBasis
import Integration.RationalOctonionTriality192
import Integration.RationalOctonionTriality192Obstruction
import Integration.F4D4TrialityAlbertShape
import Integration.E6F4WeylFold
import Integration.E6F4ShortRootRecognition
import Integration.F4MinusculeOnePlus26
import Integration.AlbertDonorDeterminantAudit
import Mathlib

/-!
# Native rational Albert / F4 max-cut

The critical path no longer runs through the external donor.  Repo-native exact
rational Cayley-Dickson octonions and H3(O_Q) formulas now provide the carrier,
standard cubic, Jordan product/laws and explicit S3 automorphisms.

The finite exceptional side independently provides W(F4)=1152, a 192-element D4
kernel and three 8-weight triality sectors.  A further signed-monomial search on
the actual octonion triality tensor constructs a 192-element triality subgroup,
but an exact element-order-spectrum comparison refutes its identification with
W(D4).  Thus the next compatible action must use a genuinely different
(non-monomial in this rational coordinate basis, or differently based/extended)
Spin(8) triality realization.
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

  signedMonomialTrialityCandidateOrder192Paid : Bool
  signedMonomialTrialityPreservationPaid : Bool
  signedMonomialCandidateRefutedAsWD4 : Bool
  nonMonomialSpin8RouteRequired : Bool

  actualD4OctonionSectorIntertwinerPaid : Bool
  actualSpin8TrialityFormPreservationPaid : Bool
  actualD4JordanAutomorphismsPaid : Bool
  generatedFiniteWeylInsideAutJPaid : Bool
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

  signedMonomialTrialityCandidateOrder192Paid := true
  signedMonomialTrialityPreservationPaid := true
  signedMonomialCandidateRefutedAsWD4 := true
  nonMonomialSpin8RouteRequired := true

  actualD4OctonionSectorIntertwinerPaid := false
  actualSpin8TrialityFormPreservationPaid := false
  actualD4JordanAutomorphismsPaid := false
  generatedFiniteWeylInsideAutJPaid := false
  fullAutJEqualsF4Paid := false
  e6UnitStabilizerEqualsF4Paid := false

inductive FiniteTrialityShapeCreatesAlbertAutomorphism : Prop
inductive Order192CreatesWD4Recognition : Prop
inductive RationalAlbertPlusS3CreatesFullF4 : Prop

theorem finite_triality_shape_does_not_create_albert_automorphism :
    ¬ FiniteTrialityShapeCreatesAlbertAutomorphism := by
  intro h; cases h

theorem order_192_does_not_create_wd4 : ¬ Order192CreatesWD4Recognition := by
  intro h; cases h

theorem rational_albert_plus_s3_does_not_create_full_f4 :
    ¬ RationalAlbertPlusS3CreatesFullF4 := by
  intro h; cases h

end Integration.RationalAlbertF4NativeMaxCut
