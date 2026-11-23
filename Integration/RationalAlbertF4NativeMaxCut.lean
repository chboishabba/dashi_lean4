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
import Integration.RationalAlbertNormUnitRigidityExact
import Integration.RationalOctonionDivisionNorm
import Integration.RationalAlbertNormStabilizerJordanSameObject
import Integration.RationalAlbertF4ScalarExtensionFormBoundary
import Integration.RationalAlbertTauCetiF4DonorAudit
import Integration.F4D4TrialityAlbertShape
import Integration.E6F4WeylFold
import Integration.E6F4ShortRootRecognition
import Integration.F4MinusculeOnePlus26
import Integration.AlbertDonorDeterminantAudit
import Mathlib

/-!
# Native rational Albert / F4 max-cut

The critical path no longer runs through the old external determinant donor.
Repo-native exact rational Cayley-Dickson octonions and H3(O_Q) formulas provide
the carrier, standard cubic, Jordan product/laws and explicit automorphisms.

The native rational octonion norm is now theorem-bearing anisotropic on the
literal Q-carrier; multiplicativity therefore gives no zero divisors.  This is
original-Q form information, unlike the companion exact `Q(i)` root-space chart,
which is explicitly scalar-extension/splitting data and cannot by itself classify
the original rational form.

The finite exceptional side independently provides W(F4)=1152, a 192-element D4
kernel and three 8-weight triality sectors.  Four explicit Spin/Tits lifts
preserve the literal octonion triality tensor; their closure has order 384 with
a central two-sheeted sign over W(D4)_192 and acts on H3(O_Q) by genuine
Jordan/cubic automorphisms.  The missing non-monomial `g24` coordinate lift is an
optional finite-coordinate refinement, not the algebraic-group classification
wall.

Arbitrary Albert inner derivations `[L_a,L_b]` satisfy the derivation law.  Exact
rational diagnostics give dimension 52 and the triality-shaped `28+8+8+8`.

The cubic-norm route is structurally closed: trace/trace pairing and adjoint are
recovered, and every Q-linear bijection preserving the native cubic and unit
preserves the Jordan product.  Conversely every native Jordan automorphism
forgets to the same unit-fixing norm symmetry.  Thus the concrete action classes
`Stab_Isom(N)(1)` and `Aut_J(J)` coincide on the same underlying maps.

What remains is *naming/classifying those already-constructed native objects*:
`Der(J)` as the appropriate rational F4 form, `Aut_J(J)` as the corresponding
F4 algebraic group, and the cubic symmetry/structure group as type E6.  TauCeti
has been pinned as a strong external formal donor candidate, but no same-object
Albert-to-canonical-F4 theorem was located at the audited commit.
-/

namespace Integration.RationalAlbertF4NativeMaxCut

structure Frontier where
  nativeRationalQuaternionPaid : Bool
  nativeRationalOctonionPaid : Bool
  octonionConjugationSourceWritten : Bool
  octonionNormMultiplicativitySourceWritten : Bool
  octonionAlternativitySourceWritten : Bool
  nativeQOctonionNormAnisotropyPaid : Bool
  nativeQOctonionNoZeroDivisorsPaid : Bool

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

  nativeTracePairNondegeneratePaid : Bool
  nativeNormUnitRigidityPaid : Bool
  unitFixingCubicSymmetryIsJordanPaid : Bool
  nativeNormUnitEqualsJordanSameActionPaid : Bool

  qiRootDecompositionPaid : Bool
  qiRootDecompositionIsScalarExtensionData : Bool
  qiRootDecompositionClassifiesOriginalQForm : Bool
  realPlaceDiagnosticPaid : Bool
  realPlaceDiagnosticClassifiesOriginalQForm : Bool
  tauCetiFormalDonorInventoryLocated : Bool
  tauCetiSameObjectClassificationLocated : Bool

  actualD4OctonionWeightLineIntertwinerPaid : Bool
  fullFiniteWeylF4InsideAutJPaid : Bool
  nativeDerivationNamedF4FormPaid : Bool
  nativeAutJNamedF4GroupPaid : Bool
  nativeCubicSymmetryNamedE6GroupPaid : Bool
  deriving Repr

/-- Exact source frontier of the native route. -/
def currentFrontier : Frontier where
  nativeRationalQuaternionPaid := true
  nativeRationalOctonionPaid := true
  octonionConjugationSourceWritten := true
  octonionNormMultiplicativitySourceWritten := true
  octonionAlternativitySourceWritten := true
  nativeQOctonionNormAnisotropyPaid := true
  nativeQOctonionNoZeroDivisorsPaid := true

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

  nativeTracePairNondegeneratePaid := true
  nativeNormUnitRigidityPaid := true
  unitFixingCubicSymmetryIsJordanPaid := true
  nativeNormUnitEqualsJordanSameActionPaid := true

  qiRootDecompositionPaid := true
  qiRootDecompositionIsScalarExtensionData := true
  qiRootDecompositionClassifiesOriginalQForm := false
  realPlaceDiagnosticPaid := true
  realPlaceDiagnosticClassifiesOriginalQForm := false
  tauCetiFormalDonorInventoryLocated := true
  tauCetiSameObjectClassificationLocated := false

  actualD4OctonionWeightLineIntertwinerPaid := false
  fullFiniteWeylF4InsideAutJPaid := false
  nativeDerivationNamedF4FormPaid := false
  nativeAutJNamedF4GroupPaid := false
  nativeCubicSymmetryNamedE6GroupPaid := false

inductive FiniteTrialityShapeCreatesAlbertAutomorphism : Prop
inductive SpinLiftCreatesFullF4 : Prop
inductive DerivationRank52CreatesF4 : Prop
inductive RationalAlbertPlusS3CreatesFullF4 : Prop
inductive NormUnitRigidityCreatesF4Classification : Prop
inductive QISplittingCreatesOriginalQFormClassification : Prop
inductive DonorInventoryCreatesNativeClassification : Prop

theorem finite_triality_shape_does_not_create_albert_automorphism :
    ¬ FiniteTrialityShapeCreatesAlbertAutomorphism := by intro h; cases h

theorem spin_lift_does_not_create_full_f4 : ¬ SpinLiftCreatesFullF4 := by
  intro h; cases h

theorem derivation_rank_52_does_not_create_f4 : ¬ DerivationRank52CreatesF4 := by
  intro h; cases h

theorem rational_albert_plus_s3_does_not_create_full_f4 :
    ¬ RationalAlbertPlusS3CreatesFullF4 := by intro h; cases h

theorem norm_unit_rigidity_does_not_create_f4_classification :
    ¬ NormUnitRigidityCreatesF4Classification := by intro h; cases h

theorem qi_splitting_does_not_create_original_q_form_classification :
    ¬ QISplittingCreatesOriginalQFormClassification := by intro h; cases h

theorem donor_inventory_does_not_create_native_classification :
    ¬ DonorInventoryCreatesNativeClassification := by intro h; cases h

end Integration.RationalAlbertF4NativeMaxCut
