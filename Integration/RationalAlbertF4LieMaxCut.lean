import Integration.RationalAlbertInnerDerivationNative
import Integration.RationalAlbertF4NativeMaxCut
import Integration.E6F4ShortRootRecognition
import Integration.E6F4WeylFold
import Mathlib

/-!
# Rational Albert derivation algebra -> F4 Lie-recognition max-cut

The actual Jordan algebra now supplies arbitrary inner derivations
`[L_a,L_b]`, and the arbitrary derivation law is theorem-facing in Lean.
Independent exact-rational local computation from the same 27-coordinate
product gives the finite linear-algebra diagnostics recorded below.

Separately, the repository already owns an explicit rank-four F4 Cartan datum,
24 short roots, 24 long roots and a 48-root finite root system.

The remaining theorem is therefore a same-Lie-algebra/root-space recognition,
not another dimension comparison.  In particular, `52`, centerlessness,
perfectness and a rank-four regular centralizer are strong diagnostics but do
not by themselves manufacture Lie type F4.
-/

namespace Integration.RationalAlbertF4LieMaxCut

open Integration.RationalAlbertInnerDerivationNative
open Integration.E6F4ShortRootRecognition
open Integration.E6F4WeylFold

structure ExactDerivationDiagnostic where
  ambientJordanDimension : Nat
  unorderedBasisPairs : Nat
  nonzeroBasisCommutators : Nat
  exactInnerDerivationSpanRank : Nat
  diagonalEvaluationRank : Nat
  diagonalStabilizerDimension : Nat
  slot0RestrictionRank : Nat
  slot1RestrictionRank : Nat
  slot2RestrictionRank : Nat
  allSelectedDerivationIdentitiesExact : Bool
  exactRationalArithmeticOnly : Bool
  scriptPath : String
  deriving Repr

/-- Executable receipt reproduced locally from the same literal native
`jordanProduct`; this is diagnostic authority, not a kernel finrank theorem. -/
def canonicalDerivationDiagnostic : ExactDerivationDiagnostic where
  ambientJordanDimension := 27
  unorderedBasisPairs := 351
  nonzeroBasisCommutators := 324
  exactInnerDerivationSpanRank := 52
  diagonalEvaluationRank := 24
  diagonalStabilizerDimension := 28
  slot0RestrictionRank := 28
  slot1RestrictionRank := 28
  slot2RestrictionRank := 28
  allSelectedDerivationIdentitiesExact := true
  exactRationalArithmeticOnly := true
  scriptPath := "scripts/rational_albert_f4_derivation_probe.py"

/-- Algebra-generated triality decomposition diagnostic.

The 28-dimensional stabilizer fixes all three diagonal idempotents, is block
preserving on the three octonion slots, and has faithful rank-28 images on each
8-dimensional slot.  The complementary evaluation rank is 24 = 8+8+8. -/
structure TrialityLieDiagnostic where
  total : Nat
  diagonalStabilizer : Nat
  movingComplement : Nat
  slotDimensions : Nat × Nat × Nat
  total_eq_52 : total = 52
  stabilizer_eq_28 : diagonalStabilizer = 28
  complement_eq_24 : movingComplement = 24
  slots_eq_8_8_8 : slotDimensions = (8,8,8)


def canonicalTrialityLieDiagnostic : TrialityLieDiagnostic where
  total := 52
  diagonalStabilizer := 28
  movingComplement := 24
  slotDimensions := (8,8,8)
  total_eq_52 := rfl
  stabilizer_eq_28 := rfl
  complement_eq_24 := rfl
  slots_eq_8_8_8 := rfl

/-- Exact promotion target.  A producer must identify root spaces of the
complexified concrete derivation algebra with the independently defined F4 root
set and make the Cartan/bracket structure commute.  The abstract carriers are
left explicit so no root-space theorem is smuggled in through dimensions. -/
structure SameLieAlgebraF4Recognition : Type 1 where
  DerivationCarrier : Type
  ComplexifiedCarrier : Type
  CartanCarrier : Type
  RootSpaceCarrier : FoldedLabel → Type

  derivationDimension52 : Prop
  complexificationOfConcreteAlbertDerivations : Prop
  cartanDimension4 : Prop

  rootSupported : FoldedLabel → Prop
  supportedRootsExactlyF4 : ∀ r, rootSupported r ↔ r ∈ f4RootSet
  nonzeroRootSpacesOneDimensional : ∀ r, r ∈ f4RootSet → Prop

  bracket : ComplexifiedCarrier → ComplexifiedCarrier → ComplexifiedCarrier
  rootBracketCompatibility :
    ∀ α β, α ∈ f4RootSet → β ∈ f4RootSet → Prop

  simpleRootCartanCompatibility : Prop
  sameConcreteBracket : Prop

/-- Standard classification may be recorded as source authority, but it is not
silently converted into the internal same-object record above. -/
structure ClassificationSourceReceipt where
  source : String
  statesAlbertDerivationAlgebraTypeF4 : Bool
  internalSameLieAlgebraRecognitionReproved : Bool
  deriving Repr

def classicalSourceReceipt : ClassificationSourceReceipt where
  source := "Schafer (1966); Jacobson (1968): derivation algebra of the Albert algebra is a form of type F4"
  statesAlbertDerivationAlgebraTypeF4 := true
  internalSameLieAlgebraRecognitionReproved := false

inductive Dimension52CreatesF4 : Prop
inductive RootCount48CreatesSameLieAlgebra : Prop
inductive SourceClassificationCreatesInternalIntertwiner : Prop

theorem dimension_52_does_not_create_f4 : ¬ Dimension52CreatesF4 := by
  intro h; cases h

theorem root_count_48_does_not_create_same_lie_algebra :
    ¬ RootCount48CreatesSameLieAlgebra := by
  intro h; cases h

theorem source_classification_does_not_create_internal_intertwiner :
    ¬ SourceClassificationCreatesInternalIntertwiner := by
  intro h; cases h

structure Boundary where
  arbitraryInnerDerivationLawPaidInLean : Bool
  exactRank52DiagnosticPaid : Bool
  exactDiagonalStabilizer28DiagnosticPaid : Bool
  exactMovingComplement24DiagnosticPaid : Bool
  threeFaithfulEightDimensionalTrialityActionsDiagnosed : Bool
  independentF4CartanPaid : Bool
  independentF4Root48Paid : Bool
  classicalF4DerivationClassificationRecorded : Bool
  formalComplexifiedRootSpaceDecompositionPaid : Bool
  sameLieAlgebraF4RecognitionPaid : Bool
  fullAutAlbertEqualsF4Paid : Bool
  e6UnitStabilizerEqualsF4Paid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  arbitraryInnerDerivationLawPaidInLean := true
  exactRank52DiagnosticPaid := true
  exactDiagonalStabilizer28DiagnosticPaid := true
  exactMovingComplement24DiagnosticPaid := true
  threeFaithfulEightDimensionalTrialityActionsDiagnosed := true
  independentF4CartanPaid := true
  independentF4Root48Paid := true
  classicalF4DerivationClassificationRecorded := true
  formalComplexifiedRootSpaceDecompositionPaid := false
  sameLieAlgebraF4RecognitionPaid := false
  fullAutAlbertEqualsF4Paid := false
  e6UnitStabilizerEqualsF4Paid := false

end Integration.RationalAlbertF4LieMaxCut
