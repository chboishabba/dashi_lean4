import Mathlib
import Integration.OggSSPSmallCharacteristicRecognition
import Integration.OggSSPP2F4FrobeniusCandidateNoGo

/-!
# Opposite small-characteristic arithmetic acquisition directions

The two raw finite-field Frobenius candidates fail in opposite directions.

p=3:
* raw F9/F3 Frobenius has six orbit components;
* the current residual target has two;
* a concrete equivariant extension-coordinate quotient exists;
* that quotient is not a pi0 embedding, hence not full recognition.

p=2:
* raw F4/F2 Frobenius has three orbit components;
* the retained residual target has ten;
* no full recognition exists;
* no uniform marked lift 3*k can produce 10.

Thus, relative to the raw field-orbit semantics:
* p=3 points toward quotient/compression;
* p=2 points toward a richer marked enrichment/cover.

This classifies search direction only. It does not identify either missing
arithmetic residual source.
-/

namespace Integration.OggSSPSmallCharacteristicAcquisitionDirection

open Integration.OggSSPSmallCharacteristicRecognition
open Integration.OggSSPP2F4FrobeniusCandidateNoGo
open Integration.ActionOrbitRecognition

inductive AcquisitionDirection
  | quotientOrCompression
  | markedEnrichmentOrCover
  deriving DecidableEq, Repr

def p3AcquisitionDirection : AcquisitionDirection :=
  .quotientOrCompression

def p2AcquisitionDirection : AcquisitionDirection :=
  .markedEnrichmentOrCover

theorem p3_raw_orbit_cardinality :
    Fintype.card F9Orbit = 6 :=
  f9_orbit_cardinality

theorem p3_residual_orbit_cardinality :
    Fintype.card P3Orbit = 2 :=
  p3_target_orbit_cardinality

theorem p3_raw_is_three_times_residual :
    Fintype.card F9Orbit = 3 * Fintype.card P3Orbit := by
  decide

theorem p3_concrete_target_surjection :
    Function.Surjective extensionCoordinate :=
  extensionCoordinate_surjective

theorem p3_extension_coordinate_equivariant :
    ∀ g x,
      extensionCoordinate (f9Act g x) =
        p3Act g (extensionCoordinate x) :=
  extensionCoordinate_equivariant

theorem p3_quotient_not_pi0_embedding :
    ¬ Nonempty (Pi0Embedding f9ExtensionCoordinateOrbitRecognition) :=
  f9_extension_coordinate_not_pi0_embedding

theorem p3_whole_f9_not_full_recognition
    (F : ActionRecognitionFunctor f9FrobeniusAction p3Action) :
    ¬ Nonempty (FullRecognition F f9OrbitPresentation p3OrbitPresentation) :=
  no_full_f9_frobenius_recognition_to_p3 F

theorem p2_raw_orbit_cardinality :
    Fintype.card F4Orbit = 3 :=
  f4_orbit_cardinality

theorem p2_residual_orbit_cardinality :
    Fintype.card P2State = 10 :=
  p2_retained_target_cardinality

theorem p2_whole_f4_not_full_recognition
    (F : ActionRecognitionFunctor f4FrobeniusAction p2DiscreteAction) :
    ¬ Nonempty (FullRecognition F f4OrbitPresentation p2DiscreteOrbitPresentation) :=
  no_full_f4_frobenius_recognition_to_p2 F

theorem p2_no_uniform_marked_lift :
    ¬ ∃ k : Nat, uniformMarkedOrbitCount k = 10 :=
  no_uniform_three_orbit_lift_to_ten

inductive PromotionError
  | p3QuotientIsArithmeticResidualSource
  | p2EnrichmentDirectionConstructsMarkedSource
  | fieldOrbitDirectionDeterminesExternalArithmetic
  deriving DecidableEq, Repr

structure Boundary where
  p3SixToTwoCompressionExact : Bool
  p3ConcreteEquivariantQuotientOwned : Bool
  p3WholeFieldFullRecognitionRejected : Bool
  p2ThreeToTenExpansionExact : Bool
  p2WholeFieldFullRecognitionRejected : Bool
  p2UniformMarkedLiftRejected : Bool
  p2MarkedEnrichmentRequiredIfRawF4OrbitSemanticsRetained : Bool
  eitherDirectionIdentifiesArithmeticResidualSource : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  p3SixToTwoCompressionExact := true
  p3ConcreteEquivariantQuotientOwned := true
  p3WholeFieldFullRecognitionRejected := true
  p2ThreeToTenExpansionExact := true
  p2WholeFieldFullRecognitionRejected := true
  p2UniformMarkedLiftRejected := true
  p2MarkedEnrichmentRequiredIfRawF4OrbitSemanticsRetained := true
  eitherDirectionIdentifiesArithmeticResidualSource := false

end Integration.OggSSPSmallCharacteristicAcquisitionDirection
