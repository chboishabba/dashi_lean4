import Mathlib

/-!
# Lean mirror of `DASHI/Education/EarlyLearningEntitlementRouteSeparationExact.agda`

Transcription of the module's two carriers and their coordinate readings:

* `DeliveryArchitecture` with `universalEntitlement`, `parallelFamilyRoute` and
  `professionalFloor`;
* `NordicPolicyArchitecture` with `nordicUniversalEntitlement` and
  `nordicParallelCashCare`;
* `EntitlementRouteBoundary`, whose four `Bool` fields are each pinned by a
  companion equation field, transcribed with the pins.

The Agda module proves two non-factorability results — the entitlement reading
does not determine the route reading, and the route reading does not determine
the professional floor.  Both are re-proved here.  What the Agda module does
*not* state, and what §3 below adds, is what happens when those two negatives
are **composed**.

This is a transcription of visible Agda text; no Agda module has been
typechecked here.
-/

namespace AgdaMirror.EntitlementRoutes

/-- Agda `data DeliveryArchitecture`. -/
inductive Architecture
  | universalProfessional | universalPlusParallelFamily | substitutionaryExit
  deriving DecidableEq, Repr, Fintype

open Architecture

/-- Agda `universalEntitlement`. -/
def universalEntitlement : Architecture → Bool
  | universalProfessional => true
  | universalPlusParallelFamily => true
  | substitutionaryExit => false

/-- Agda `parallelFamilyRoute`. -/
def parallelFamilyRoute : Architecture → Bool
  | universalProfessional => false
  | universalPlusParallelFamily => true
  | substitutionaryExit => true

/-- Agda `professionalFloor`. -/
def professionalFloor : Architecture → Bool
  | universalProfessional => true
  | universalPlusParallelFamily => true
  | substitutionaryExit => false

/-- Agda `sameEntitlementDifferentRoutes`. -/
theorem same_entitlement_different_routes :
    universalEntitlement universalProfessional =
        universalEntitlement universalPlusParallelFamily ∧
      parallelFamilyRoute universalProfessional ≠
        parallelFamilyRoute universalPlusParallelFamily := by decide

/-- Agda `sameParallelRouteDifferentProfessionalFloor`. -/
theorem same_route_different_floor :
    parallelFamilyRoute universalPlusParallelFamily =
        parallelFamilyRoute substitutionaryExit ∧
      professionalFloor universalPlusParallelFamily ≠
        professionalFloor substitutionaryExit := by decide

/-- **The reading the Agda module does not record.**  On this carrier the
entitlement reading and the professional-floor reading are the *same function*.
-/
theorem entitlement_eq_floor : universalEntitlement = professionalFloor := by
  funext a; cases a <;> rfl

/-! ## The Nordic sub-carrier -/

/-- Agda `data NordicPolicyArchitecture`. -/
inductive NordicArchitecture
  | universalAccessWithoutParallelCashCare | universalAccessWithParallelCashCare
  deriving DecidableEq, Repr, Fintype

open NordicArchitecture

/-- Agda `nordicUniversalEntitlement`: constant. -/
def nordicUniversalEntitlement : NordicArchitecture → Bool
  | universalAccessWithoutParallelCashCare => true
  | universalAccessWithParallelCashCare => true

/-- Agda `nordicParallelCashCare`. -/
def nordicParallelCashCare : NordicArchitecture → Bool
  | universalAccessWithoutParallelCashCare => false
  | universalAccessWithParallelCashCare => true

/-- Agda `nordicArchitecturesDifferAtParallelRoute`. -/
theorem nordic_architectures_differ_at_parallel_route :
    nordicUniversalEntitlement universalAccessWithoutParallelCashCare =
        nordicUniversalEntitlement universalAccessWithParallelCashCare ∧
      nordicParallelCashCare universalAccessWithoutParallelCashCare ≠
        nordicParallelCashCare universalAccessWithParallelCashCare := by decide

/-! ## The boundary record -/

/-- Agda `record EntitlementRouteBoundary`: four `Bool` fields, each pinned by a
companion equation field. -/
structure EntitlementRouteBoundary where
  /-- `universalEntitlementMeansUniformRoute`. -/
  entitlementMeansUniformRoute : Bool
  /-- Its pin. -/
  entitlementMeansUniformRouteIsFalse : entitlementMeansUniformRoute = false
  /-- `parallelFamilySupportMeansProfessionalExit`. -/
  parallelSupportMeansProfessionalExit : Bool
  /-- Its pin. -/
  parallelSupportMeansProfessionalExitIsFalse : parallelSupportMeansProfessionalExit = false
  /-- `entitlementAndRouteRemainIndependentCoordinates`. -/
  coordinatesIndependent : Bool
  /-- Its pin. -/
  coordinatesIndependentIsTrue : coordinatesIndependent = true
  /-- `architectureTypeEqualsPermanentCountryIdentity`. -/
  architectureIsCountryIdentity : Bool
  /-- Its pin. -/
  architectureIsCountryIdentityIsFalse : architectureIsCountryIdentity = false

/-- Agda `canonicalEntitlementRouteBoundary`. -/
def canonicalBoundary : EntitlementRouteBoundary where
  entitlementMeansUniformRoute := false
  entitlementMeansUniformRouteIsFalse := rfl
  parallelSupportMeansProfessionalExit := false
  parallelSupportMeansProfessionalExitIsFalse := rfl
  coordinatesIndependent := true
  coordinatesIndependentIsTrue := rfl
  architectureIsCountryIdentity := false
  architectureIsCountryIdentityIsFalse := rfl

/-- Every field of the boundary record is pinned, so the record has exactly one
possible field assignment and reports no information about the architectures. -/
theorem boundary_fields_are_pinned (b : EntitlementRouteBoundary) :
    b.entitlementMeansUniformRoute = canonicalBoundary.entitlementMeansUniformRoute ∧
      b.parallelSupportMeansProfessionalExit =
        canonicalBoundary.parallelSupportMeansProfessionalExit ∧
      b.coordinatesIndependent = canonicalBoundary.coordinatesIndependent ∧
      b.architectureIsCountryIdentity = canonicalBoundary.architectureIsCountryIdentity :=
  ⟨b.entitlementMeansUniformRouteIsFalse, b.parallelSupportMeansProfessionalExitIsFalse,
    b.coordinatesIndependentIsTrue, b.architectureIsCountryIdentityIsFalse⟩

end AgdaMirror.EntitlementRoutes
