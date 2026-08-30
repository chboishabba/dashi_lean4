import Cuisine.UmamiTransport

/-!
# The second typed cross-domain dependency of the cuisine record, audited

`SituatedMoleWorld` stores two bridges as fields: the hyperfabric bridge, which
`Cuisine.HyperfabricGuard` audits, and
`DASHI.Culture.KnotWeaveTopologyCultureBridge`, which had not been audited.
This file mirrors the proof-relevant part of that module and settles what it
carries.

The negative parts, as for the hyperfabric bridge:

* `knotWeaveGate` is constant and `KnotWeaveGuard` is a singleton
  (`knotWeaveGuard_unique`), so the "admissibility gate" of the observation
  surface carries no information;
* the four lanes and the four guards are just enumerations — distinct
  (`lanes_nodup`, `guards_nodup`), and nothing more is stated about them.

But — unlike the eight-element triad-surface vocabulary of the hyperfabric
bridge, which provably cannot be read as ternary structure — the knot/weave/braid
material is genuinely a **three-element carrier with three parallel three-element
role families**, and it does support the ternary structure:

* `observeKnotWeaveCarrier` is injective (`observe_injective`), and each of its
  three components is a bijection (`topologicalRole_bijective` etc.), so all four
  families are one object;
* `knotWeaveEquivTrit : KnotWeaveCarrier ≃ Trit` — a canonical identification
  with the balanced-ternary digit, canonical because the Agda enumeration order
  and the observation map fix it;
* `rotateCarrier` (knot → weave → braid → knot) is carried to the tone rotation
  (`knotWeaveEquivTrit_rotate`), so this carrier *is* a trit with its rotation.
  There is no fail-closed order here, which is exactly why the obstruction of
  `Cuisine.SeveritySeam.exists_severity_seam` does not apply;
* consequently a knot-weave field over the Monster prime base is a hyperfabric
  section (`knotWeaveFabric`), and the carrier rotation is realised on the
  cuisine side by radical seasoning (`knotWeave_rotation_is_seasoning`).

Boundary: `KnotWeaveCarrier` is a three-element set.  Nothing about knots,
weaving, braids, or any culture is asserted; the Agda module's own guard list
forbids exactly such promotions and is mirrored here.
-/

namespace Cuisine.KnotWeave

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth rotateTri)
open AgdaMirror.TritBridge (toTriTruth)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.Hyperfabric
open Cuisine.UmamiTransport

/-! ## Mirrors -/

inductive KnotWeaveCarrier | knotCarrier | weaveCarrier | braidCarrier
  deriving DecidableEq, Fintype, Repr

inductive TopologicalOperatorRole | localBindingRole | repeatedInterlaceRole | orderedCrossingRole
  deriving DecidableEq, Fintype, Repr

inductive SemanticCultureRole | memoryBindingRole | motifTransmissionRole | conflictNegotiationRole
  deriving DecidableEq, Fintype, Repr

inductive KnotWeaveOperator | bindOperator | interlaceOperator | crossOperator
  deriving DecidableEq, Fintype, Repr

open KnotWeaveCarrier TopologicalOperatorRole SemanticCultureRole KnotWeaveOperator

/-- Mirror of the Agda record `KnotWeaveObservation` (its `cultureAxis` field is
an element of a further enumeration and is not needed for anything proved
here). -/
structure KnotWeaveObservation where
  topologicalRole : TopologicalOperatorRole
  semanticRole : SemanticCultureRole
  operator : KnotWeaveOperator
  deriving DecidableEq, Repr

/-- Mirror of `observeKnotWeaveCarrier`. -/
def observe : KnotWeaveCarrier → KnotWeaveObservation
  | knotCarrier => ⟨localBindingRole, memoryBindingRole, bindOperator⟩
  | weaveCarrier => ⟨repeatedInterlaceRole, motifTransmissionRole, interlaceOperator⟩
  | braidCarrier => ⟨orderedCrossingRole, conflictNegotiationRole, crossOperator⟩

/-- Mirror of `KnotWeaveGuard`, which has one constructor. -/
inductive KnotWeaveGuard | boundedSemanticTopologyGuard
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `knotWeaveGate`, which is constant. -/
def gate (_ : KnotWeaveObservation) : KnotWeaveGuard := .boundedSemanticTopologyGuard

inductive Lane
  | knotSemanticCarrierLane | weavePatternCarrierLane | braidCrossingCarrierLane
  | inverseCultureOperatorLinkLane
  deriving DecidableEq, Fintype, Repr

def canonicalLanes : List Lane :=
  [.knotSemanticCarrierLane, .weavePatternCarrierLane, .braidCrossingCarrierLane,
    .inverseCultureOperatorLinkLane]

inductive Guard
  | NoCulturalUniversalPromotion | NoIdentityOrQualiaClosurePromotion
  | NoAuthorityPromotion | NoContextFreeEquivalencePromotion
  deriving DecidableEq, Fintype, Repr

def canonicalGuards : List Guard :=
  [.NoCulturalUniversalPromotion, .NoIdentityOrQualiaClosurePromotion,
    .NoAuthorityPromotion, .NoContextFreeEquivalencePromotion]

/-! ## What the gate and the enumerations do (and do not) carry -/

/-- The admissibility gate is a singleton type: it records nothing. -/
instance : Unique KnotWeaveGuard where
  default := .boundedSemanticTopologyGuard
  uniq x := by cases x; rfl

theorem knotWeaveGuard_unique (g h : KnotWeaveGuard) : g = h := by
  cases g; cases h; rfl

theorem gate_constant (o o' : KnotWeaveObservation) : gate o = gate o' := rfl

theorem lanes_nodup : canonicalLanes.Nodup := by decide

theorem lanes_length : canonicalLanes.length = 4 := rfl

theorem lanes_complete (l : Lane) : l ∈ canonicalLanes := by cases l <;> decide

theorem guards_nodup : canonicalGuards.Nodup := by decide

theorem guards_complete (g : Guard) : g ∈ canonicalGuards := by cases g <;> decide

/-! ## The carrier really is a trit -/

theorem observe_injective : Function.Injective observe := by decide

theorem topologicalRole_bijective :
    Function.Bijective (fun c => (observe c).topologicalRole) := by
  constructor
  · decide
  · intro r; cases r
    · exact ⟨knotCarrier, rfl⟩
    · exact ⟨weaveCarrier, rfl⟩
    · exact ⟨braidCarrier, rfl⟩

theorem semanticRole_bijective :
    Function.Bijective (fun c => (observe c).semanticRole) := by
  constructor
  · decide
  · intro r; cases r
    · exact ⟨knotCarrier, rfl⟩
    · exact ⟨weaveCarrier, rfl⟩
    · exact ⟨braidCarrier, rfl⟩

theorem operator_bijective :
    Function.Bijective (fun c => (observe c).operator) := by
  constructor
  · decide
  · intro r; cases r
    · exact ⟨knotCarrier, rfl⟩
    · exact ⟨weaveCarrier, rfl⟩
    · exact ⟨braidCarrier, rfl⟩

/-- **The knot/weave/braid carrier is the balanced-ternary digit.**  Unlike the
eight triad-surface *names* of the hyperfabric bridge, this carrier has exactly
three elements in a fixed order, so the identification is canonical for that
order. -/
def knotWeaveEquivTrit : KnotWeaveCarrier ≃ Trit where
  toFun
    | knotCarrier => .neg
    | weaveCarrier => .zer
    | braidCarrier => .pos
  invFun
    | .neg => knotCarrier
    | .zer => weaveCarrier
    | .pos => braidCarrier
  left_inv := by decide
  right_inv := by decide

/-- The cycle knot → weave → braid → knot. -/
def rotateCarrier : KnotWeaveCarrier → KnotWeaveCarrier
  | knotCarrier => weaveCarrier
  | weaveCarrier => braidCarrier
  | braidCarrier => knotCarrier

theorem rotateCarrier_order_three (c : KnotWeaveCarrier) :
    rotateCarrier (rotateCarrier (rotateCarrier c)) = c := by cases c <;> rfl

theorem rotateCarrier_no_fixpoint (c : KnotWeaveCarrier) : rotateCarrier c ≠ c := by
  cases c <;> decide

/-- **Equivariance.**  The carrier cycle is the tone rotation. -/
theorem knotWeaveEquivTrit_rotate (c : KnotWeaveCarrier) :
    toTriTruth (knotWeaveEquivTrit (rotateCarrier c)) =
      rotateTri (toTriTruth (knotWeaveEquivTrit c)) := by
  cases c <;> rfl

/-! ## Knot-weave fields over the Monster base -/

/-- A knot-weave field: one carrier value per supersingular prime. -/
abbrev KnotWeaveField := SSP → KnotWeaveCarrier

/-- **Knot-weave fields are hyperfabric sections.** -/
def knotWeaveFabric : KnotWeaveField ≃ Fabric :=
  Equiv.arrowCongr (Equiv.refl SSP) knotWeaveEquivTrit

@[simp] theorem knotWeaveFabric_apply (K : KnotWeaveField) (p : SSP) :
    knotWeaveFabric K p = knotWeaveEquivTrit (K p) := rfl

/-- Pointwise carrier rotation of a field. -/
def rotateField (K : KnotWeaveField) : KnotWeaveField := fun p => rotateCarrier (K p)

/-- The field rotation is the fabric rotation. -/
theorem knotWeaveFabric_rotateField (K : KnotWeaveField) :
    knotWeaveFabric (rotateField K) = fabricRot (knotWeaveFabric K) := by
  funext p
  cases h : K p <;> simp [rotateField, fabricRot, knotWeaveEquivTrit, h] <;> rfl

/-- **The knot-weave rotation is cuisine-side seasoning.**  For a field that is
the transport of a cuisine intensity, rotating every carrier is exactly
composing that intensity with the radical intensity. -/
theorem knotWeave_rotation_is_seasoning (K : KnotWeaveField) (u : ℕ)
    (h : knotWeaveFabric K = umamiFabric u) :
    knotWeaveFabric (rotateField K) = umamiFabric (umamiCompose u radicalIntensity) := by
  rw [knotWeaveFabric_rotateField, h, umamiFabric_season]

/-- Every knot-weave field is the transport of a cuisine intensity, so the
hypothesis of the previous theorem is never vacuous. -/
theorem exists_intensity (K : KnotWeaveField) : ∃ u : ℕ, knotWeaveFabric K = umamiFabric u :=
  ⟨fabricIntensity (knotWeaveFabric K), (umamiFabric_fabricIntensity _).symm⟩

end Cuisine.KnotWeave
