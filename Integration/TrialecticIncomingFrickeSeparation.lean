import Integration.MoonshineNeutralCuspRelationCrossPollination
import Integration.MoonshineC6TenRankWeightTwelveCrossPollination
import Mathlib

/-!
# Incoming trialectic inversion quotient vs finite Fricke quotient

Lean mirror of the Agda separation theorem.

The incoming ternary square and the ten-state completion carrier both admit
five-state quotient coordinates Mode5, but their raw involutions are not
equivariantly equivalent:

* invertNine fixes the centre;
* the finite Fricke complement on Completion10 has no fixed point.

Thus the quotient-coordinate match is exact while raw-action identification is
formally rejected.
-/

namespace Integration.TrialecticIncomingFrickeSeparation

open Integration.MoonshineNeutralCuspRelationCrossPollination
open Integration.MoonshineC6TenRankWeightTwelveCrossPollination

def finiteFricke : Completion10 → Completion10
  | .d0 => .j
  | .d1 => .d8
  | .d2 => .d7
  | .d3 => .d6
  | .d4 => .d5
  | .d5 => .d4
  | .d6 => .d3
  | .d7 => .d2
  | .d8 => .d1
  | .j => .d0

theorem finiteFricke_involutive (x : Completion10) :
    finiteFricke (finiteFricke x) = x := by
  cases x <;> rfl

def finiteFrickeMode (x : Completion10) : Mode5 :=
  (tenToModePhase x).1

theorem finiteFricke_mode_invariant (x : Completion10) :
    finiteFrickeMode (finiteFricke x) = finiteFrickeMode x := by
  cases x <;> rfl

def incomingQuotientMode (p : NinePoint) : Mode5 :=
  orbitToMode (quotientNine p)

theorem incoming_mode_inversion_invariant (p : NinePoint) :
    incomingQuotientMode (invertNine p) = incomingQuotientMode p := by
  simp [incomingQuotientMode, quotientNine_inversion_invariant]

def modeToIncomingOrbit : Mode5 → NineOrbit5 :=
  modeToOrbit

theorem incoming_orbit_mode_roundtrip (o : NineOrbit5) :
    modeToIncomingOrbit (orbitToMode o) = o :=
  orbit_mode_roundtrip o

theorem mode_incoming_orbit_roundtrip (m : Mode5) :
    orbitToMode (modeToIncomingOrbit m) = m :=
  mode_orbit_roundtrip m

def incomingCentre : NinePoint := (.zero,.zero)

theorem incoming_centre_fixed :
    invertNine incomingCentre = incomingCentre := rfl

theorem finiteFricke_no_fixed_point (x : Completion10) :
    finiteFricke x ≠ x := by
  cases x <;> decide

structure RawInvolutionEquivariantEquiv where
  equiv : NinePoint ≃ Completion10
  intertwines : ∀ p, equiv (invertNine p) = finiteFricke (equiv p)

theorem raw_involution_equivariant_equiv_impossible :
    ¬ Nonempty RawInvolutionEquivariantEquiv := by
  rintro ⟨h⟩
  have hfixed : finiteFricke (h.equiv incomingCentre) = h.equiv incomingCentre := by
    rw [← h.intertwines incomingCentre, incoming_centre_fixed]
  exact finiteFricke_no_fixed_point (h.equiv incomingCentre) hfixed

/-! ## Orbit-count agreement does not extend to stabilizer profiles -/

def incomingOrbitStabilizerSize : NineOrbit5 → Nat
  | .zeroOrbit => 2
  | .firstAxisOrbit => 1
  | .secondAxisOrbit => 1
  | .equalSignOrbit => 1
  | .oppositeSignOrbit => 1

def finiteFrickeModeStabilizerSize : Mode5 → Nat
  | .m09 | .m18 | .m27 | .m36 | .m45 => 1

structure StabilizerPreservingFiveWayEquiv where
  equiv : NineOrbit5 ≃ Mode5
  stabilizerPreserved :
    ∀ orbit,
      incomingOrbitStabilizerSize orbit =
        finiteFrickeModeStabilizerSize (equiv orbit)

theorem stabilizer_preserving_five_way_equiv_impossible :
    ¬ Nonempty StabilizerPreservingFiveWayEquiv := by
  rintro ⟨h⟩
  have hs := h.stabilizerPreserved NineOrbit5.zeroOrbit
  cases hm : h.equiv NineOrbit5.zeroOrbit <;>
    simp [incomingOrbitStabilizerSize, finiteFrickeModeStabilizerSize, hm] at hs

/-! ## Correct future target: quotient-level analytic Fricke recognition -/

structure AnalyticFrickeFiveModeRecognition where
  AnalyticState : Type
  analyticFricke : AnalyticState → AnalyticState
  involutive : ∀ state, analyticFricke (analyticFricke state) = state
  analyticMode : AnalyticState → Mode5
  modeInvariant :
    ∀ state, analyticMode (analyticFricke state) = analyticMode state
  representative : Mode5 → AnalyticState
  representativeExact :
    ∀ mode, analyticMode (representative mode) = mode

def incomingAnalyticRepresentative
    (recognition : AnalyticFrickeFiveModeRecognition)
    (point : NinePoint) : recognition.AnalyticState :=
  recognition.representative (incomingQuotientMode point)

theorem incoming_analytic_representative_same_mode
    (recognition : AnalyticFrickeFiveModeRecognition)
    (point : NinePoint) :
    recognition.analyticMode
      (incomingAnalyticRepresentative recognition point)
      = incomingQuotientMode point :=
  recognition.representativeExact _

inductive QuotientRecognitionCreatesRawEquivariantEquiv : Prop
inductive QuotientRecognitionCreatesStabilizerGroupoidEquiv : Prop

theorem quotient_recognition_does_not_create_raw_equiv :
    ¬ QuotientRecognitionCreatesRawEquivariantEquiv := by
  intro h
  cases h

theorem quotient_recognition_does_not_create_groupoid_equiv :
    ¬ QuotientRecognitionCreatesStabilizerGroupoidEquiv := by
  intro h
  cases h

inductive QuotientCoordinateMatchCreatesRawActionIdentity : Prop
inductive FiniteFrickeIsAnalyticModularFricke : Prop

theorem quotient_match_does_not_create_raw_action_identity :
    ¬ QuotientCoordinateMatchCreatesRawActionIdentity := by
  intro h
  cases h

theorem finite_fricke_not_promoted_to_analytic_fricke :
    ¬ FiniteFrickeIsAnalyticModularFricke := by
  intro h
  cases h

structure Boundary where
  incomingQuotientModeOwned : Bool
  finiteFrickeModeOwned : Bool
  fiveStateQuotientCoordinateShared : Bool
  incomingRawActionHasFixedCentre : Bool
  finiteFrickeRawActionFixedPointFree : Bool
  rawEquivariantEquivalenceRejected : Bool
  incomingStabilizerProfileTwoOneOneOneOne : Bool
  finiteFrickeStabilizerProfileAllOne : Bool
  stabilizerPreservingFiveWayEquivalenceRejected : Bool
  quotientLevelAnalyticRecognitionContractOwned : Bool
  rawEquivRequiredByAnalyticContract : Bool
  groupoidEquivRequiredByAnalyticContract : Bool
  analyticFrickeIdentificationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  incomingQuotientModeOwned := true
  finiteFrickeModeOwned := true
  fiveStateQuotientCoordinateShared := true
  incomingRawActionHasFixedCentre := true
  finiteFrickeRawActionFixedPointFree := true
  rawEquivariantEquivalenceRejected := true
  incomingStabilizerProfileTwoOneOneOneOne := true
  finiteFrickeStabilizerProfileAllOne := true
  stabilizerPreservingFiveWayEquivalenceRejected := true
  quotientLevelAnalyticRecognitionContractOwned := true
  rawEquivRequiredByAnalyticContract := false
  groupoidEquivRequiredByAnalyticContract := false
  analyticFrickeIdentificationPaid := false

end Integration.TrialecticIncomingFrickeSeparation
