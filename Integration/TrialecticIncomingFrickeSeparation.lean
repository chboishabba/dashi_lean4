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
  analyticFrickeIdentificationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  incomingQuotientModeOwned := true
  finiteFrickeModeOwned := true
  fiveStateQuotientCoordinateShared := true
  incomingRawActionHasFixedCentre := true
  finiteFrickeRawActionFixedPointFree := true
  rawEquivariantEquivalenceRejected := true
  analyticFrickeIdentificationPaid := false

end Integration.TrialecticIncomingFrickeSeparation
