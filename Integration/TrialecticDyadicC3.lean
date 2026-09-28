import Integration.TrialecticDyadicLocalComplement
import Mathlib

/-!
# Participant C3 symmetry of dyadic T4 × T5 charts

Cyclic relabelling uses:
  new A = old B
  new B = old C
  new C = old A.

This cycles the original dyadic local charts AB -> BC -> CA and has order 3.
It is distinct from the square D4 chart symmetry.
-/

namespace Integration.TrialecticDyadicC3

open Integration.TrialecticDyadicT4
open Integration.TrialecticDyadicLocalComplement
open Integration.MoonshineTrialecticSurfaceConsumerRouting
open Integration.MoonshineMonstrousExponentTrialecticCodec

def rotateABC : T9Carrier → T9Carrier
  | (a,b,c) =>
      (
        ⟨b.y,b.z,b.x⟩,
        ⟨c.y,c.z,c.x⟩,
        ⟨a.y,a.z,a.x⟩
      )

theorem rotateABC_three_times (state : T9Carrier) :
    rotateABC (rotateABC (rotateABC state)) = state := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

def bcAsAB : BCSection → ABSection
  | ⟨bb,bc,cb,cc⟩ => ⟨bb,bc,cb,cc⟩

def caAsAB : CASection → ABSection
  | ⟨cc,ca,ac,aa⟩ => ⟨cc,ca,ac,aa⟩

def caAsBC : CASection → BCSection
  | ⟨cc,ca,ac,aa⟩ => ⟨cc,ca,ac,aa⟩

def abAsCA : ABSection → CASection
  | ⟨aa,ab,ba,bb⟩ => ⟨aa,ab,ba,bb⟩

theorem restrictAB_after_rotate_is_BC (state : T9Carrier) :
    restrictAB (rotateABC state) = bcAsAB (restrictBC state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem restrictAB_after_rotate_twice_is_CA (state : T9Carrier) :
    restrictAB (rotateABC (rotateABC state)) =
      caAsAB (restrictCA state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem restrictBC_after_rotate_is_CA (state : T9Carrier) :
    restrictBC (rotateABC state) = caAsBC (restrictCA state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem restrictCA_after_rotate_is_AB (state : T9Carrier) :
    restrictCA (rotateABC state) = abAsCA (restrictAB state) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

inductive ParticipantC3EqualsSquareD4 : Prop
inductive ParticipantC3CreatesPreferredChart : Prop

theorem participant_c3_not_identified_with_square_d4 :
    ¬ ParticipantC3EqualsSquareD4 := by
  intro h
  cases h

theorem participant_c3_does_not_create_preferred_chart :
    ¬ ParticipantC3CreatesPreferredChart := by
  intro h
  cases h

structure Boundary where
  participantC3Owned : Bool
  participantC3OrderThree : Bool
  abCyclesToBC : Bool
  abCyclesTwiceToCA : Bool
  allDyadicLocalChartsConjugate : Bool
  squareD4Identified : Bool
  preferredChartClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  participantC3Owned := true
  participantC3OrderThree := true
  abCyclesToBC := true
  abCyclesTwiceToCA := true
  allDyadicLocalChartsConjugate := true
  squareD4Identified := false
  preferredChartClaimed := false

end Integration.TrialecticDyadicC3
