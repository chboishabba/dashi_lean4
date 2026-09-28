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

structure BCComplement5 where
  ba : SSPTrit
  ca : SSPTrit
  ab : SSPTrit
  ac : SSPTrit
  aa : SSPTrit
  deriving DecidableEq, Repr, Fintype

structure CAComplement5 where
  cb : SSPTrit
  ab : SSPTrit
  bc : SSPTrit
  ba : SSPTrit
  bb : SSPTrit
  deriving DecidableEq, Repr, Fintype

def bcComplement : T9Carrier → BCComplement5
  | (a,b,c) => ⟨b.x,c.x,a.y,a.z,a.x⟩

def caComplement : T9Carrier → CAComplement5
  | (a,b,c) => ⟨c.y,a.y,b.z,b.x,b.y⟩

structure BCLocalComplement where
  local : BCSection
  complement : BCComplement5
  deriving DecidableEq, Repr, Fintype

structure CALocalComplement where
  local : CASection
  complement : CAComplement5
  deriving DecidableEq, Repr, Fintype

def observerToBCLocalComplement (state : T9Carrier) : BCLocalComplement :=
  ⟨restrictBC state, bcComplement state⟩

def bcLocalComplementToObserver : BCLocalComplement → T9Carrier
  | ⟨⟨bb,bc,cb,cc⟩,⟨ba,ca,ab,ac,aa⟩⟩ =>
      (
        ⟨aa,ab,ac⟩,
        ⟨ba,bb,bc⟩,
        ⟨ca,cb,cc⟩
      )

def observerToCALocalComplement (state : T9Carrier) : CALocalComplement :=
  ⟨restrictCA state, caComplement state⟩

def caLocalComplementToObserver : CALocalComplement → T9Carrier
  | ⟨⟨cc,ca,ac,aa⟩,⟨cb,ab,bc,ba,bb⟩⟩ =>
      (
        ⟨aa,ab,ac⟩,
        ⟨ba,bb,bc⟩,
        ⟨ca,cb,cc⟩
      )

theorem bc_local_complement_roundtrip (state : T9Carrier) :
    bcLocalComplementToObserver (observerToBCLocalComplement state) = state := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem ca_local_complement_roundtrip (state : T9Carrier) :
    caLocalComplementToObserver (observerToCALocalComplement state) = state := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

def bcComplementAsABComplement : BCComplement5 → T5Carrier
  | ⟨ba,ca,ab,ac,aa⟩ => ⟨ba,ca,ab,ac,aa⟩

def caComplementAsABComplement : CAComplement5 → T5Carrier
  | ⟨cb,ab,bc,ba,bb⟩ => ⟨cb,ab,bc,ba,bb⟩

theorem ab_factorization_after_rotate_is_bc (state : T9Carrier) :
    observerToABLocalComplement (rotateABC state) =
      (bcAsAB (restrictBC state), bcComplementAsABComplement (bcComplement state)) := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem ab_factorization_after_rotate_twice_is_ca (state : T9Carrier) :
    observerToABLocalComplement (rotateABC (rotateABC state)) =
      (caAsAB (restrictCA state), caComplementAsABComplement (caComplement state)) := by
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
  allDyadicLocalComplementFactorizationsConjugate : Bool
  squareD4Identified : Bool
  preferredChartClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  participantC3Owned := true
  participantC3OrderThree := true
  abCyclesToBC := true
  abCyclesTwiceToCA := true
  allDyadicLocalChartsConjugate := true
  allDyadicLocalComplementFactorizationsConjugate := true
  squareD4Identified := false
  preferredChartClaimed := false

end Integration.TrialecticDyadicC3
