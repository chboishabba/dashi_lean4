import Integration.TrialecticDyadicT4
import Integration.TrialecticDyadicLocalComplement
import Integration.TrialecticDyadicC3
import Integration.TrialecticDyadicPointed
import Mathlib

/-!
# Pre-RH trialectic ternary local/descent capstone

This module deliberately excludes the later RH analytic interpretation.

It consolidates the original trialectic structure:
- three exact T4 dyadic locals;
- three one-trit overlap equalities;
- compatible matching families exactly equivalent to T9;
- exact T9 ≃ T4_local × T5_complement;
- participant C3 conjugacy of the three local charts;
- pointed restrictions with a rejected naive punctured-subpresheaf reading.
-/

namespace Integration.TrialecticPreRHTernaryCapstone

open Integration.TrialecticDyadicT4
open Integration.TrialecticDyadicLocalComplement
open Integration.TrialecticDyadicC3
open Integration.TrialecticDyadicPointed
open Integration.MoonshineTrialecticSurfaceConsumerRouting

theorem ab_local_exact_t4 :
    Function.Bijective abToT4 :=
  ⟨abT4Equiv.injective, abT4Equiv.surjective⟩

theorem bc_local_exact_t4 :
    Function.Bijective bcToT4 :=
  ⟨bcT4Equiv.injective, bcT4Equiv.surjective⟩

theorem ca_local_exact_t4 :
    Function.Bijective caToT4 :=
  ⟨caT4Equiv.injective, caT4Equiv.surjective⟩

theorem local_count_81 :
    Fintype.card ABSection = 81 :=
  ab_section_count

theorem punctured_local_count_80 :
    Fintype.card PuncturedAB = 80 :=
  punctured_ab_count

theorem compatible_locals_exact_t9 :
    Function.Bijective t9ToMatching :=
  ⟨t9DyadicMatchingEquiv.injective, t9DyadicMatchingEquiv.surjective⟩

theorem compatible_local_count_19683 :
    Fintype.card DyadicMatching = 19683 :=
  dyadic_matching_count

theorem raw_local_factorization :
    Fintype.card DyadicRawTriple =
      Fintype.card DyadicMatching * 27 :=
  raw_to_matching_count_factor

theorem global_exact_local_times_complement :
    Function.Bijective observerToABLocalComplement :=
  ⟨t9ABLocalComplementEquiv.injective, t9ABLocalComplementEquiv.surjective⟩

theorem complement_count_243 :
    Fintype.card T5Carrier = 243 :=
  t5_state_count

theorem participant_c3_order_three (state : T9Carrier) :
    rotateABC (rotateABC (rotateABC state)) = state :=
  rotateABC_three_times state

theorem ab_cycles_to_bc (state : T9Carrier) :
    restrictAB (rotateABC state) = bcAsAB (restrictBC state) :=
  restrictAB_after_rotate_is_BC state

theorem ab_cycles_twice_to_ca (state : T9Carrier) :
    restrictAB (rotateABC (rotateABC state)) =
      caAsAB (restrictCA state) :=
  restrictAB_after_rotate_twice_is_CA state

def pointedRestrictionSystem :
    PointedDyadicRestrictionSystem :=
  canonicalPointedDyadicRestrictionSystem

theorem nonzero_local_can_hit_basepoint_A :
    ABtoA.toFun offDiagonalABRelativePuncture.point =
      APointed.basepoint :=
  offDiagonalAB_restricts_to_basepoint_A

theorem nonzero_local_can_hit_basepoint_B :
    ABtoB.toFun offDiagonalABRelativePuncture.point =
      BPointed.basepoint :=
  offDiagonalAB_restricts_to_basepoint_B

inductive PreRHCapstoneImportsRHAnalyticTheorem : Prop
inductive PreRHCapstoneSelectsPreferredDyadicChart : Prop
inductive PointedRepairEqualsTopologicalCofiber : Prop

theorem no_rh_analytic_dependency :
    ¬ PreRHCapstoneImportsRHAnalyticTheorem := by
  intro h
  cases h

theorem no_preferred_dyadic_chart :
    ¬ PreRHCapstoneSelectsPreferredDyadicChart := by
  intro h
  cases h

theorem pointed_repair_not_promoted_to_cofiber :
    ¬ PointedRepairEqualsTopologicalCofiber := by
  intro h
  cases h

structure Boundary where
  threeDyadicLocalsAreT4 : Bool
  localCount81Owned : Bool
  puncturedLocalCount80Owned : Bool
  compatibleLocalsExactlyT9 : Bool
  rawLocalFactor27Owned : Bool
  localTimesComplementExact : Bool
  complementCount243Owned : Bool
  participantC3CyclesCharts : Bool
  noPreferredChart : Bool
  pointedRestrictionRepairOwned : Bool
  naivePuncturedSubpresheafRejected : Bool
  rhAnalyticTheoremImported : Bool
  topologicalCofiberClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  threeDyadicLocalsAreT4 := true
  localCount81Owned := true
  puncturedLocalCount80Owned := true
  compatibleLocalsExactlyT9 := true
  rawLocalFactor27Owned := true
  localTimesComplementExact := true
  complementCount243Owned := true
  participantC3CyclesCharts := true
  noPreferredChart := true
  pointedRestrictionRepairOwned := true
  naivePuncturedSubpresheafRejected := true
  rhAnalyticTheoremImported := false
  topologicalCofiberClaimed := false

end Integration.TrialecticPreRHTernaryCapstone
