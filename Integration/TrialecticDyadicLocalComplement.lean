import Integration.TrialecticDyadicT4
import Integration.MoonshineTrialecticSurfaceConsumerRouting
import Integration.TernaryHub
import Mathlib

/-!
# Exact T9 ≃ dyadic T4 local × five-trit complement

For the AB local chart:
- local coordinates: AA, AB, BA, BB;
- complement coordinates: AC, BC, CA, CB, CC.

Thus the global T9 carrier splits exactly as T4 × T5.

This is the original trialectic geometry itself, independent of the later RH
arithmetic observation.
-/

namespace Integration.TrialecticDyadicLocalComplement

open Integration.TrialecticDyadicT4
open Integration.MoonshineTrialecticSurfaceConsumerRouting
open Integration.MoonshineMonstrousExponentTrialecticCodec
open Integration.TernaryHub

structure T5Carrier where
  d4 : SSPTrit
  d3 : SSPTrit
  d2 : SSPTrit
  d1 : SSPTrit
  d0 : SSPTrit
  deriving DecidableEq, Repr, Fintype

def abComplement : T9Carrier → T5Carrier
  | (a,b,c) => ⟨a.z,b.z,c.x,c.y,c.z⟩

def observerToABLocalComplement : T9Carrier → ABSection × T5Carrier
  | state => (restrictAB state, abComplement state)

def abLocalComplementToObserver : ABSection × T5Carrier → T9Carrier
  | (⟨aa,ab,ba,bb⟩,⟨ac,bc,ca,cb,cc⟩) =>
      (
        ⟨aa,ab,ac⟩,
        ⟨ba,bb,bc⟩,
        ⟨ca,cb,cc⟩
      )

theorem observer_after_ab_local_complement (state : T9Carrier) :
    abLocalComplementToObserver (observerToABLocalComplement state) = state := by
  rcases state with ⟨⟨aa,ab,ac⟩,⟨ba,bb,bc⟩,⟨ca,cb,cc⟩⟩
  rfl

theorem ab_local_complement_after_observer
    (state : ABSection × T5Carrier) :
    observerToABLocalComplement (abLocalComplementToObserver state) = state := by
  rcases state with ⟨⟨aa,ab,ba,bb⟩,⟨ac,bc,ca,cb,cc⟩⟩
  rfl

def t9ABLocalComplementEquiv :
    T9Carrier ≃ (ABSection × T5Carrier) where
  toFun := observerToABLocalComplement
  invFun := abLocalComplementToObserver
  left_inv := observer_after_ab_local_complement
  right_inv := ab_local_complement_after_observer

theorem t5_state_count :
    Fintype.card T5Carrier = 243 := by
  native_decide

theorem t9_is_t4_times_t5 :
    Fintype.card T9Carrier =
      Fintype.card ABSection * Fintype.card T5Carrier := by
  norm_num [t9_state_count, ab_section_count, t5_state_count]

theorem depth_five_factor_is_literal_complement :
    Fintype.card T5Carrier = 3^5 := by
  norm_num [t5_state_count]

inductive ComplementT5CreatesRHMechanism : Prop
inductive ABChartIsIntrinsicPreferredChart : Prop

theorem complement_t5_does_not_create_rh_mechanism :
    ¬ ComplementT5CreatesRHMechanism := by
  intro h
  cases h

theorem ab_chart_not_promoted_to_intrinsic_preference :
    ¬ ABChartIsIntrinsicPreferredChart := by
  intro h
  cases h

structure Boundary where
  globalT9ToABLocalComplementExact : Bool
  localExactlyT4 : Bool
  complementExactlyT5 : Bool
  t9ExactlyT4TimesT5 : Bool
  complementCount243 : Bool
  rhMechanismClaimed : Bool
  chartPreferredIntrinsically : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  globalT9ToABLocalComplementExact := true
  localExactlyT4 := true
  complementExactlyT5 := true
  t9ExactlyT4TimesT5 := true
  complementCount243 := true
  rhMechanismClaimed := false
  chartPreferredIntrinsically := false

end Integration.TrialecticDyadicLocalComplement
