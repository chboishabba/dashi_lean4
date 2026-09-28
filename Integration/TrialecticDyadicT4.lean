import Integration.MoonshineTrialecticSurfaceConsumerRouting
import Integration.BalancedTernaryDepthFiveX6Bridge
import Mathlib

/-!
# Trialectic dyadic local sections are exactly four-trit carriers

Carrier-level Lean mirror of the Agda theorem
`Trialectic369DyadicSectionTriadicKernelExact`.

For a T9 state interpreted as three trit rows A/B/C:

  U_AB = (AA, AB, BA, BB)
  U_BC = (BB, BC, CB, CC)
  U_CA = (CC, CA, AC, AA)

Each local chart is exactly a four-trit carrier, hence has 81 states.  Removing
the all-zero local section gives an 80-state punctured local carrier.

This is a trialectic-local carrier theorem only.  It does not make the RH pole
coefficient a consequence of Grothendieck descent.
-/

namespace Integration.TrialecticDyadicT4

open Integration.MoonshineTrialecticSurfaceConsumerRouting
open Integration.MoonshineMonstrousExponentTrialecticCodec
open Integration.BalancedTernaryDepthFiveX6Bridge

structure ABSection where
  aa : SSPTrit
  ab : SSPTrit
  ba : SSPTrit
  bb : SSPTrit
  deriving DecidableEq, Repr, Fintype

structure BCSection where
  bb : SSPTrit
  bc : SSPTrit
  cb : SSPTrit
  cc : SSPTrit
  deriving DecidableEq, Repr, Fintype

structure CASection where
  cc : SSPTrit
  ca : SSPTrit
  ac : SSPTrit
  aa : SSPTrit
  deriving DecidableEq, Repr, Fintype

def restrictAB : T9Carrier → ABSection
  | (a,b,_) => ⟨a.x,a.y,b.x,b.y⟩

def restrictBC : T9Carrier → BCSection
  | (_,b,c) => ⟨b.y,b.z,c.y,c.z⟩

def restrictCA : T9Carrier → CASection
  | (a,_,c) => ⟨c.z,c.x,a.z,a.x⟩

def abToT4 : ABSection → T4Carrier
  | ⟨aa,ab,ba,bb⟩ => ⟨aa,ab,ba,bb⟩

def t4ToAB : T4Carrier → ABSection
  | ⟨d3,d2,d1,d0⟩ => ⟨d3,d2,d1,d0⟩

def bcToT4 : BCSection → T4Carrier
  | ⟨bb,bc,cb,cc⟩ => ⟨bb,bc,cb,cc⟩

def t4ToBC : T4Carrier → BCSection
  | ⟨d3,d2,d1,d0⟩ => ⟨d3,d2,d1,d0⟩

def caToT4 : CASection → T4Carrier
  | ⟨cc,ca,ac,aa⟩ => ⟨cc,ca,ac,aa⟩

def t4ToCA : T4Carrier → CASection
  | ⟨d3,d2,d1,d0⟩ => ⟨d3,d2,d1,d0⟩

def abT4Equiv : ABSection ≃ T4Carrier where
  toFun := abToT4
  invFun := t4ToAB
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

def bcT4Equiv : BCSection ≃ T4Carrier where
  toFun := bcToT4
  invFun := t4ToBC
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

def caT4Equiv : CASection ≃ T4Carrier where
  toFun := caToT4
  invFun := t4ToCA
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

theorem ab_section_count : Fintype.card ABSection = 81 := by decide
theorem bc_section_count : Fintype.card BCSection = 81 := by decide
theorem ca_section_count : Fintype.card CASection = 81 := by decide

def zeroAB : ABSection :=
  t4ToAB zeroT4

def zeroBC : BCSection :=
  t4ToBC zeroT4

def zeroCA : CASection :=
  t4ToCA zeroT4

abbrev PuncturedAB := {x : ABSection // x ≠ zeroAB}
abbrev PuncturedBC := {x : BCSection // x ≠ zeroBC}
abbrev PuncturedCA := {x : CASection // x ≠ zeroCA}

theorem punctured_ab_count : Fintype.card PuncturedAB = 80 := by
  native_decide

theorem punctured_bc_count : Fintype.card PuncturedBC = 80 := by
  native_decide

theorem punctured_ca_count : Fintype.card PuncturedCA = 80 := by
  native_decide

/-! The same four-trit scale found by the arithmetic analysis is therefore
already present as each original local chart carrier. -/

theorem local_full_vs_punctured_scale :
    Fintype.card ABSection = Fintype.card PuncturedAB + 1 := by
  norm_num [ab_section_count, punctured_ab_count]

theorem rh_pole_count_matches_punctured_local :
    (80 : Nat) = Fintype.card PuncturedAB := by
  simpa using punctured_ab_count.sym

inductive DyadicT4ChartCreatesRHMechanism : Prop
inductive GrothendieckDescentForcesPuncture : Prop

theorem dyadic_t4_chart_does_not_create_rh_mechanism :
    ¬ DyadicT4ChartCreatesRHMechanism := by
  intro h
  cases h

theorem descent_does_not_force_puncture :
    ¬ GrothendieckDescentForcesPuncture := by
  intro h
  cases h

structure Boundary where
  abSectionExactlyT4 : Bool
  bcSectionExactlyT4 : Bool
  caSectionExactlyT4 : Bool
  eachLocalCount81 : Bool
  eachPuncturedLocalCount80 : Bool
  rhPoleMatchesPuncturedLocalCount : Bool
  rhMechanismClaimed : Bool
  punctureForcedByDescent : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  abSectionExactlyT4 := true
  bcSectionExactlyT4 := true
  caSectionExactlyT4 := true
  eachLocalCount81 := true
  eachPuncturedLocalCount80 := true
  rhPoleMatchesPuncturedLocalCount := true
  rhMechanismClaimed := false
  punctureForcedByDescent := false

end Integration.TrialecticDyadicT4
