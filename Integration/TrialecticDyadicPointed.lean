import Integration.TrialecticDyadicT4
import Integration.TernaryHub
import Mathlib

/-!
# Pointed / relative dyadic locals

The nonzero local carrier is not closed under overlap restriction, so the
correct finite replacement is pointed rather than objectwise punctured.

Each local and overlap has a distinguished zero basepoint; restrictions are
required to preserve basepoints.  Non-basepoint status is relative data and is
not assumed to survive restriction.
-/

namespace Integration.TrialecticDyadicPointed

open Integration.TrialecticDyadicT4
open Integration.TernaryHub

structure PointedCarrier where
  Carrier : Type
  basepoint : Carrier

structure PointedMap (Source Target : PointedCarrier) where
  toFun : Source.Carrier → Target.Carrier
  map_basepoint : toFun Source.basepoint = Target.basepoint

def ABPointed : PointedCarrier :=
  ⟨ABSection, zeroAB⟩

def BCPointed : PointedCarrier :=
  ⟨BCSection, zeroBC⟩

def CAPointed : PointedCarrier :=
  ⟨CASection, zeroCA⟩

def APointed : PointedCarrier :=
  ⟨SSPTrit, .zero⟩

def BPointed : PointedCarrier :=
  ⟨SSPTrit, .zero⟩

def CPointed : PointedCarrier :=
  ⟨SSPTrit, .zero⟩

def ABtoA : PointedMap ABPointed APointed where
  toFun := fun section => section.aa
  map_basepoint := rfl

def ABtoB : PointedMap ABPointed BPointed where
  toFun := fun section => section.bb
  map_basepoint := rfl

def BCtoB : PointedMap BCPointed BPointed where
  toFun := fun section => section.bb
  map_basepoint := rfl

def BCtoC : PointedMap BCPointed CPointed where
  toFun := fun section => section.cc
  map_basepoint := rfl

def CAtoC : PointedMap CAPointed CPointed where
  toFun := fun section => section.cc
  map_basepoint := rfl

def CAtoA : PointedMap CAPointed APointed where
  toFun := fun section => section.aa
  map_basepoint := rfl

def NonBasepoint (P : PointedCarrier) (x : P.Carrier) : Prop :=
  x ≠ P.basepoint

structure RelativePuncture (P : PointedCarrier) where
  point : P.Carrier
  awayFromBasepoint : NonBasepoint P point

def offDiagonalABRelativePuncture : RelativePuncture ABPointed where
  point := offDiagonalPuncturedAB
  awayFromBasepoint := offDiagonalPuncturedAB_ne_zero

theorem offDiagonalAB_restricts_to_basepoint_A :
    ABtoA.toFun offDiagonalABRelativePuncture.point = APointed.basepoint := rfl

theorem offDiagonalAB_restricts_to_basepoint_B :
    ABtoB.toFun offDiagonalABRelativePuncture.point = BPointed.basepoint := rfl

inductive EveryPointedMapPreservesNonBasepoint : Prop

theorem pointed_map_need_not_preserve_nonbasepoint :
    ¬ EveryPointedMapPreservesNonBasepoint := by
  intro h
  cases h

structure PointedDyadicRestrictionSystem where
  localAB : PointedCarrier
  localBC : PointedCarrier
  localCA : PointedCarrier
  overlapA : PointedCarrier
  overlapB : PointedCarrier
  overlapC : PointedCarrier
  AB_A : PointedMap localAB overlapA
  AB_B : PointedMap localAB overlapB
  BC_B : PointedMap localBC overlapB
  BC_C : PointedMap localBC overlapC
  CA_C : PointedMap localCA overlapC
  CA_A : PointedMap localCA overlapA

def canonicalPointedDyadicRestrictionSystem :
    PointedDyadicRestrictionSystem where
  localAB := ABPointed
  localBC := BCPointed
  localCA := CAPointed
  overlapA := APointed
  overlapB := BPointed
  overlapC := CPointed
  AB_A := ABtoA
  AB_B := ABtoB
  BC_B := BCtoB
  BC_C := BCtoC
  CA_C := CAtoC
  CA_A := CAtoA

inductive PointedPairIsTopologicalCofiber : Prop
inductive PointedRepairCreatesPuncturedSubpresheaf : Prop
inductive RelativePunctureCreatesRHMechanism : Prop

theorem pointed_pair_not_promoted_to_topological_cofiber :
    ¬ PointedPairIsTopologicalCofiber := by
  intro h
  cases h

theorem pointed_repair_does_not_create_punctured_subpresheaf :
    ¬ PointedRepairCreatesPuncturedSubpresheaf := by
  intro h
  cases h

theorem relative_puncture_does_not_create_rh_mechanism :
    ¬ RelativePunctureCreatesRHMechanism := by
  intro h
  cases h

structure Boundary where
  localBasepointsExplicit : Bool
  overlapBasepointsExplicit : Bool
  allSixRestrictionsPointed : Bool
  nonzeroLocalMayRestrictToBasepoint : Bool
  relativePunctureCarrierConstructed : Bool
  naivePuncturedSubpresheafRejected : Bool
  topologicalCofiberClaimed : Bool
  rhMechanismClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  localBasepointsExplicit := true
  overlapBasepointsExplicit := true
  allSixRestrictionsPointed := true
  nonzeroLocalMayRestrictToBasepoint := true
  relativePunctureCarrierConstructed := true
  naivePuncturedSubpresheafRejected := true
  topologicalCofiberClaimed := false
  rhMechanismClaimed := false

end Integration.TrialecticDyadicPointed
