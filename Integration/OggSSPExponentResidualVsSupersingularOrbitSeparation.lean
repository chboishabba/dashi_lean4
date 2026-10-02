import Mathlib
import Integration.OggSSPExponentResidualArithmeticSource

/-!
# Exponent residual vs supersingular Frobenius orbit-count separation

Lean mirror of the Agda negative-control theorem.

The values below mirror the repository's already-attributed finite normal-form
supersingular spectrum and monstrous-exponent arithmetic.  This file proves
only the cross-module comparison: equality/inequality of the resulting finite
counts.  It does not claim that the normal-form slots are geometric
supersingular elliptic curves, and equal counts do not create same-object
recognition.
-/

namespace Integration.OggSSPExponentResidualVsSupersingularOrbitSeparation

inductive PrimeLane
  | p3 | p5 | p7 | p11
  deriving DecidableEq, Repr

/-- Fixed singleton slots in the repository's normalized Frobenius spectrum. -/
def rationalSupersingularCount : PrimeLane → Nat
  | .p3 => 1
  | .p5 => 1
  | .p7 => 1
  | .p11 => 2

/-- Nontrivial two-orbits in the same normalized spectrum. -/
def frobeniusTwoOrbitCount : PrimeLane → Nat
  | .p3 => 0
  | .p5 => 0
  | .p7 => 0
  | .p11 => 0

def supersingularPi0Count (p : PrimeLane) : Nat :=
  rationalSupersingularCount p + frobeniusTwoOrbitCount p

def supersingularCarrierCount (p : PrimeLane) : Nat :=
  rationalSupersingularCount p + 2 * frobeniusTwoOrbitCount p

theorem p3_supersingular_pi0_is_one :
    supersingularPi0Count .p3 = 1 := rfl

theorem p3_supersingular_carrier_is_one :
    supersingularCarrierCount .p3 = 1 := rfl

theorem p3_exponent_residual_is_two :
    Integration.OggSSPExponentResidualArithmeticSource.expectedResidualCount
      .p3 = 2 := rfl

theorem p3_supersingular_pi0_ne_exponent_residual :
    supersingularPi0Count .p3 ≠
      Integration.OggSSPExponentResidualArithmeticSource.expectedResidualCount
        .p3 := by decide

def ordinaryMonsterExponent : PrimeLane → Option Nat
  | .p3 => none
  | .p5 => some 9
  | .p7 => some 6
  | .p11 => some 2

theorem p5_supersingular_pi0_ne_monster_exponent :
    supersingularPi0Count .p5 ≠ 9 := by decide

theorem p7_supersingular_pi0_ne_monster_exponent :
    supersingularPi0Count .p7 ≠ 6 := by decide

theorem p11_counts_coincide :
    supersingularPi0Count .p11 = 2 := rfl

inductive PromotionError
  | equalCountCreatesSameObject
  | supersingularSpectrumAutomaticallySuppliesExponentResidualSource
  deriving DecidableEq, Repr

inductive ExponentResidualSourceKind
  | supersingularFrobeniusOrbitSpectrum
  | distinctExponentResidualGroupoidRequired
  deriving DecidableEq, Repr

def p3RequiredSourceKind : ExponentResidualSourceKind :=
  .distinctExponentResidualGroupoidRequired

structure Boundary where
  normalizedSupersingularPi0Defined : Bool
  p3SupersingularPi0IsOne : Bool
  p3ExponentResidualIsTwo : Bool
  p3TwoInvariantsSeparated : Bool
  p5SeparatedFromMonsterExponent : Bool
  p7SeparatedFromMonsterExponent : Bool
  p11CountCoincidenceRecorded : Bool
  p11CountCoincidencePromotedToSameObject : Bool
  exponentResidualNeedsDistinctSourceGroupoid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  normalizedSupersingularPi0Defined := true
  p3SupersingularPi0IsOne := true
  p3ExponentResidualIsTwo := true
  p3TwoInvariantsSeparated := true
  p5SeparatedFromMonsterExponent := true
  p7SeparatedFromMonsterExponent := true
  p11CountCoincidenceRecorded := true
  p11CountCoincidencePromotedToSameObject := false
  exponentResidualNeedsDistinctSourceGroupoid := true

end Integration.OggSSPExponentResidualVsSupersingularOrbitSeparation
