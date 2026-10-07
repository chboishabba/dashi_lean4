import Integration.AlbertTrialityCubicCompiler
import Mathlib

/-!
# Slot-permutation compiler for the triality/Freudenthal cubic

The Albert coordinate cubic has three scalar slots paired with three
8-dimensional quadratic slots.  The S3/triality quotient of W(F4) permutes
those three slots.  This file isolates the exact algebraic conditions under
which the two adjacent transpositions preserve the cubic.

No octonion-specific formulas are assumed here.  Concrete H3(O) realization
must supply the quadratic-form identifications and the corresponding symmetry
of the triality trilinear form (possibly after conjugation in selected slots).
-/

namespace Integration.AlbertTrialitySlotPermutationCompiler

open Integration.AlbertTrialityCubicCompiler

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Compatibility data for swapping slots 0 and 1. -/
structure Swap01Compatibility (D : TrialityCubicData V) where
  q0_eq_q1 : ∀ x, D.q0 x = D.q1 x
  triality_swap01 : ∀ x y z, D.tri y x z = D.tri x y z

/-- Pure slot swap on coordinates.  A concrete octonion realization may first
conjugate/reidentify one sector so that its action has this normal form. -/
def swap01 (x : TrialityCoordinates V) : TrialityCoordinates V where
  d0 := x.d1
  d1 := x.d0
  d2 := x.d2
  x0 := x.x1
  x1 := x.x0
  x2 := x.x2

theorem swap01_cubic_preserved
    (D : TrialityCubicData V) (H : Swap01Compatibility D) :
    ∀ x, cubic D (swap01 x) = cubic D x := by
  intro x
  simp [cubic, swap01, H.q0_eq_q1, H.triality_swap01]
  ring

/-- Compatibility data for swapping slots 1 and 2. -/
structure Swap12Compatibility (D : TrialityCubicData V) where
  q1_eq_q2 : ∀ x, D.q1 x = D.q2 x
  triality_swap12 : ∀ x y z, D.tri x z y = D.tri x y z

/-- Pure slot swap 1 <-> 2. -/
def swap12 (x : TrialityCoordinates V) : TrialityCoordinates V where
  d0 := x.d0
  d1 := x.d2
  d2 := x.d1
  x0 := x.x0
  x1 := x.x2
  x2 := x.x1

theorem swap12_cubic_preserved
    (D : TrialityCubicData V) (H : Swap12Compatibility D) :
    ∀ x, cubic D (swap12 x) = cubic D x := by
  intro x
  simp [cubic, swap12, H.q1_eq_q2, H.triality_swap12]
  ring

/-- The source-level terminal for the quotient S3 action.  The finite branch has
already proved that its two folded generators induce the two transpositions on
the three 8-dimensional sectors; this record asks a concrete Albert realization
to identify those actions with cubic-preserving slot symmetries. -/
structure S3AlbertSlotRealization (D : TrialityCubicData V) : Prop where
  swap01Compatibility : Swap01Compatibility D
  swap12Compatibility : Swap12Compatibility D
  finiteG05MatchesSwap01AfterSectorIdentification : Prop
  finiteG24MatchesSwap12AfterSectorIdentification : Prop

structure Boundary where
  twoS3GeneratorsReducedToSlotSwaps : Bool
  swap01CubicCompilerPaid : Bool
  swap12CubicCompilerPaid : Bool
  actualOctonionConjugationConventionsPaidHere : Bool
  actualFiniteToAlbertSlotIdentificationPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  twoS3GeneratorsReducedToSlotSwaps := true
  swap01CubicCompilerPaid := true
  swap12CubicCompilerPaid := true
  actualOctonionConjugationConventionsPaidHere := false
  actualFiniteToAlbertSlotIdentificationPaidHere := false

end Integration.AlbertTrialitySlotPermutationCompiler
