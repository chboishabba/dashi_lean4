import Integration.E8E6A2TernaryBranchingCandidate
import Integration.E8LiteralE6A2Branching
import Integration.E6LiteralE8Action
import Integration.E6PGSp4ExteriorSquare
import Mathlib

/-!
# Action obstruction for the count-matched 72+81+81+6 ternary branching

The existing ternary and literal-E8 owners deliberately stopped at matching
sector cardinalities.  The now-formalized E6 action lets us test the stronger
same-action recognition criterion.

The test fails for the proposed 81+81+6 ternary extension:

* ternary `MixedSectorA = Q=0` contains the zero vector, fixed by every E6
  reflection;
* neither literal E8 mixed 81-sector has any root fixed by all six E6 simple
  reflections (each is instead three 27-point E6 weight fibres);
* ternary `MixedSectorB` is not invariant under the E6 reflections at all;
* the selected six-point ternary A2 candidate is likewise not E6-invariant.

Therefore the exact count identity remains valid, but it cannot be promoted to
the literal E8 -> E6 x A2 branching under this E6 action.
-/

namespace Integration.E8TernaryBranchingActionObstruction

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.E6PGSp4ExteriorSquare
open Integration.E6LiteralE8Action
open Integration.E8E6A2TernaryBranchingCandidate
open Integration.E8LiteralE6A2Branching
open Integration.E8RelativeT5IntrinsicGraphObstruction

/-- The Q=0 ternary 81-sector is invariant under the existing E6 action. -/
def actMixedA (s : E6SimpleReflection) (z : MixedSectorA) : MixedSectorA :=
  ⟨reflectStandard s z.1, by
    rw [simple_reflections_preserve_quadratic s z.1, z.2]⟩

/-- Its zero state is globally fixed. -/
def mixedAZero : MixedSectorA :=
  ⟨⟨0,0,0,0,0⟩, by native_decide⟩

theorem mixed_a_zero_fixed : ∀ s, actMixedA s mixedAZero = mixedAZero := by
  native_decide

/-- Literal coordinate reflection by one of the six embedded E6 simple roots.
The scaled E8 roots have norm squared 8, so the reflection coefficient is
`dot/4`; on the literal mixed sectors these dots are in {-4,0,4}. -/
def literalReflectCoord
    (s : E6SimpleReflection) (r : E8ScaledRoot) (k : Fin 8) : Int :=
  let pairing := vectorDot (e8Coord r) (simpleVector s) / 4
  e8Coord r k - pairing * simpleVector s k

def LiteralFixedByAllE6 (r : E8ScaledRoot) : Prop :=
  ∀ s k, literalReflectCoord s r k = e8Coord r k

/-- There is no E6-global fixed root in the first 81-point literal mixed
sector. -/
theorem no_literal_mixed_plus_global_fixed_point :
    ∀ r : LiteralMixedPlus, ¬ LiteralFixedByAllE6 r.1 := by
  native_decide

/-- Nor in the opposite 81-point literal mixed sector. -/
theorem no_literal_mixed_minus_global_fixed_point :
    ∀ r : LiteralMixedMinus, ¬ LiteralFixedByAllE6 r.1 := by
  native_decide

/-- Same-action recognition contract from the ternary Q=0 sector to the first
literal mixed E8 sector.  The right-hand action is fixed independently by the
literal E8 reflection formula, not transported through the equivalence. -/
structure MixedAPlusSameActionRecognition : Prop where
  equiv : MixedSectorA ≃ LiteralMixedPlus
  intertwines :
    ∀ s x k,
      e8Coord (equiv (actMixedA s x)).1 k =
        literalReflectCoord s (equiv x).1 k

structure MixedAMinusSameActionRecognition : Prop where
  equiv : MixedSectorA ≃ LiteralMixedMinus
  intertwines :
    ∀ s x k,
      e8Coord (equiv (actMixedA s x)).1 k =
        literalReflectCoord s (equiv x).1 k

/-- The global fixed point on ternary Q=0 has nowhere to go in the literal
mixed sector, so an action-equivariant bijection is impossible. -/
theorem mixed_a_plus_same_action_impossible : ¬ MixedAPlusSameActionRecognition := by
  intro rec
  let r : LiteralMixedPlus := rec.equiv mixedAZero
  apply no_literal_mixed_plus_global_fixed_point r
  intro s k
  have h := rec.intertwines s mixedAZero k
  rw [mixed_a_zero_fixed] at h
  exact h.symm

theorem mixed_a_minus_same_action_impossible : ¬ MixedAMinusSameActionRecognition := by
  intro rec
  let r : LiteralMixedMinus := rec.equiv mixedAZero
  apply no_literal_mixed_minus_global_fixed_point r
  intro s k
  have h := rec.intertwines s mixedAZero k
  rw [mixed_a_zero_fixed] at h
  exact h.symm

/-- Invariance predicate for the second ternary 81-sector. -/
def MixedBInvariantUnderE6 : Prop :=
  ∀ s (z : MixedSectorB),
    standardQuadratic (reflectStandard s z.1) = 1 ∧
      inSelectedAffinePlane (reflectStandard s z.1) = false

/-- Explicit finite counterexample: one E6 reflection sends a MixedB point into
the selected affine line/plane. -/
theorem mixed_b_not_e6_invariant : ¬ MixedBInvariantUnderE6 := by
  native_decide

/-- The selected six-point ternary sector also fails to be E6-invariant. -/
def A2SectorInvariantUnderE6 : Prop :=
  ∀ s (z : A2Sector),
    inSelectedAffinePlane (reflectStandard s z.1) = true ∧
      inSelectedAffineLine (reflectStandard s z.1) = false

theorem a2_sector_not_e6_invariant : ¬ A2SectorInvariantUnderE6 := by
  native_decide

/-- The selected three-point line is likewise not an E6-stable subobject. -/
def SelectedLineInvariantUnderE6 : Prop :=
  ∀ s (z : SelectedLineSector),
    inSelectedAffineLine (reflectStandard s z.1) = true

theorem selected_line_not_e6_invariant : ¬ SelectedLineInvariantUnderE6 := by
  native_decide

inductive CountMatchedBranchingCreatesSameActionRecognition : Prop

theorem count_match_cannot_override_action_obstruction :
    ¬ CountMatchedBranchingCreatesSameActionRecognition := by
  intro h
  cases h

structure Boundary where
  literalMixedPlusNoGlobalFixedPointPaid : Bool
  literalMixedMinusNoGlobalFixedPointPaid : Bool
  ternaryMixedAHasGlobalFixedZeroPaid : Bool
  mixedAPlusSameActionBlocked : Bool
  mixedAMinusSameActionBlocked : Bool
  mixedBNonInvariantPaid : Bool
  a2CandidateNonInvariantPaid : Bool
  selectedLineNonInvariantPaid : Bool
  countMatchedBranchingSameActionBlocked : Bool
  cardinalityBranchingStillValid : Bool
  allPossibleE8TernaryRecognitionsBlocked : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalMixedPlusNoGlobalFixedPointPaid := true
  literalMixedMinusNoGlobalFixedPointPaid := true
  ternaryMixedAHasGlobalFixedZeroPaid := true
  mixedAPlusSameActionBlocked := true
  mixedAMinusSameActionBlocked := true
  mixedBNonInvariantPaid := true
  a2CandidateNonInvariantPaid := true
  selectedLineNonInvariantPaid := true
  countMatchedBranchingSameActionBlocked := true
  cardinalityBranchingStillValid := true
  allPossibleE8TernaryRecognitionsBlocked := false

end Integration.E8TernaryBranchingActionObstruction
