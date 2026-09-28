import Mathlib
import Integration.OggSSPP2BalancedTernaryPuncturedPlane

/-!
# p=2 balanced-ternary neutral-completion bridge

Lean mirror of the finite Agda bridge.

The duplicated-centre ternary completion has ten states.  We rechart it as

  ComplementMode5 × BinaryPhase

and define the nine-state quotient obtained by collapsing only the duplicated
mode09 centre.  The resulting quotient is exactly one ternary nine-sheet.

This is a finite presentation theorem only.
-/

namespace Integration.OggSSPP2BalancedTernaryNeutralCompletionBridge

open Integration.OggSSPP2BalancedTernaryPuncturedPlane
open Integration.BalancedTernaryAntipodal369OrbitHierarchy

inductive ComplementMode5
  | mode09 | mode18 | mode27 | mode36 | mode45
  deriving DecidableEq, Repr, Fintype

inductive BinaryPhase
  | direct | counter
  deriving DecidableEq, Repr, Fintype

abbrev Oriented10 := ComplementMode5 × BinaryPhase

inductive Quotient9
  | identity
  | mode18counter | mode18direct
  | mode27counter | mode27direct
  | mode36counter | mode36direct
  | mode45counter | mode45direct
  deriving DecidableEq, Repr, Fintype

def duplicatedCentreToOriented10 :
    DuplicatedCentreNineSheet → Oriented10
  | .lowerCentre => (.mode09, .counter)
  | .upperCentre => (.mode09, .direct)
  | .puncturedPoint .negativeFirstAxis => (.mode18, .counter)
  | .puncturedPoint .positiveFirstAxis => (.mode18, .direct)
  | .puncturedPoint .negativeSecondAxis => (.mode27, .counter)
  | .puncturedPoint .positiveSecondAxis => (.mode27, .direct)
  | .puncturedPoint .negativeEqualDiagonal => (.mode36, .counter)
  | .puncturedPoint .positiveEqualDiagonal => (.mode36, .direct)
  | .puncturedPoint .negativeOppositeDiagonal => (.mode45, .counter)
  | .puncturedPoint .positiveOppositeDiagonal => (.mode45, .direct)

def oriented10ToDuplicatedCentre :
    Oriented10 → DuplicatedCentreNineSheet
  | (.mode09, .counter) => .lowerCentre
  | (.mode09, .direct) => .upperCentre
  | (.mode18, .counter) => .puncturedPoint .negativeFirstAxis
  | (.mode18, .direct) => .puncturedPoint .positiveFirstAxis
  | (.mode27, .counter) => .puncturedPoint .negativeSecondAxis
  | (.mode27, .direct) => .puncturedPoint .positiveSecondAxis
  | (.mode36, .counter) => .puncturedPoint .negativeEqualDiagonal
  | (.mode36, .direct) => .puncturedPoint .positiveEqualDiagonal
  | (.mode45, .counter) => .puncturedPoint .negativeOppositeDiagonal
  | (.mode45, .direct) => .puncturedPoint .positiveOppositeDiagonal

theorem duplicated_oriented_roundtrip (s : DuplicatedCentreNineSheet) :
    oriented10ToDuplicatedCentre (duplicatedCentreToOriented10 s) = s := by
  cases s with
  | lowerCentre => rfl
  | upperCentre => rfl
  | puncturedPoint p => cases p <;> rfl

theorem oriented_duplicated_roundtrip (s : Oriented10) :
    duplicatedCentreToOriented10 (oriented10ToDuplicatedCentre s) = s := by
  rcases s with ⟨m,p⟩
  cases m <;> cases p <;> rfl

def quotientOriented10 : Oriented10 → Quotient9
  | (.mode09, _) => .identity
  | (.mode18, .counter) => .mode18counter
  | (.mode18, .direct) => .mode18direct
  | (.mode27, .counter) => .mode27counter
  | (.mode27, .direct) => .mode27direct
  | (.mode36, .counter) => .mode36counter
  | (.mode36, .direct) => .mode36direct
  | (.mode45, .counter) => .mode45counter
  | (.mode45, .direct) => .mode45direct

def nineSheetToQuotient9 : NineSheet → Quotient9
  | (.zero,.zero) => .identity
  | (.neg,.zero) => .mode18counter
  | (.pos,.zero) => .mode18direct
  | (.zero,.neg) => .mode27counter
  | (.zero,.pos) => .mode27direct
  | (.neg,.neg) => .mode36counter
  | (.pos,.pos) => .mode36direct
  | (.neg,.pos) => .mode45counter
  | (.pos,.neg) => .mode45direct

def quotient9ToNineSheet : Quotient9 → NineSheet
  | .identity => (.zero,.zero)
  | .mode18counter => (.neg,.zero)
  | .mode18direct => (.pos,.zero)
  | .mode27counter => (.zero,.neg)
  | .mode27direct => (.zero,.pos)
  | .mode36counter => (.neg,.neg)
  | .mode36direct => (.pos,.pos)
  | .mode45counter => (.neg,.pos)
  | .mode45direct => (.pos,.neg)

theorem nine_quotient_roundtrip (s : NineSheet) :
    quotient9ToNineSheet (nineSheetToQuotient9 s) = s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem quotient_nine_roundtrip (q : Quotient9) :
    nineSheetToQuotient9 (quotient9ToNineSheet q) = q := by
  cases q <;> rfl

theorem neutral_collapse_commutes (s : DuplicatedCentreNineSheet) :
    nineSheetToQuotient9 (collapseDuplicatedCentre s) =
      quotientOriented10 (duplicatedCentreToOriented10 s) := by
  cases s with
  | lowerCentre => rfl
  | upperCentre => rfl
  | puncturedPoint p => cases p <;> rfl

theorem oriented10_cardinality :
    Fintype.card Oriented10 = 10 := by decide

theorem quotient9_cardinality :
    Fintype.card Quotient9 = 9 := by decide

structure Boundary where
  duplicatedCentreRechartsToOriented10 : Bool
  nineSheetRechartsToQuotient9 : Bool
  collapseDiagramsCommute : Bool
  semanticIdentityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  duplicatedCentreRechartsToOriented10 := true
  nineSheetRechartsToQuotient9 := true
  collapseDiagramsCommute := true
  semanticIdentityClaimed := false

end Integration.OggSSPP2BalancedTernaryNeutralCompletionBridge
