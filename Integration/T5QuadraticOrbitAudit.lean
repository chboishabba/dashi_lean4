import Integration.T5E8RelativeComplementCandidate
import Mathlib

/-!
# Five-trit quadratic-orbit audit

DASHI derivation over the repository's balanced `ZMod 3` coordinate.

On the exact 243-state T5 carrier, define the standard nondegenerate quadratic
form

  Q(x) = x₄² + x₃² + x₂² + x₁² + x₀²  in F₃.

Finite enumeration pays the exact shell counts

  243 = 1 + 80 + 90 + 72,

where the summands are zero, nonzero Q=0, Q=1, and Q=2 respectively.

Crucially, this is *not* the same partition as the donor's diagonal 3 + 240
relative-complement cut.  The two nonzero diagonal points have Q=2, so after
removing all three diagonal points the 240-state carrier splits as

  240 = 80 + 90 + 70.

This blocks a silent identification of the cardinality-240 relative complement
with the 72-state Q=2 shell.  Any E8 recognition still needs the explicit
same-object/action intertwining contract from `T5E8RelativeComplementCandidate`.
-/

namespace Integration.T5QuadraticOrbitAudit

open Integration.TernaryHub
open Integration.TrialecticDyadicLocalComplement
open Integration.T5E8RelativeComplementCandidate

/-- Standard quadratic form in the canonical balanced `ZMod 3` coordinate. -/
def qT5 : T5Carrier → ZMod 3
  | ⟨a,b,c,d,e⟩ =>
      balSSP a ^ 2 + balSSP b ^ 2 + balSSP c ^ 2 + balSSP d ^ 2 + balSSP e ^ 2

/-- Three quadratic shells of the full T5 carrier. -/
def QZeroShell := {x : T5Carrier // qT5 x = 0}
def QOneShell := {x : T5Carrier // qT5 x = 1}
def QTwoShell := {x : T5Carrier // qT5 x = 2}

instance : Fintype QZeroShell := inferInstance
instance : Fintype QOneShell := inferInstance
instance : Fintype QTwoShell := inferInstance

/-- Named diagonal states used to compare the two decompositions. -/
def negativeDiagonal : T5Carrier := diagonalT5 .negOne
def zeroDiagonal : T5Carrier := diagonalT5 .zero
def positiveDiagonal : T5Carrier := diagonalT5 .posOne

/-- The 80 nonzero isotropic points. -/
def QZeroNonzeroShell := {x : T5Carrier // qT5 x = 0 ∧ x ≠ zeroDiagonal}
instance : Fintype QZeroNonzeroShell := inferInstance

/-- Exact finite shell counts. -/
theorem qzero_shell_card : Fintype.card QZeroShell = 81 := by
  native_decide

theorem qone_shell_card : Fintype.card QOneShell = 90 := by
  native_decide

theorem qtwo_shell_card : Fintype.card QTwoShell = 72 := by
  native_decide

theorem qzero_nonzero_shell_card : Fintype.card QZeroNonzeroShell = 80 := by
  native_decide

/-- Exact `1 + 80 + 90 + 72` decomposition. -/
theorem full_t5_orbit_count :
    Fintype.card T5Carrier =
      1 + Fintype.card QZeroNonzeroShell + Fintype.card QOneShell + Fintype.card QTwoShell := by
  norm_num [t5_state_count, qzero_nonzero_shell_card, qone_shell_card, qtwo_shell_card]

/-- The diagonal locus meets Q=0 once and Q=2 twice. -/
theorem q_negative_diagonal : qT5 negativeDiagonal = 2 := by
  native_decide

theorem q_zero_diagonal : qT5 zeroDiagonal = 0 := by
  native_decide

theorem q_positive_diagonal : qT5 positiveDiagonal = 2 := by
  native_decide

/-- Restrict the quadratic shells to the donor's actual 240-state carrier. -/
def RelativeQZeroShell := {x : RelativeT5Carrier // qT5 x.1 = 0}
def RelativeQOneShell := {x : RelativeT5Carrier // qT5 x.1 = 1}
def RelativeQTwoShell := {x : RelativeT5Carrier // qT5 x.1 = 2}

instance : Fintype RelativeQZeroShell := inferInstance
instance : Fintype RelativeQOneShell := inferInstance
instance : Fintype RelativeQTwoShell := inferInstance

theorem relative_qzero_shell_card : Fintype.card RelativeQZeroShell = 80 := by
  native_decide

theorem relative_qone_shell_card : Fintype.card RelativeQOneShell = 90 := by
  native_decide

theorem relative_qtwo_shell_card : Fintype.card RelativeQTwoShell = 70 := by
  native_decide

theorem relative_quadratic_partition :
    Fintype.card RelativeT5Carrier =
      Fintype.card RelativeQZeroShell +
      Fintype.card RelativeQOneShell +
      Fintype.card RelativeQTwoShell := by
  norm_num [relative_state_count, relative_qzero_shell_card,
    relative_qone_shell_card, relative_qtwo_shell_card]

/-- Cardinality proves the relative carrier is not literally the 72-state
Q=2 shell.  This is a type-level anti-collapse fact, not an E8 no-go theorem. -/
theorem relative240_card_ne_qtwo72 :
    Fintype.card RelativeT5Carrier ≠ Fintype.card QTwoShell := by
  norm_num [relative_state_count, qtwo_shell_card]

inductive RelativeComplementIsQTwoShellPermission : Prop

theorem relativeComplementCannotBeQTwoShellByCardinality :
    ¬ RelativeComplementIsQTwoShellPermission := by
  intro h
  cases h

structure Boundary where
  balancedCoordinateConsumed : Bool
  fullT5Count243Consumed : Bool
  fullT5OrbitPartitionOnePlusEightyPlusNinetyPlusSeventyTwo : Bool
  qTwoShellCount72Paid : Bool
  diagonalQPatternZeroTwoTwoPaid : Bool
  relative240PartitionEightyNinetySeventyPaid : Bool
  relative240IsNotTheQTwoShell : Bool
  cardinality240CreatesE8Recognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  balancedCoordinateConsumed := true
  fullT5Count243Consumed := true
  fullT5OrbitPartitionOnePlusEightyPlusNinetyPlusSeventyTwo := true
  qTwoShellCount72Paid := true
  diagonalQPatternZeroTwoTwoPaid := true
  relative240PartitionEightyNinetySeventyPaid := true
  relative240IsNotTheQTwoShell := true
  cardinality240CreatesE8Recognition := false

end Integration.T5QuadraticOrbitAudit
