import Mathlib
import Integration.RiemannSSP15ChosenGridTransversality

/-!
# RH role-column × CM-class contingency profile

For the explicitly chosen 5×3 role grid and the mirrored Q(sqrt(-7)) CM table:

                    split  inert  ramified
  origin              2      2       1
  j                   1      4       0
  s                   2      3       0

Rows sum to 5; columns sum to the canonical 5,9,1 CM count shape.
This quantifies transversality and does not identify the two partitions.
-/

namespace Integration.RiemannSSP15RoleCMContingency

open Integration.RiemannSSP15DepthFiveRoleCodec
open Integration.RiemannSSP15ChosenGridTransversality

def rolePrimeList : RHDepthFiveRole → List Prime15
  | .origin => [.p2,.p7,.p17,.p29,.p47]
  | .j => [.p3,.p11,.p19,.p31,.p59]
  | .s => [.p5,.p13,.p23,.p41,.p71]

def countClass : RHDepthFiveRole → CMClass → Nat
  | .origin, .split => 2
  | .origin, .inert => 2
  | .origin, .ramified => 1
  | .j, .split => 1
  | .j, .inert => 4
  | .j, .ramified => 0
  | .s, .split => 2
  | .s, .inert => 3
  | .s, .ramified => 0

theorem origin_prime_classes_exact :
    (cmClass .p2, cmClass .p7, cmClass .p17, cmClass .p29, cmClass .p47)
      = (.split,.ramified,.inert,.split,.inert) := rfl

theorem j_prime_classes_exact :
    (cmClass .p3, cmClass .p11, cmClass .p19, cmClass .p31, cmClass .p59)
      = (.inert,.split,.inert,.inert,.inert) := rfl

theorem s_prime_classes_exact :
    (cmClass .p5, cmClass .p13, cmClass .p23, cmClass .p41, cmClass .p71)
      = (.inert,.inert,.split,.inert,.split) := rfl

theorem origin_contingency :
    countClass .origin .split = 2 ∧
    countClass .origin .inert = 2 ∧
    countClass .origin .ramified = 1 := by
  native_decide

theorem j_contingency :
    countClass .j .split = 1 ∧
    countClass .j .inert = 4 ∧
    countClass .j .ramified = 0 := by
  native_decide

theorem s_contingency :
    countClass .s .split = 2 ∧
    countClass .s .inert = 3 ∧
    countClass .s .ramified = 0 := by
  native_decide

theorem every_role_row_sums_to_five :
    (countClass .origin .split + countClass .origin .inert + countClass .origin .ramified = 5) ∧
    (countClass .j .split + countClass .j .inert + countClass .j .ramified = 5) ∧
    (countClass .s .split + countClass .s .inert + countClass .s .ramified = 5) := by
  native_decide

theorem cm_column_sums :
    (countClass .origin .split + countClass .j .split + countClass .s .split = 5) ∧
    (countClass .origin .inert + countClass .j .inert + countClass .s .inert = 9) ∧
    (countClass .origin .ramified + countClass .j .ramified + countClass .s .ramified = 1) := by
  native_decide

theorem complete_contingency_matrix :
    ((countClass .origin .split, countClass .origin .inert, countClass .origin .ramified),
     (countClass .j .split, countClass .j .inert, countClass .j .ramified),
     (countClass .s .split, countClass .s .inert, countClass .s .ramified))
    =
    ((2,2,1),(1,4,0),(2,3,0)) := by
  native_decide

inductive PromotionError
  | contingencyTableCreatesPartitionIdentity
  | cmCountsCreateRHRoleSemantics
  deriving DecidableEq, Repr

structure Boundary where
  completeThreeByThreeTableOwned : Bool
  rowSumsFiveOwned : Bool
  columnSumsFiveNineOneOwned : Bool
  chosenGridIdentifiedWithCMPartition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  completeThreeByThreeTableOwned := true
  rowSumsFiveOwned := true
  columnSumsFiveNineOneOwned := true
  chosenGridIdentifiedWithCMPartition := false

end Integration.RiemannSSP15RoleCMContingency
