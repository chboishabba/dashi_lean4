import Welds.PNPAffinePinReopeningExact
import Welds.PNPResidualGeometryBridgeExact

namespace PNPClauseSyndromeFold
open PNPF3SyndromeBoundary

-- The actual prefix state stores clauses already made true and the
-- accumulated affine contribution. Neither multiplicity nor a witness
-- is part of the consumer key.
structure Key (m r : Nat) where
  mask : Finset (Fin m)
  syndrome : Syndrome r

def join {m r : Nat} (a b : Key m r) : Key m r :=
  ⟨a.mask ∪ b.mask,a.syndrome+b.syndrome⟩

def empty {m r : Nat} : Key m r := ⟨∅,0⟩

theorem join_assoc {m r : Nat} (a b c : Key m r) :
    join (join a b) c=join a (join b c) := by
  cases a; cases b; cases c
  simp [join,Finset.union_assoc,add_assoc]

theorem join_empty {m r : Nat} (a : Key m r) : join a empty=a := by
  cases a
  simp [join,empty]

def accepts {m r : Nat} (t : Syndrome r) (a : Key m r) : Prop :=
  a.mask=Finset.univ ∧ a.syndrome=t

def fold {m r : Nat} (xs : List (Key m r)) : Key m r :=
  xs.foldl join empty

theorem foldl_join {m r : Nat} (a : Key m r) (xs : List (Key m r)) :
    xs.foldl join a=join a (fold xs) := by
  induction xs generalizing a with
  | nil => simp [fold,join_empty]
  | cons b bs ih =>
    simp only [List.foldl_cons,fold]
    rw [ih (join a b),ih (join empty b),join_assoc]
    have h : join empty b=b := by cases b; simp [join,empty]
    rw [h]

theorem fold_append {m r : Nat} (xs ys : List (Key m r)) :
    fold (xs++ys)=join (fold xs) (fold ys) := by
  simp only [fold,List.foldl_append]
  exact foldl_join (xs.foldl join empty) ys

theorem same_key_all_continuations {m r : Nat}
    (xs ys tail : List (Key m r)) (t : Syndrome r)
    (same : fold xs=fold ys) :
    accepts t (fold (xs++tail)) ↔ accepts t (fold (ys++tail)) := by
  rw [fold_append,fold_append,same]

-- A dropped prefix can be excluded precisely when a clause has no
-- remaining occurrences and is not already satisfied.
theorem expired_clause {m r : Nat} (a b : Key m r) (j : Fin m)
    (missing : j∉a.mask) (noFuture : j∉b.mask) (t : Syndrome r) :
    ¬ accepts t (join a b) := by
  intro h
  have hj : j∈(join a b).mask := by rw [h.1]; simp
  exact (Finset.mem_union.mp hj).elim missing noFuture

-- Equal keys allow mass merging because the continuation family is
-- identical, not because all full source assignments are identified.
-- The next native attachment is the concrete Boolean prefix producer
-- and disjoint mass partition for the actual Python table.
end PNPClauseSyndromeFold

namespace PNPAffineRowOperations
open PNPAffinePinReopening

abbrev Row (n : Nat) := (Fin n → ZMod 3) × ZMod 3

def value {n : Nat} (x : Fin n → Bool) (a : Row n) : ZMod 3 :=
  (∑ i,a.1 i*embed (x i))-a.2

def addScaled {n : Nat} (a b : Row n) (k : ZMod 3) : Row n :=
  (fun i => a.1 i+k*b.1 i,a.2+k*b.2)

theorem addScaled_value {n : Nat} (x : Fin n → Bool) (a b : Row n) (k : ZMod 3) :
    value x (addScaled a b k)=value x a+k*value x b := by
  classical
  simp only [value,addScaled,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  ring

theorem addScaled_inverse {n : Nat} (a b : Row n) (k : ZMod 3) :
    addScaled (addScaled a b k) b (-k)=a := by
  rcases a with ⟨a,t⟩
  apply Prod.ext
  · funext i
    simp [addScaled]
  · simp [addScaled]

theorem addScaled_sound {n : Nat} (x : Fin n → Bool) (a b : Row n)
    (k : ZMod 3) (hb : value x b=0) :
    value x (addScaled a b k)=0 ↔ value x a=0 := by
  rw [addScaled_value,hb,mul_zero,add_zero]

def scale {n : Nat} (a : Row n) (k : ZMod 3) : Row n :=
  (fun i => k*a.1 i,k*a.2)

theorem scale_value {n : Nat} (x : Fin n → Bool) (a : Row n) (k : ZMod 3) :
    value x (scale a k)=k*value x a := by
  classical
  simp only [value,scale,mul_assoc,← Finset.mul_sum]
  ring

theorem scale_sound {n : Nat} (x : Fin n → Bool) (a : Row n)
    (k : ZMod 3) (hk : k≠0) :
    value x (scale a k)=0 ↔ value x a=0 := by
  rw [scale_value,mul_eq_zero]
  simp [hk]

-- Swapping equations preserves their conjunction. Row addition is
-- reversible while retaining the source row; nonzero scaling preserves
-- zeros. A concrete operation-list interpreter remains to be attached.
end PNPAffineRowOperations
