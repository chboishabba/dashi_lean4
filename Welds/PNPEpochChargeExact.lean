import Mathlib
import Welds.PNPFutureResidualChargeExact

namespace PNPEpochCharge
open PNPSameRunReadFootprint
open PNPFutureResidualCharge
open scoped BigOperators

-- The epoch observer is the actual final STATE, not the eventual
-- decision after other epochs. A collision that persists is not charged.
theorem separated_epoch {S : Type*} [DecidableEq S] {n : Nat}
    (ask : S → Option (Fin n × (Bool → S)))
    (prefix : (Fin n → Bool) → S) (x y : Fin n → Bool) (k : Nat)
    (h : prefix x=prefix y)
    (sep : (run ask x k (prefix x)).1 ≠ (run ask y k (prefix y)).1) :
    ∃ i ∈ (run ask x k (prefix x)).2, x i≠y i := by
  let z := (run ask x k (prefix x)).1
  apply collision_requires_read ask (fun s => decide (s=z)) prefix x y k h
  have hne : (run ask y k (prefix y)).1 ≠ z := Ne.symm sep
  simp [z,hne]

theorem survives_epoch {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S)))
    (prefix : (Fin n → Bool) → S) (x y : Fin n → Bool) (k : Nat)
    (h : prefix x=prefix y)
    (agree : ∀ i ∈ (run ask x k (prefix x)).2, x i=y i) :
    run ask x k (prefix x)=run ask y k (prefix y) := by
  rw [← h]
  exact agreement ask x y k (prefix x) agree

-- Each successive epoch uses its actual start, with no reinitialization
-- or independent counterfactual run charged to the retained input.
def epochRun {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x : Fin n → Bool) :
    List Nat → S → S × List (Fin n)
  | [], s => (s,[])
  | k::ks, s =>
    let a := run ask x k s
    let b := epochRun ask x ks a.1
    (b.1,a.2++b.2)

theorem epochRun_budget {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x : Fin n → Bool)
    (ks : List Nat) (s : S) :
    (epochRun ask x ks s).2.length ≤ ks.sum := by
  induction ks generalizing s with
  | nil => simp [epochRun]
  | cons k ks ih =>
    simp only [epochRun,List.length_append,List.sum_cons]
    exact Nat.add_le_add (reads_le_fuel ask x k s) (ih _)

-- Demand is supplied per actual epoch from separated_epoch and the
-- weighted packing. Summing charges is valid only on these disjoint
-- pieces of the SAME run.
def charges {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x : Fin n → Bool)
    (demand : Nat → S → Nat) : List Nat → S → Nat
  | [], _ => 0
  | k::ks, s => demand k s + charges ask x demand ks (run ask x k s).1

theorem sum_actual_epochs {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x : Fin n → Bool)
    (demand : Nat → S → Nat) (C : Nat)
    (bound : ∀ k s, demand k s ≤ C*(run ask x k s).2.length)
    (ks : List Nat) (s : S) :
    charges ask x demand ks s ≤ C*(epochRun ask x ks s).2.length := by
  induction ks generalizing s with
  | nil => simp [charges,epochRun]
  | cons k ks ih =>
    simp only [charges,epochRun,List.length_append,Nat.mul_add]
    exact Nat.add_le_add (bound k s) (ih _)

-- Erasure of input distinctions alone does not create different
-- residual DECISIONS. The prefix may have computed the full answer.
theorem answer_state_no_demand {A : Type*} (f : A → Bool)
    (x y : A) (h : f x=f y) : ¬ f x≠f y := fun hn => hn h

-- Stronger countercontrol: many states of the same output can collide,
-- but the terminal read footprint is exactly empty.
theorem terminal_no_reads {n : Nat} (x : Fin n → Bool) (k : Nat) (s : Bool) :
    (run (fun _ : Bool => (none : Option (Fin n × (Bool → Bool)))) x k s).2=[] := by
  cases k <;> rfl

-- Pigeonhole can force some state fibre to be large, not a large fibre
-- for every actual input, nor mixed output within it. In particular a
-- one-bit answer state has no different-output collisions at all.
end PNPEpochCharge
