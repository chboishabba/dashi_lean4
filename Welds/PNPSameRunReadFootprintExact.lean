import Mathlib

namespace PNPSameRunReadFootprint

-- All between-query computation, sharing, cache and internal workspace
-- can be included in S. The only fresh access to x is through the
-- explicitly requested coordinate. No hidden input-dependent initial state.
def run {S : Type*} {n : Nat} (ask : S → Option (Fin n × (Bool → S)))
    (x : Fin n → Bool) : Nat → S → S × List (Fin n)
  | 0, s => (s, [])
  | k+1, s =>
    match ask s with
    | none => (s, [])
    | some (i, step) =>
      let p := run ask x k (step (x i))
      (p.1, i :: p.2)

-- Adaptive reads, actual path, arbitrary state sharing. Agreement
-- on the coordinates read by ONE run suffices for the whole run.
theorem agreement {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x y : Fin n → Bool)
    (k : Nat) (s : S)
    (h : ∀ i ∈ (run ask x k s).2, x i = y i) :
    run ask x k s = run ask y k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases ha : ask s with
    | none => simp [run,ha]
    | some p =>
      rcases p with ⟨i,step⟩
      have hi : x i = y i := h i (by simp [run,ha])
      have ht : ∀ j ∈ (run ask x k (step (x i))).2, x j = y j := by
        intro j hj
        apply h j
        simp [run,ha,hj]
      have rec := ih (step (x i)) ht
      simp only [run,ha]
      rw [← hi,rec]

def flip {n : Nat} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j=i then !x j else x j

-- Sensitivity at a particular actual input forces a read on THAT
-- run, not merely on one of exponentially many hypothetical inputs.
theorem sensitive_read {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (x : Fin n → Bool) (k : Nat) (s : S) (i : Fin n)
    (h : accept (run ask x k s).1 ≠ accept (run ask (flip x i) k s).1) :
    i ∈ (run ask x k s).2 := by
  by_contra hn
  have he : ∀ j ∈ (run ask x k s).2, x j = flip x i j := by
    intro j hj
    have hji : j≠i := fun e => hn (e ▸ hj)
    simp [flip,hji]
  exact h (congrArg (fun p : S × List (Fin n) => accept p.1)
    (agreement ask x (flip x i) k s he))

theorem reads_le_fuel {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (x : Fin n → Bool)
    (k : Nat) (s : S) : (run ask x k s).2.length ≤ k := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
    cases ha : ask s with
    | none => simp [run,ha]
    | some p =>
      rcases p with ⟨i,step⟩
      simpa [run,ha] using Nat.succ_le_succ (ih (step (x i)))

theorem sensitive_set_lower {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (x : Fin n → Bool) (k : Nat) (s : S) (D : Finset (Fin n))
    (h : ∀ i ∈ D, accept (run ask x k s).1 ≠
      accept (run ask (flip x i) k s).1) :
    D.card ≤ (run ask x k s).2.length := by
  have hs : D ⊆ (run ask x k s).2.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (sensitive_read ask accept x k s i (h i hi))
  exact (Finset.card_le_card hs).trans (List.toFinset_card_le _)

theorem all_sensitive_lower {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (x : Fin n → Bool) (k : Nat) (s : S)
    (h : ∀ i, accept (run ask x k s).1 ≠
      accept (run ask (flip x i) k s).1) : n ≤ k := by
  have hp := sensitive_set_lower ask accept x k s Finset.univ (fun i _ => h i)
  have hq := reads_le_fuel ask x k s
  simpa using hp.trans hq

-- Reservation telescope for the capped-producer family. Declared caps,
-- not physical bit time. No successful-attempt-only accounting.
namespace Allowance

def consume : Nat → List Nat → Option Nat
  | left, [] => some left
  | left, a::as => if a≤left then consume (left-a) as else none

theorem total_exact (left : Nat) (charges : List Nat) (remain : Nat)
    (h : consume left charges = some remain) :
    charges.sum + remain = left := by
  induction charges generalizing left with
  | nil => simpa [consume] using h.symm
  | cons a as ih =>
    by_cases ha : a≤left
    · simp only [consume,if_pos ha] at h
      have hp := ih (left-a) h
      simp only [List.sum_cons]
      omega
    · simp [consume,ha] at h

end Allowance
end PNPSameRunReadFootprint
