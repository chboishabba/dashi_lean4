import Mathlib
import Welds.PNPSameRunReadFootprintExact

namespace PNPFutureResidualCharge
open PNPSameRunReadFootprint
open scoped BigOperators

-- The prefix may have performed arbitrary data-dependent reads and
-- computation. Every persistent cache/address/flag must be in S.
-- A collision in the actual state leaves only future source queries
-- with which to separate the two continuations.
theorem collision_requires_read {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (prefix : (Fin n → Bool) → S) (x y : Fin n → Bool) (k : Nat)
    (stateEq : prefix x = prefix y)
    (different : accept (run ask x k (prefix x)).1 ≠
      accept (run ask y k (prefix y)).1) :
    ∃ i ∈ (run ask x k (prefix x)).2, x i≠y i := by
  classical
  by_contra h
  push_neg at h
  have e := agreement ask x y k (prefix x) h
  rw [← stateEq] at different
  exact different (congrArg (fun p : S × List (Fin n) => accept p.1) e)

-- Many distinct counterfactuals can be separated by ONE read. Instead
-- of counting counterfactuals as distinct events, use a packing whose
-- total demand on each actual source coordinate is bounded by C.
theorem packed_future_reads {S J : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (prefix : (Fin n → Bool) → S) (x : Fin n → Bool) (k C : Nat)
    (obligations : Finset J) (alt : J → Fin n → Bool) (w : J → Nat)
    (collision : ∀ j∈obligations, prefix x=prefix (alt j))
    (different : ∀ j∈obligations,
      accept (run ask x k (prefix x)).1 ≠
      accept (run ask (alt j) k (prefix (alt j))).1)
    (capacity : ∀ i, (∑ j∈obligations, if x i≠alt j i then w j else 0)≤C) :
    (∑ j∈obligations, w j) ≤ C * (run ask x k (prefix x)).2.length := by
  classical
  let R := (run ask x k (prefix x)).2.toFinset
  have localBound (j : J) (hj : j∈obligations) :
      w j ≤ ∑ i∈R, if x i≠alt j i then w j else 0 := by
    obtain ⟨i,hi,hne⟩ :=
      collision_requires_read ask accept prefix x (alt j) k (collision j hj) (different j hj)
    have hi' : i∈R := List.mem_toFinset.mpr hi
    have hle : (if x i≠alt j i then w j else 0) ≤
        ∑ q∈R, if x q≠alt j q then w j else 0 :=
      Finset.single_le_sum (fun q _ => Nat.zero_le _) hi'
    simpa [hne] using hle
  calc
    (∑ j∈obligations,w j)
      ≤ ∑ j∈obligations, ∑ i∈R, if x i≠alt j i then w j else 0 :=
        Finset.sum_le_sum localBound
    _ = ∑ i∈R, ∑ j∈obligations, if x i≠alt j i then w j else 0 :=
        Finset.sum_comm
    _ ≤ ∑ _i∈R, C := Finset.sum_le_sum (fun i _ => capacity i)
    _ = R.card*C := by simp
    _ ≤ (run ask x k (prefix x)).2.length*C :=
        Nat.mul_le_mul_right C (List.toFinset_card_le _)
    _ = C*(run ask x k (prefix x)).2.length := Nat.mul_comm _ _

-- Unit demand / disjoint difference sets gives a same-run lower bound
-- without fixed query order. General weights allow overlap, but no
-- double charging. This theorem does not create state collisions or
-- superpolynomial packed demand, nor charge a reread across epochs
-- without a fresh proof of the collision premise.
end PNPFutureResidualCharge
