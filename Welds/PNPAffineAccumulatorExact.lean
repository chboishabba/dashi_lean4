import Welds.PNPSeparatorMarginalsExact
import Welds.PNPClauseSyndromeRowOperationsExact

namespace PNPAffineAccumulator
open scoped BigOperators
open PNPOriginalModularIncidence

-- A prefix retains the rational partial value, rather than each bit.
-- Only already-consumed coordinates contribute to the prefix.
def partial {d : Nat} (a : ℚ) (row : Fin d → ℚ)
    (S : Finset (Fin d)) (u : Fin d → Bool) : ℚ :=
  a+∑ k∈S,row k*emb ℚ (u k)

theorem append_value {d : Nat} (a : ℚ) (row : Fin d → ℚ)
    (S T : Finset (Fin d)) (disjoint : Disjoint S T) (u : Fin d → Bool) :
    partial a row (S∪T) u=partial a row S u+
      ∑ k∈T,row k*emb ℚ (u k) := by
  classical
  unfold partial
  rw [Finset.sum_union disjoint]
  ring

theorem same_partial_all_tails {d : Nat} (a : ℚ) (row : Fin d → ℚ)
    (S T : Finset (Fin d)) (disjoint : Disjoint S T)
    (u v : Fin d → Bool)
    (same : partial a row S u=partial a row S v)
    (tail : ∀ k∈T,u k=v k) :
    partial a row (S∪T) u=partial a row (S∪T) v := by
  rw [append_value a row S T disjoint u,append_value a row S T disjoint v,same]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [tail k hk]

-- A complete rational affine value is tested against the two actual
-- Boolean values, not a rounded approximation or integer relaxation.
def legal (v : ℚ) : Prop := v=0 ∨ v=1

theorem same_partial_same_terminal_bit {d : Nat} (a : ℚ) (row : Fin d → ℚ)
    (S T : Finset (Fin d)) (disjoint : Disjoint S T)
    (u v : Fin d → Bool)
    (same : partial a row S u=partial a row S v)
    (tail : ∀ k∈T,u k=v k) :
    (legal (partial a row (S∪T) u) ↔ legal (partial a row (S∪T) v)) ∧
    decide (partial a row (S∪T) u=1)=decide (partial a row (S∪T) v=1) := by
  rw [same_partial_all_tails a row S T disjoint u v same tail]
  exact ⟨Iff.rfl,rfl⟩

-- Original factor states use the existing OR/ternary syndrome/one-hot
-- accumulators. An already-overfull exact-one row cannot be repaired.
theorem one_hot_retire (past future : Nat) (h : future=0) :
    past+future=1 ↔ past=1 :=
  PNPEndpointClippedOccupancy.exactOne_retire past future h

theorem one_hot_overfull (past future : Nat) (h : 1<past) :
    past+future≠1 :=
  PNPEndpointClippedOccupancy.exactOne_overfull past future h

-- Equal future-visible partial values and equal original factor
-- states imply identical continuations. This is the algebraic key
-- used by the live mass partition; concrete schedule/ownership
-- extraction is an independent native receipt obligation.
theorem key_sufficient {X K Y : Type*} (key : X → K)
    (read : K → Y) (x y : X) (same : key x=key y) :
    read (key x)=read (key y) := congrArg read same

-- Exact signed interval bound: each future Boolean summand lies
-- between min(0,c) and max(0,c). This is a safe pruning receiver,
-- not a sufficiency test for an arbitrary subset-sum.
theorem bit_term_bounds (c : ℚ) (b : Bool) :
    min 0 c ≤ c*emb ℚ b ∧ c*emb ℚ b ≤ max 0 c := by
  cases b
  · simp [emb,min_le_left,le_max_left]
  · simp [emb,min_le_right,le_max_right]

theorem future_bounds {d : Nat} (row : Fin d → ℚ)
    (T : Finset (Fin d)) (u : Fin d → Bool) :
    (∑ k∈T,min 0 (row k)) ≤ ∑ k∈T,row k*emb ℚ (u k) ∧
    (∑ k∈T,row k*emb ℚ (u k)) ≤ ∑ k∈T,max 0 (row k) := by
  constructor <;> apply Finset.sum_le_sum
  · intro k _
    exact (bit_term_bounds (row k) (u k)).1
  · intro k _
    exact (bit_term_bounds (row k) (u k)).2

theorem interval_excludes {d : Nat} (p : ℚ) (row : Fin d → ℚ)
    (T : Finset (Fin d)) (u : Fin d → Bool)
    (outside : p+(∑ k∈T,max 0 (row k))<0 ∨
      1<p+(∑ k∈T,min 0 (row k))) :
    ¬ legal (p+∑ k∈T,row k*emb ℚ (u k)) := by
  have h := future_bounds row T u
  intro hv
  rcases outside with h0|h1 <;> rcases hv with e|e <;> linarith [h.1,h.2]

-- The actual pruning test permits an interval lying strictly
-- between 0 and 1: neither original bit is attainable there.
theorem interval_excludes_bits {d : Nat} (p : ℚ) (row : Fin d → ℚ)
    (T : Finset (Fin d)) (u : Fin d → Bool)
    (outside : ∀ b : ℚ, legal b → ¬ (p+(∑ k∈T,min 0 (row k))≤b ∧
      b≤p+(∑ k∈T,max 0 (row k)))) :
    ¬ legal (p+∑ k∈T,row k*emb ℚ (u k)) := by
  intro h
  have bounds := future_bounds row T u
  exact outside _ h ⟨add_le_add_left bounds.1 p,add_le_add_left bounds.2 p⟩

end PNPAffineAccumulator
