import Mathlib

namespace PNPConstructiveDescent

-- No model count is needed by the consumer: it tries every scale
-- 1 <= k <= n+1. A positive count supplies one good scale in that list.
theorem pow_scale (n : Nat) : 2*(2:Nat)^n ≤ 3^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ 2 n, show n+1+1=(n+1)+1 by omega, pow_succ 3 (n+1)]
    omega

theorem scale_exists (m K : Nat) (hm : 0<m) (hK : 2*m≤3^K) :
    ∃ k≤K, 0<k ∧ 2*m≤3^k ∧ 3^k<6*m := by
  induction K with
  | zero =>
    simp at hK
    omega
  | succ K ih =>
    by_cases h : 2*m≤3^K
    · obtain ⟨k,hk,hpos,hlo,hhi⟩ := ih h
      exact ⟨k,by omega,hpos,hlo,hhi⟩
    · refine ⟨K+1,by omega,by omega,hK,?_⟩
      rw [pow_succ]
      omega

theorem good_scale (n m : Nat) (hm : 0<m) (h : m≤2^n) :
    ∃ k≤n+1, 0<k ∧ 2*m≤3^k ∧ 3^k<6*m :=
  scale_exists m (n+1) hm ((Nat.mul_le_mul_left 2 h).trans (pow_scale n))

-- For the signed occupancy root x=m/3^k and correction=m/3^(2k).
-- Existing Toeplitz moment identity supplies this expression.
theorem root_positive (x correction : ℚ) (hx : 1/6<x)
    (hy : x≤1/2) (hc : 0≤correction) :
    1/12 < x-x*x+correction := by
  have hp := mul_nonneg (show 0≤x by linarith) (show 0≤1/2-x by linarith)
  nlinarith

theorem descent_telescope (V : Nat → ℚ) (loss : ℚ) (L : Nat)
    (h : ∀ i<L, V i-loss≤V (i+1)) :
    V 0-(L:ℚ)*loss≤V L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hs := h L (by omega)
    push_cast
    linarith

-- The signed producer certifies Delta=3*(Vchild-Vparent).
-- L steps with Delta>=-1/(8L) preserve a strictly positive terminal.
theorem positive_terminal (V : Nat → ℚ) (L : Nat) (hL : 0<L)
    (root : 1/12<V 0)
    (step : ∀ i<L, -(1/(8*(L:ℚ)))≤3*(V (i+1)-V i)) :
    1/24<V L := by
  have hn : (L:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have he : (1/(8*(L:ℚ)))/3=1/(24*(L:ℚ)) := by field_simp <;> ring
  have ht := descent_telescope V (1/(24*(L:ℚ))) L (by
    intro i hi
    have hs := step i hi
    linarith [he])
  have hp : (L:ℚ)*(1/(24*(L:ℚ)))=1/24 := by field_simp <;> ring
  rw [hp] at ht
  linarith

theorem singleton_of_positive (m : Nat)
    (h : 0<(m:ℚ)*(2-(m:ℚ))) : m=1 := by
  by_contra hn
  have hs : m=0 ∨ 2≤m := by omega
  rcases hs with hm | hm
  · simp [hm] at h
  · have hm' : (2:ℚ)≤m := by exact_mod_cast hm
    have hz : (0:ℚ)≤m := by positivity
    have hp := mul_nonpos_of_nonneg_of_nonpos hz (show 2-(m:ℚ)≤0 by linarith)
    linarith

-- The original Boolean bit histogram of a singleton has total mass 1
-- and label 2 absent. A certified positive contrast picks its true bit.
theorem singleton_bit (h0 h1 : Nat) (h : h0+h1=1) :
    (1≤3*(h0:ℤ)-1 ↔ h0=1) ∧
    (1≤3*(h1:ℤ)-1 ↔ h1=1) := by
  constructor <;> constructor <;> intro a <;> omega

-- At most n+1 scales, <=4n+1 continuation + bit queries per scale.
-- Their sound production within a UNIFORM polynomial total physical
-- clock remains the open adequacy obligation, not inferred from this count.
theorem per_scale_queries (n k : Nat) (hk : k≤n+1) :
    n+2*k-1+n≤4*n+1 := by omega

end PNPConstructiveDescent
