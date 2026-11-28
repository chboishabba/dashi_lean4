import Welds.PNPOriginalModularIncidenceExact

namespace PNPIncidenceLine
open PNPOriginalModularIncidence

-- General derived affine rows: an original Boolean coordinate
-- determines every coordinate in this rank-(n-1) chart.
theorem oneFreeRefutes {n : Nat} (F : (Fin n → Bool) → Prop)
    (k : Fin n) (a b : Fin n → ℚ)
    (derived : ∀ x, F x → ∀ j, emb ℚ (x j)=a j+b j*emb ℚ (x k))
    (zeroBad : ∃ j, a j≠0 ∧ a j≠1)
    (oneBad : ∃ j, a j+b j≠0 ∧ a j+b j≠1) :
    ¬ ∃ x, F x := by
  rintro ⟨x,hx⟩
  cases hk : x k
  · obtain ⟨j,h0,h1⟩ := zeroBad
    have h := derived x hx j
    cases hj : x j <;> simp [emb,hk,hj] at h
    · exact h0 h.symm
    · exact h1 h.symm
  · obtain ⟨j,h0,h1⟩ := oneBad
    have h := derived x hx j
    cases hj : x j <;> simp [emb,hk,hj] at h
    · exact h0 h.symm
    · exact h1 h.symm

-- Original eight-column tripartite source. Only six of its nine
-- exact-one rows are needed. Its remaining free coordinate is t=x7.
theorem eightColumnRefutes (x : Fin 8 → Bool)
    (h0 : emb ℚ (x 0)+emb ℚ (x 1)+emb ℚ (x 2)=1)
    (h2 : emb ℚ (x 6)+emb ℚ (x 7)=1)
    (h4 : emb ℚ (x 1)+emb ℚ (x 7)=1)
    (h5 : emb ℚ (x 2)+emb ℚ (x 4)+emb ℚ (x 5)=1)
    (h6 : emb ℚ (x 1)+emb ℚ (x 4)=1)
    (h7 : emb ℚ (x 5)+emb ℚ (x 6)=1) : False := by
  have hA : emb ℚ (x 0)=3*emb ℚ (x 7)-1 := by linarith
  have hB : emb ℚ (x 2)=1-2*emb ℚ (x 7) := by linarith
  cases ht : x 7
  · cases h : x 0 <;> norm_num [emb,ht,h] at hA
  · cases h : x 2 <;> norm_num [emb,ht,h] at hB

-- This proves the actual Boolean obstruction despite signed integer
-- and fractional feasible relaxations. No arbitrary nullity bound.
end PNPIncidenceLine
