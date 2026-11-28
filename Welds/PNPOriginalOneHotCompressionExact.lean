import Welds.PNPAffineAccumulatorExact
import Welds.PNPNormalMassExact

namespace PNPOriginalOneHotCompression
open PNPFrontierResolution PNPOriginalModularIncidence
open scoped BigOperators

def OneHot {n : Nat} (x : Assignment n) (row : Finset (Fin n)) : Prop :=
  ∃ i∈row, x i=true ∧ ∀ j∈row, x j=true → j=i

theorem oneHot_positive {n : Nat} (x : Assignment n) (row : Finset (Fin n))
    (h : OneHot x row) : SatClause x (positive row) := by
  obtain ⟨i,hi,hx,_⟩ := h
  exact ⟨(i,true),Finset.mem_image.mpr ⟨i,hi,rfl⟩,hx⟩

theorem oneHot_negative {n : Nat} (x : Assignment n) (row : Finset (Fin n))
    (h : OneHot x row) (i j : Fin n) (hi : i∈row) (hj : j∈row) (hne : i≠j) :
    SatClause x (negativePair i j) := by
  obtain ⟨k,hk,hx,uniq⟩ := h
  cases ei : x i
  · exact ⟨(i,false),by simp [negativePair],ei⟩
  · cases ej : x j
    · exact ⟨(j,false),by simp [negativePair],ej⟩
    · exact False.elim (hne ((uniq i hi ei).trans (uniq j hj ej).symm))

-- Every removed clause is covered by an actual checked source row.
-- Overlapping one-hot rows are allowed: conjunction, not disjointness.
theorem original_iff_compressed {n : Nat} (F G : List (Clause n))
    (O : List (Finset (Fin n))) (x : Assignment n)
    (retained : ∀ c∈G,c∈F)
    (pos : ∀ row∈O,positive row∈F)
    (neg : ∀ row∈O,∀ i∈row,∀ j∈row,i≠j → negativePair i j∈F)
    (cover : ∀ c∈F,c∈G ∨
      ∃ row∈O,c=positive row ∨
        ∃ i∈row,∃ j∈row,i≠j ∧ c=negativePair i j) :
    SatAll x F ↔ SatAll x G ∧ ∀ row∈O,OneHot x row := by
  constructor
  · intro hx
    refine ⟨fun c hc => hx c (retained c hc),fun row hr => ?_⟩
    exact exactOneFromClauses F x row hx (pos row hr) (neg row hr)
  · rintro ⟨hx,ho⟩ c hc
    rcases cover c hc with hg|⟨row,hr,e|⟨i,hi,j,hj,hne,e⟩⟩
    · exact hx c hg
    · rw [e]
      exact oneHot_positive x row (ho row hr)
    · rw [e]
      exact oneHot_negative x row (ho row hr) i j hi hj hne

theorem countSelected {n : Nat} (x : Assignment n) (row : Finset (Fin n)) :
    (∑ j∈row,if x j then (1 : Nat) else 0)=
      (row.filter (fun j => x j=true)).card := by
  classical
  -- Rewrite the filtered sum of ones to the indicator sum.
  simp [Finset.card_eq_sum_ones,Finset.sum_filter]

-- Boolean exact-one iff natural row sum equals one. This is NOT
-- equivalence with odd parity, which is only a necessary relaxation.
theorem oneHot_iff_count {n : Nat} (x : Assignment n) (row : Finset (Fin n)) :
    OneHot x row ↔ (row.filter (fun j => x j=true)).card=1 := by
  classical
  constructor
  · rintro ⟨i,hi,hx,uniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨i,?_⟩
    ext j
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hj,hy⟩
      exact uniq j hj hy
    · intro e
      subst j
      exact ⟨hi,hx⟩
  · intro h
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
    have hm : i∈row.filter (fun j => x j=true) := by rw [hi]; simp
    obtain ⟨hr,hx⟩ := Finset.mem_filter.mp hm
    refine ⟨i,hr,hx,fun j hj hv => ?_⟩
    have hmem := Finset.mem_filter.mpr ⟨hj,hv⟩
    rw [hi] at hmem
    exact Finset.mem_singleton.mp hmem

theorem oneHot_iff_sum {n : Nat} (x : Assignment n) (row : Finset (Fin n)) :
    OneHot x row ↔ (∑ j∈row,if x j then (1 : Nat) else 0)=1 := by
  rw [countSelected,oneHot_iff_count]

theorem oneHot_parity {n : Nat} (x : Assignment n) (row : Finset (Fin n))
    (h : OneHot x row) :
    (∑ j : Fin n,(if j∈row then 1 else 0 : ZMod 2)*emb (ZMod 2) (x j))=1 :=
  exactOne_sum x row h

end PNPOriginalOneHotCompression
