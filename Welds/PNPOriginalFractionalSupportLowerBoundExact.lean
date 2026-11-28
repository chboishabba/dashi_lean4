import Welds.PNPOriginalWeightedSupportCoverExact

/-!
# Fractional original-disagreement-support certificate

This turns a weighted *family of original divergent supports* into an
actual read-footprint lower bound, while allowing arbitrary overlap.
The weight capacity is imposed at each original coordinate, before the
chosen execution trace picks its read. The total weight cannot exceed n
under these assumptions; no unrestricted complexity claim is made.
-/

namespace PNPResidualGeometryBridge
open scoped BigOperators

theorem original_fractional_support_lower_bound {n m : ℕ}
    (x : Fin n → Bool)
    (rivals : Fin m → Fin n → Bool)
    (read : Finset (Fin n)) (weight : Fin m → ℝ)
    (hits : ∀ i : Fin m,
      ∃ j ∈ read, j ∈ differenceSupport x (rivals i))
    (hweight : ∀ i, 0 ≤ weight i)
    (hcapacity : ∀ j : Fin n,
      (∑ i : Fin m,
        if j ∈ differenceSupport x (rivals i) then weight i else 0) ≤ 1) :
    (∑ i : Fin m, weight i) ≤ (read.card : ℝ) := by
  classical
  choose select hs using hits
  apply weighted_original_read_capacity read select weight
  · intro i
    exact (hs i).1
  · intro j hj
    calc
      (∑ i : Fin m, if select i = j then weight i else 0) ≤
          ∑ i : Fin m,
            if j ∈ differenceSupport x (rivals i) then weight i else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : select i = j
        · subst j
          simp [(hs i).2]
        · simp only [h, ite_false]
          split_ifs <;> exact hweight i
      _ ≤ 1 := hcapacity j

/-- The fractional witness cannot exceed the original input dimension.
An exponential family of supports does not evade the n-coordinate
capacity ceiling by being enumerated many times. -/
theorem original_fractional_support_input_ceiling {n m : ℕ}
    (x : Fin n → Bool)
    (rivals : Fin m → Fin n → Bool)
    (weight : Fin m → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcapacity : ∀ j : Fin n,
      (∑ i : Fin m,
        if j ∈ differenceSupport x (rivals i) then weight i else 0) ≤ 1)
    (hnonempty : ∀ i, (differenceSupport x (rivals i)).Nonempty) :
    (∑ i : Fin m, weight i) ≤ (n : ℝ) := by
  classical
  have hits : ∀ i : Fin m,
      ∃ j ∈ (Finset.univ : Finset (Fin n)),
        j ∈ differenceSupport x (rivals i) := by
    intro i
    obtain ⟨j, hj⟩ := hnonempty i
    exact ⟨j, Finset.mem_univ j, hj⟩
  have h := original_fractional_support_lower_bound
    x rivals (Finset.univ : Finset (Fin n)) weight
    hits hweight hcapacity
  simpa using h

end PNPResidualGeometryBridge
