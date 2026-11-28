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
        · by_cases hm : j ∈ differenceSupport x (rivals i)
          · simp [h, hm, hweight i]
          · simp [h, hm]
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


/-- Consume the ACTUAL transcript observation theorem. The hitting-set
premise is derived from same-state divergence and sound execution,
rather than supplied independently. Overlaps are allowed, but the
fractional-capacity premise remains an explicit original-coordinate
certificate, and hence is limited to n total mass. -/
theorem actual_transcript_fractional_support_lower_bound
    {n m : ℕ} {S T Y : Type*}
    (state : (Fin n → Bool) → S)
    (transcript : (Fin n → Bool) → T)
    (consumer : (Fin n → Bool) → Y)
    (x : Fin n → Bool) (read : Finset (Fin n))
    (rivals : Fin m → Fin n → Bool)
    (weight : Fin m → ℝ)
    (hread : ∀ y, (∀ j ∈ (↑read : Set (Fin n)), x j = y j) →
      state x = state y → transcript x = transcript y)
    (hsound : ∀ a b, state a = state b →
      transcript a = transcript b → consumer a = consumer b)
    (hsame : ∀ i, state x = state (rivals i))
    (hdiff : ∀ i, consumer x ≠ consumer (rivals i))
    (hweight : ∀ i, 0 ≤ weight i)
    (hcapacity : ∀ j : Fin n,
      (∑ i : Fin m,
        if j ∈ differenceSupport x (rivals i) then weight i else 0) ≤ 1) :
    (∑ i : Fin m, weight i) ≤ (read.card : ℝ) := by
  apply original_fractional_support_lower_bound
    x rivals read weight
  · intro i
    obtain ⟨j, hj, hr⟩ :=
      actual_transcript_hits state transcript consumer x
        (↑read : Set (Fin n)) hread hsound
        (rivals i) (hsame i) (hdiff i)
    exact ⟨j, hr, hj⟩
  · exact hweight
  · exact hcapacity


end PNPResidualGeometryBridge
