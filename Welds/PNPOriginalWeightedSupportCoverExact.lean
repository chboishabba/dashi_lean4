import Welds.PNPOriginalTranscriptDisjointSupportExact

/-! A finite weighted dual certificate for original input support
hitting. It permits overlapping disagreement supports and counts
shared actual reads, unlike a rival-count lower bound. Its ceiling
is still the number of original coordinates. -/
namespace PNPResidualGeometryBridge
open scoped BigOperators

/-- Every original support has a selected actual read. If the total
weight of obligations assigned to any one read is bounded by c, the
total obligation weight is at most c times the number of reads.
This is a finite sharing-sensitive capacity certificate, not a
superpolynomial running-time theorem. -/
theorem weighted_original_read_capacity {n m : ℕ}
    (read : Finset (Fin n))
    (select : Fin m → Fin n) (weight : Fin m → ℝ)
    (hread : ∀ i, select i ∈ read)
    (hcapacity : ∀ j ∈ read,
      (∑ i : Fin m, if select i = j then weight i else 0) ≤ 1) :
    (∑ i : Fin m, weight i) ≤ (read.card : ℝ) := by
  classical
  have hrows (i : Fin m) :
      weight i =
        ∑ j ∈ read, if select i = j then weight i else 0 := by
    rw [Finset.sum_ite_eq']
    simp [hread i]
  calc
    (∑ i : Fin m, weight i) =
        ∑ i : Fin m, ∑ j ∈ read,
          if select i = j then weight i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrows i
    _ = ∑ j ∈ read, ∑ i : Fin m,
          if select i = j then weight i else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ read, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcapacity j hj
    _ = read.card := by simp

end PNPResidualGeometryBridge
