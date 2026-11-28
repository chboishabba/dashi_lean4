import Welds.PNPResidualAdaptiveTranscriptExact

/-! Section 21f. Same-run read footprint lower bound from genuinely
disjoint original disagreement supports. This cannot by itself prove
superpolynomial complexity: there are at most n disjoint nonempty
supports on n input bits. -/
namespace PNPResidualGeometryBridge

/-- Distinct disjoint consumer-relevant supports require distinct read
coordinates, on the same original input footprint. Pairwise disjointness
is a hypothesis on the ORIGINAL supports, not on arbitrary labels. -/
theorem original_disjoint_support_read_lower_bound {n m : ℕ}
    (x : Fin n → Bool) (rivals : Fin m → Fin n → Bool)
    (read : Finset (Fin n))
    (hits : ∀ i : Fin m, ∃ j ∈ read, x j ≠ rivals i j)
    (disjoint : ∀ i k : Fin m, i ≠ k →
      Disjoint (differenceSupport x (rivals i))
        (differenceSupport x (rivals k))) :
    m ≤ read.card := by
  classical
  choose j hj using hits
  have inj : Function.Injective j := by
    intro i k he
    by_contra hne
    have hi : j i ∈ differenceSupport x (rivals i) := (hj i).2
    have hk : j i ∈ differenceSupport x (rivals k) := by
      change x (j i) ≠ rivals k (j i)
      simpa only [he] using (hj k).2
    exact (Set.disjoint_left.mp (disjoint i k hne)) hi hk
  let f : Fin m → {z : Fin n // z ∈ read} :=
    fun i => ⟨j i, (hj i).1⟩
  have hf : Function.Injective f := by
    intro i k e
    apply inj
    exact congrArg Subtype.val e
  have bound := Fintype.card_le_of_injective f hf
  simpa using bound

end PNPResidualGeometryBridge
