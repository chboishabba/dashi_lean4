import Welds.PNPOriginalDisjointSupportReadLowerBoundExact

/-! Section 21g: consume the actual same-state consumer transcript
criterion to derive a quantitative original read-footprint bound.
Disjoint original disagreement supports remain explicit, and imply at
most input-length charges. This is not an unrestricted complexity proof. -/
namespace PNPResidualGeometryBridge

theorem actual_transcript_disjoint_support_lower_bound
    {n m : ℕ} {S T Y : Type*}
    (state : (Fin n → Bool) → S)
    (transcript : (Fin n → Bool) → T)
    (consumer : (Fin n → Bool) → Y)
    (x : Fin n → Bool) (read : Finset (Fin n))
    (rivals : Fin m → Fin n → Bool)
    (hread : ∀ y, (∀ i ∈ (↑read : Set (Fin n)), x i = y i) →
      state x = state y → transcript x = transcript y)
    (hsound : ∀ a b, state a = state b →
      transcript a = transcript b → consumer a = consumer b)
    (hsame : ∀ i, state x = state (rivals i))
    (hdiff : ∀ i, consumer x ≠ consumer (rivals i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint (differenceSupport x (rivals i))
        (differenceSupport x (rivals k))) :
    m ≤ read.card := by
  apply original_disjoint_support_read_lower_bound x rivals read
  · intro i
    obtain ⟨j, hj, hr⟩ :=
      actual_transcript_hits state transcript consumer x
        (↑read : Set (Fin n)) hread hsound
        (rivals i) (hsame i) (hdiff i)
    exact ⟨j, hr, hj⟩
  · exact hdisjoint

/-- Every charge of this kind is bounded by the original input support.
No unearned superpolynomial lower bound is available from disjointness. -/
theorem actual_transcript_disjoint_support_input_ceiling
    {n m : ℕ} {S T Y : Type*}
    (state : (Fin n → Bool) → S)
    (transcript : (Fin n → Bool) → T)
    (consumer : (Fin n → Bool) → Y)
    (x : Fin n → Bool) (read : Finset (Fin n))
    (rivals : Fin m → Fin n → Bool)
    (hread : ∀ y, (∀ i ∈ (↑read : Set (Fin n)), x i = y i) →
      state x = state y → transcript x = transcript y)
    (hsound : ∀ a b, state a = state b →
      transcript a = transcript b → consumer a = consumer b)
    (hsame : ∀ i, state x = state (rivals i))
    (hdiff : ∀ i, consumer x ≠ consumer (rivals i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint (differenceSupport x (rivals i))
        (differenceSupport x (rivals k))) :
    m ≤ n := by
  calc
    m ≤ read.card :=
      actual_transcript_disjoint_support_lower_bound
        state transcript consumer x read rivals hread hsound
        hsame hdiff hdisjoint
    _ ≤ n := by simpa using (Finset.card_le_univ read)

end PNPResidualGeometryBridge
