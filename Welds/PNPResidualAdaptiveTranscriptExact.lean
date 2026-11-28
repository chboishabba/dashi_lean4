import Welds.PNPResidualGeometryBridgeExact
import Welds.PNPEpochChargeExact

namespace PNPResidualGeometryBridge

/-- The actual coordinate disagreement family of original input bits. -/
def differenceSupport {n : ℕ} (x y : Fin n → Bool) : Set (Fin n) :=
  {i | x i ≠ y i}

/-- At the fixed anchor, a read set distinguishes a rival iff it hits
its original disagreement support. No counting of hypothetical runs. -/
theorem read_agreement_iff_no_hit {n : ℕ} (x y : Fin n → Bool) (R : Set (Fin n)) :
    (∀ i∈R,x i=y i) ↔ ¬ ∃ i, i∈differenceSupport x y ∧ i∈R := by
  constructor
  · intro h hhit
    obtain ⟨i,hi,hr⟩ := hhit
    exact hi (h i hr)
  · intro h i hi
    by_contra hn
    exact h ⟨i,hn,hi⟩

/-- A fixed actual transcript which is invariant under agreement on
its read footprint must hit each same-state different-consumer rival
if the consumer descends through state and transcript.
No assumption of linear states or nonsharing. -/
theorem actual_transcript_hits {n : ℕ} {S T Y : Type*}
    (state : (Fin n → Bool) → S) (transcript : (Fin n → Bool) → T)
    (consumer : (Fin n → Bool) → Y) (x : Fin n → Bool) (R : Set (Fin n))
    (hread : ∀ y,(∀ i∈R,x i=y i) → state x=state y → transcript x=transcript y)
    (hsound : ∀ a b,state a=state b → transcript a=transcript b → consumer a=consumer b)
    (y : Fin n → Bool) (hy : state x=state y) (hd : consumer x≠consumer y) :
    ∃ i,i∈differenceSupport x y ∧ i∈R := by
  by_contra h
  have ha := (read_agreement_iff_no_hit x y R).mpr h
  exact hd (hsound x y hy (hread y ha hy))

/-- Reverse direction: explicit coverage of every relevant rival gives
the local consumer descent criterion on the state/read observation.
Constructing the hitting set and paying adaptive execution remain open. -/
theorem actual_read_consumer_iff {n : ℕ} {S Y : Type*}
    (state : (Fin n → Bool) → S) (consumer : (Fin n → Bool) → Y)
    (x : Fin n → Bool) (R : Set (Fin n)) :
    (∀ y,state x=state y → (∀ i∈R,x i=y i) → consumer x=consumer y) ↔
    (∀ y,state x=state y → consumer x≠consumer y →
      ∃ i,i∈differenceSupport x y ∧ i∈R) := by
  constructor
  · intro h y hy hd
    by_contra hn
    exact hd (h y hy ((read_agreement_iff_no_hit x y R).mpr hn))
  · intro h y hy hr
    by_contra hd
    exact (read_agreement_iff_no_hit x y R).mp hr (h y hy hd)

/-- Instantiate the support criterion on the actual adaptive run owner,
with the footprint of ONE original epoch and the original start state. -/
theorem actual_epoch_support_hit {n : ℕ} {S Y : Type*}
    (ask : S → Option (Fin n × (Bool → S)))
    (prefix : (Fin n → Bool) → S) (consumer : S → Y)
    (x y : Fin n → Bool) (k : ℕ) (h : prefix x=prefix y)
    (hd : consumer (PNPSameRunReadFootprint.run ask x k (prefix x)).1 ≠
      consumer (PNPSameRunReadFootprint.run ask y k (prefix y)).1) :
    ∃ i ∈ (PNPSameRunReadFootprint.run ask x k (prefix x)).2,
      i∈differenceSupport x y := by
  classical
  have hn : (PNPSameRunReadFootprint.run ask x k (prefix x)).1 ≠
      (PNPSameRunReadFootprint.run ask y k (prefix y)).1 :=
    fun e=>hd (congrArg consumer e)
  exact PNPEpochCharge.separated_epoch ask prefix x y k h hn

/-- The exact original epoch observation is sufficient on its own read
footprint, including arbitrary shared state and adaptive query choice. -/
theorem actual_epoch_consumer_factor {n : ℕ} {S Y : Type*}
    (ask : S → Option (Fin n × (Bool → S)))
    (prefix : (Fin n → Bool) → S) (consumer : S → Y)
    (x y : Fin n → Bool) (k : ℕ) (h : prefix x=prefix y)
    (hr : ∀ i∈(PNPSameRunReadFootprint.run ask x k (prefix x)).2,x i=y i) :
    consumer (PNPSameRunReadFootprint.run ask x k (prefix x)).1 =
      consumer (PNPSameRunReadFootprint.run ask y k (prefix y)).1 := by
  exact congrArg (fun p : S × List (Fin n)=>consumer p.1)
    (PNPEpochCharge.survives_epoch ask prefix x y k h hr)

end PNPResidualGeometryBridge
