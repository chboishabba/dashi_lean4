import Welds.PNPHyperfabricOwnedEventsExact

namespace PNPHyperfabricOwnedEvents

/-- Each obligation must be supplied by a reachable rival colliding at
the start and separating at the actual end of its window. Select one
actual event from each window, not from a counterfactual execution.
Pairwise disjoint windows pay distinct time positions on one run. -/
theorem actual_disjoint_epoch_packing {X S I Y : Type*}
    (valid : Set X) (state : X → ℕ → S) (consumer : X → Y)
    (observe : ℕ → X → I) (step : ℕ → S → I → S)
    (stepExact : ∀ z k, state z (k+1)=step k (state z k) (observe k z))
    (x : X) (m T : ℕ) (a len : Fin m → ℕ) (rival : Fin m → X)
    (hr : ∀ i, rival i ∈ ReachableDivergentSet valid state consumer x (a i))
    (he : ∀ i, state x (a i+len i) ≠ state (rival i) (a i+len i))
    (hT : ∀ i, a i+len i≤T)
    (hdisjoint : ∀ i j, i≠j →
      a i+len i≤a j ∨ a j+len j≤a i) :
    ∃ event : Fin m ↪ Fin T,
      ∀ i, a i≤(event i).val ∧ (event i).val<a i+len i ∧
        state x (event i).val=state (rival i) (event i).val ∧
        state x ((event i).val+1)≠state (rival i) ((event i).val+1) ∧
        observe (event i).val x≠observe (event i).val (rival i) := by
  classical
  have h := fun i => reachable_epoch_event valid state consumer observe step
    stepExact x (rival i) (a i) (len i) (hr i) (he i)
  choose j hj using h
  let e : Fin m → Fin T := fun i => ⟨j i,lt_of_lt_of_le (hj i).2.1 (hT i)⟩
  have hinj : Function.Injective e := by
    intro i k heq
    by_contra hne
    have hval : j i=j k := congrArg Fin.val heq
    rcases hdisjoint i k hne with hle|hle
    · omega
    · omega
  exact ⟨⟨e,hinj⟩,hj⟩

theorem actual_disjoint_epoch_ceiling {X S I Y : Type*}
    (valid : Set X) (state : X → ℕ → S) (consumer : X → Y)
    (observe : ℕ → X → I) (step : ℕ → S → I → S)
    (stepExact : ∀ z k, state z (k+1)=step k (state z k) (observe k z))
    (x : X) (m T : ℕ) (a len : Fin m → ℕ) (rival : Fin m → X)
    (hr : ∀ i, rival i ∈ ReachableDivergentSet valid state consumer x (a i))
    (he : ∀ i, state x (a i+len i) ≠ state (rival i) (a i+len i))
    (hT : ∀ i, a i+len i≤T)
    (hdisjoint : ∀ i j, i≠j → a i+len i≤a j ∨ a j+len j≤a i) :
    m≤T := by
  obtain ⟨e,_⟩ := actual_disjoint_epoch_packing valid state consumer observe
    step stepExact x m T a len rival hr he hT hdisjoint
  simpa using Fintype.card_le_of_injective e e.injective

end PNPHyperfabricOwnedEvents
