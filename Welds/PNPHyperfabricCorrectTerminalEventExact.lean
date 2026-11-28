import Welds.PNPHyperfabricOwnedEventsExact

namespace PNPHyperfabricOwnedEvents

/-- Correct decoding at the terminal horizon forces separation of every
reachable consumer-divergent rival. Overlapping windows may share events. -/
theorem correct_terminal_reachable_event {X S I Y : Type*}
    (valid : Set X) (state : X → ℕ → S) (consumer : X → Y)
    (observe : ℕ → X → I) (step : ℕ → S → I → S)
    (stepExact : ∀ z k, state z (k+1)=step k (state z k) (observe k z))
    (decode : S → Y) (x y : X) (a len : ℕ)
    (hx : x ∈ valid)
    (hy : y ∈ ReachableDivergentSet valid state consumer x a)
    (correct : ∀ z ∈ valid, decode (state z (a+len)) = consumer z) :
    ∃ j, a≤j ∧ j<a+len ∧ state x j=state y j ∧
      state x (j+1)≠state y (j+1) ∧ observe j x≠observe j y := by
  apply reachable_epoch_event valid state consumer observe step stepExact x y a len hy
  intro h
  apply hy.2.2
  rw [← correct y hy.1, ← correct x hx, h]

end PNPHyperfabricOwnedEvents
