import Welds.PNPHyperfabricActualEpochPackingExact

namespace PNPHyperfabricOwnedEvents

/-- Correct local decoders at each actual window end discharge separation.
Disjointness is still a genuine resource premise, not inferred from rivalry. -/
theorem correct_window_packing {X S I Y : Type*}
    (valid : Set X) (state : X → ℕ → S) (consumer : X → Y)
    (observe : ℕ → X → I) (step : ℕ → S → I → S)
    (stepExact : ∀ z k, state z (k+1)=step k (state z k) (observe k z))
    (x : X) (m T : ℕ) (a len : Fin m → ℕ) (rival : Fin m → X)
    (hx : x ∈ valid)
    (hr : ∀ i, rival i ∈ ReachableDivergentSet valid state consumer x (a i))
    (decode : Fin m → S → Y)
    (hc : ∀ i z, z ∈ valid → decode i (state z (a i+len i))=consumer z)
    (hT : ∀ i, a i+len i≤T)
    (hdisjoint : ∀ i j, i≠j → a i+len i≤a j ∨ a j+len j≤a i) :
    m≤T := by
  apply actual_disjoint_epoch_ceiling valid state consumer observe step stepExact
    x m T a len rival hr _ hT hdisjoint
  intro i h
  have hri := hr i
  apply hri.2.2
  calc
    consumer (rival i) = decode i (state (rival i) (a i+len i)) := (hc i _ hri.1).symm
    _ = decode i (state x (a i+len i)) := congrArg (decode i) h.symm
    _ = consumer x := hc i x hx

end PNPHyperfabricOwnedEvents
