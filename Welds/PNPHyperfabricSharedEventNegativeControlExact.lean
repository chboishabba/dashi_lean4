import Welds.PNPHyperfabricCorrectTerminalEventExact

namespace PNPHyperfabricOwnedEvents

/-- Arbitrarily many distinct rivals share a single actual read.
The input is a consumer bit plus an arbitrary irrelevant address.
This is a negative control, not a claim about SAT complexity. -/
theorem shared_event_rivals (m : ℕ) :
    ∃ (consumer : Bool × Fin m → Bool)
      (state : Bool × Fin m → ℕ → Bool)
      (observe : ℕ → Bool × Fin m → Bool)
      (step : ℕ → Bool → Bool → Bool),
      (∀ z k, state z (k+1)=step k (state z k) (observe k z)) ∧
      (∀ z, state z 1=consumer z) ∧
      (∀ i : Fin m, ∀ j : Fin m,
        state (false,i) 0=state (true,j) 0 ∧
        consumer (false,i)≠consumer (true,j) ∧
        observe 0 (false,i)≠observe 0 (true,j)) := by
  refine ⟨Prod.fst, fun z k => if k=0 then false else z.1,
    fun _ z => z.1, fun _ _ b => b, ?_, ?_, ?_⟩
  · intro z k
    simp
  · intro z
    simp
  · intro i j
    simp

end PNPHyperfabricOwnedEvents
