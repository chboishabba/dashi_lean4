import Welds.PNPOriginalModularIncidenceExact

namespace PNPNonlinearObservationLift
open PNPFrontierResolution PNPOriginalModularIncidence
open scoped BigOperators

-- The observations are actual functions on original Boolean assignments,
-- not independent ambient field coordinates. A verified block truth table
-- certifies that every failing original local pattern is excluded by F.
theorem observationRow {n m k : Nat} (F : List (Clause n))
    (scope : Fin m → Finset (Fin n)) (obs : Fin k → Assignment n → ZMod 2)
    (A : Fin m → Fin k → ZMod 2) (b : Fin m → ZMod 2)
    (covered : ∀ i x, (∑ j,A i j*obs j x)≠b i →
      blocking (scope i) x ∈ F)
    (x : Assignment n) (hx : SatAll x F) :
    ∀ i, (∑ j,A i j*obs j x)=b i := by
  intro i
  by_contra h
  exact blocking_excludes (scope i) x (hx _ (covered i x h))

-- Overlapping nonlinear observations are allowed for refutation.
-- The lifted linear system is only a necessary condition for SAT.
theorem original_observation_conflict {n m k : Nat} (F : List (Clause n))
    (scope : Fin m → Finset (Fin n)) (obs : Fin k → Assignment n → ZMod 2)
    (A : Fin m → Fin k → ZMod 2) (b y : Fin m → ZMod 2)
    (covered : ∀ i x, (∑ j,A i j*obs j x)≠b i →
      blocking (scope i) x ∈ F)
    (annihilate : ∀ j,(∑ i,y i*A i j)=0)
    (nonzero : (∑ i,y i*b i)≠0) :
    ¬ ∃ x : Assignment n, SatAll x F := by
  rintro ⟨x,hx⟩
  exact modular_conflict A b y (fun j => obs j x)
    (observationRow F scope obs A b covered x hx) annihilate nonzero

-- For a Boolean-valued observation, a zero and a one preimage suffice
-- for all requested bits. The source-discovered disjoint support
-- test is needed before combining such preimages.
theorem boolean_surjective {X : Type*} (f : X → Bool)
    (x0 x1 : X) (h0 : f x0=false) (h1 : f x1=true) :
    Function.Surjective f := by
  intro b
  cases b
  · exact ⟨x0,h0⟩
  · exact ⟨x1,h1⟩

theorem disjoint_support_reopen {n k : Nat}
    (scope : Fin k → Finset (Fin n))
    (obs : Fin k → Assignment n → Bool)
    (locality : ∀ i x y, (∀ j∈scope i,x j=y j) → obs i x=obs i y)
    (disjoint : ∀ i i' j, j∈scope i → j∈scope i' → i=i')
    (preimage : ∀ i, Function.Surjective (obs i))
    (target : Fin k → Bool) :
    ∃ x : Assignment n, ∀ i, obs i x=target i := by
  classical
  choose z hz using fun i => preimage i (target i)
  let x : Assignment n := fun j =>
    if h : ∃ i, j∈scope i then z (Classical.choose h) j else false
  refine ⟨x,fun i => ?_⟩
  rw [locality i x (z i) ?_,hz i]
  intro j hj
  have h : ∃ i',j∈scope i' := ⟨i,hj⟩
  have e : Classical.choose h=i :=
    disjoint _ _ j (Classical.choose_spec h) hj
  simp [x,h,e]

-- These are receiver proofs. The concrete bounded table and Moebius
-- certificate interpreter is Python-replayed, not kernel-accepted.
end PNPNonlinearObservationLift
