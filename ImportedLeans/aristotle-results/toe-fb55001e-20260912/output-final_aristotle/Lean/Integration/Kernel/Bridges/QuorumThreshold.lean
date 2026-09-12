import Integration.Kernel.EvidenceDependence

/-!
# Bridge: quorum thresholds ↔ collective state transitions

A small bridge module, deliberately narrow.  The donor observation is that a
population can hold a shared state which flips only once enough members are in
the active configuration.  The question worth asking of the corpus is whether
that gives any mathematical structure beyond "a monotone predicate on a finite
set", and the answer this file records is: it gives one useful thing, namely
that **a quorum counted by participants is not a quorum counted by independent
provenance**.

## What is proved

* `Switched`, `switched_monotone`, `switched_iff_card` — the threshold rule as a
  monotone predicate of the active set.
* **`one_member_flips_the_collective_state`** — the transition is genuinely a
  threshold and not a gradient: one additional member takes the population from
  not-switched to switched.
* **`collective_state_is_not_an_individual_property`** — no reading of a single
  member's state returns the collective verdict.
* **`quorum_by_count_is_not_quorum_by_independent_roots`** — the bridge to
  `Integration.Kernel.EvidenceDependence`: a population can be over threshold by
  headcount while its provenance support has cardinality one, so a thresholded
  collective transition licenses nothing about independent corroboration.

**Claim boundary.**  Members are elements of `Fin 6`, the threshold is a
stipulated natural number and provenance is a stipulated assignment.  Nothing
models any organism, signalling molecule, committee or vote.
-/

namespace Integration.Kernel.Bridges.QuorumThreshold

open Integration.Kernel.Quotient Integration.Kernel.EvidenceDependence

/-! ## §1 The threshold rule -/

/-- The members of the population. -/
abbrev Member := Fin 6

/-- The quorum. -/
def threshold : ℕ := 4

/-- The collective has switched. -/
def Switched (active : Finset Member) : Prop := threshold ≤ active.card

instance (active : Finset Member) : Decidable (Switched active) :=
  inferInstanceAs (Decidable (threshold ≤ active.card))

theorem switched_iff_card (active : Finset Member) : Switched active ↔ threshold ≤ active.card :=
  Iff.rfl

theorem switched_monotone {a b : Finset Member} (h : a ⊆ b) (ha : Switched a) : Switched b :=
  le_trans ha (Finset.card_le_card h)

/-- **The transition is a threshold, not a gradient.**  Three active members
leave the collective unswitched; the fourth flips it. -/
theorem one_member_flips_the_collective_state :
    ¬ Switched ({0, 1, 2} : Finset Member) ∧ Switched ({0, 1, 2, 3} : Finset Member) := by
  refine ⟨by decide, by decide⟩

/-- **The collective state is not an individual property.**  Two active sets
agree on member `0` and differ in whether the collective has switched. -/
theorem collective_state_is_not_an_individual_property :
    ¬ DescendsThrough (fun a : Finset Member => decide (Switched a))
        (fun a : Finset Member => decide ((0 : Member) ∈ a)) :=
  not_descendsThrough_of_collision
    (x := ({0, 1, 2} : Finset Member)) (y := ({0, 1, 2, 3} : Finset Member)) (by decide) (by decide)

/-! ## §2 What the threshold does not license -/

/-- A provenance in which every member rests on the same root. -/
def sharedRoots : Provenance Member ℕ := ⟨fun _ => {0}⟩

/-- **A quorum by headcount is not a quorum by independent provenance.**  Five
active members put the collective over threshold, and their whole provenance
support has cardinality one — well under it. -/
theorem quorum_by_count_is_not_quorum_by_independent_roots :
    Switched ({0, 1, 2, 3, 4} : Finset Member) ∧
      (rootSupport sharedRoots [0, 1, 2, 3, 4]).card = 1 ∧
        ¬ threshold ≤ (rootSupport sharedRoots [0, 1, 2, 3, 4]).card := by
  refine ⟨by decide, by decide, by decide⟩

/-- And no two members of such a population are independent evidence. -/
theorem members_are_not_independent (i j : Member) : ¬ Independent sharedRoots i j :=
  shared_root_blocks_independent_replication ⟨0, by simp [sharedRoots], by simp [sharedRoots]⟩

end Integration.Kernel.Bridges.QuorumThreshold
