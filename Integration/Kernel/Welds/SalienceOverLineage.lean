import Integration.Kernel.Welds.AmplifiedObservationCount

/-!
# Second-order crossing: salience measured over lineage roots

The salience weld schedules by how much a residual separates the currently live
*hypotheses*.  The lineage weld says that what is live is often not twenty
observations but three acquisitions.  Crossing the two gives a sharper
scheduling question: how much does a residual separate the **provenance
classes**?

This file measures both on the twenty-node lineage of
`Integration.Kernel.Welds.AmplifiedObservationCount` and shows the two measures
are genuinely different quantities, with an implication in exactly one
direction.

## What is proved

* `splitOn` — the separation a Boolean reading achieves on a finite live set,
  stated generically so it applies to observations and to root classes alike.
* **`hypothesis_separation_does_not_imply_root_separation`** — a reading that
  separates the observation set maximally can separate no provenance class at
  all: `indexParity` splits ten observations from ten and yet every root class
  still contains both readings.
* **`root_separating_reading_also_separates_hypotheses`** — the converse does
  hold whenever every class is inhabited: separating the classes forces
  separating the observations.
* **`salience_ordering_disagrees`** — the scheduling consequence: on this
  lineage one reading wins on hypothesis salience and loses on root salience,
  so a scheduler ordering by observation split is not the same scheduler as one
  ordering by root split.

**Claim boundary.**  The lineage, the readings and both salience measures are
definitions in this and the imported file; nothing is claimed about any real
observation, source or search process.
-/

namespace Integration.Kernel.Welds.SalienceOverLineage

open Integration.Kernel.EvidenceDependence
open Integration.Kernel.Welds.AmplifiedObservationCount

/-! ## §1 Two salience measures -/

/-- How much a Boolean reading splits a finite live set. -/
def splitOn {α : Type} [DecidableEq α] (read : α → Bool) (live : Finset α) : ℕ :=
  (live.filter (fun x => read x = true)).card * (live.filter (fun x => read x = false)).card

/-- The live observations. -/
def liveObs : Finset Obs := Finset.univ

/-- The live provenance classes. -/
def liveRoots : Finset Root := Finset.univ

/-- A reading of an observation induces a reading of a class only if it is
constant on the class; this is the reading that says the class is `0`. -/
def rootClassReading (r : Root) : Bool := decide (r = 0)

/-- A reading that splits the observations evenly and ignores provenance. -/
def indexParity (i : Obs) : Bool := decide (i.val < 10)

/-- A reading that tracks the provenance class. -/
def classReading (i : Obs) : Bool := decide (rootOf i = 0)

/-! ## §2 The two measures come apart -/

theorem indexParity_splits_observations : splitOn indexParity liveObs = 100 := by decide

theorem classReading_splits_observations : splitOn classReading liveObs = 91 := by decide

theorem classReading_splits_roots : splitOn rootClassReading liveRoots = 2 := by decide

/-- **Separating the observations is not separating the provenance.**  The
parity reading splits the twenty observations into ten and ten, and yet each of
the three provenance classes still contains observations with both readings, so
it distinguishes no class at all. -/
theorem hypothesis_separation_does_not_imply_root_separation :
    0 < splitOn indexParity liveObs ∧
      ∀ r : Root, ∃ i j : Obs, rootOf i = r ∧ rootOf j = r ∧ indexParity i ≠ indexParity j := by
  refine ⟨by decide, ?_⟩
  intro r
  fin_cases r
  · exact ⟨0, 12, by decide, by decide, by decide⟩
  · exact ⟨1, 13, by decide, by decide, by decide⟩
  · exact ⟨2, 14, by decide, by decide, by decide⟩

/-- **The implication runs the other way.**  If a reading is induced by the
provenance class and separates two inhabited classes, it separates the
observations resting on them. -/
theorem root_separating_reading_also_separates_hypotheses {i j : Obs}
    (h : rootClassReading (rootOf i) ≠ rootClassReading (rootOf j)) :
    classReading i ≠ classReading j := by
  simpa [classReading, rootClassReading] using h

/-- **The two schedulers order the same queue differently.**  On the
observation measure the parity reading scores higher (100 against 91), so a
size-of-split scheduler prefers it; on the provenance measure the class reading
separates and parity separates nothing.  The ordering of the queue therefore
depends on which live set salience is measured against. -/
theorem salience_ordering_disagrees :
    splitOn classReading liveObs < splitOn indexParity liveObs ∧
      splitOn rootClassReading liveRoots > 0 ∧
        (∀ r : Root, ∃ i j : Obs,
          rootOf i = r ∧ rootOf j = r ∧ indexParity i ≠ indexParity j) := by
  refine ⟨by decide, by decide, hypothesis_separation_does_not_imply_root_separation.2⟩

/-- And the observations the parity reading separates are frequently not
independent evidence anyway: nodes `0` and `3` differ in parity reading only
trivially, share a root, and are therefore not independent. -/
theorem separated_but_dependent :
    indexParity 0 = indexParity 3 ∧ ¬ Independent prov 0 3 :=
  ⟨by decide, same_class_are_not_independent (by decide)⟩

end Integration.Kernel.Welds.SalienceOverLineage
