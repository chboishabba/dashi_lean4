import Integration.Kernel.Welds.RuntimeBraidedProvenance
import Integration.Kernel.Welds.CommutingProvenanceSquare

/-!
# Second-order crossing: lane extraction is a projection, and the flat log is not

The two welds `Integration.Kernel.Welds.RuntimeBraidedProvenance` and
`Integration.Kernel.Welds.CommutingProvenanceSquare` were built independently.
This file makes one constrain the other, which is the second-order crossing the
frontier asked for: *does the lane-extraction map of a braided runtime trace
satisfy the commuting-square discipline that the provenance weld demands before
a coarse reading may be called a projection of a fine record?*

It does, and the square is proved rather than assumed.  The pooled reading, by
contrast, does not even determine the lane data, so it cannot be a projection of
anything lane-sensitive.

## What is proved

* `laneRoots_append` — the recurrence that makes the square possible: appending
  an event unions in its roots when the event is in the lane and changes nothing
  otherwise.
* **`lane_extraction_is_a_projection`** — for every event `e` and lane `l`, the
  lane-root map intertwines "append `e`" on traces with `laneStep e l` on root
  sets, in the exact sense of
  `Integration.Kernel.Welds.CommutingProvenanceSquare.IsProjection`.
* `laneProjectionClaim` — the same fact packaged as a `ProjectionClaim`, so
  `ProjectionClaim.transports` applies and the lane reading of a trace is
  correct after any number of appends (`lane_roots_transport`).
* **`flat_log_is_not_a_projection_of_the_lane_state`** — the negative half: the
  payload log does not determine the lane assignment, so no coarse step on it
  can be a projection of the lane-indexed record.

**Claim boundary.**  As in both parent files: events, lanes and roots are finite
labels, and nothing models an actual runtime or knowledge holder.
-/

namespace Integration.Kernel.Welds.LaneProjectionSquare

open Integration.Kernel.Quotient
open Integration.Kernel.Welds.RuntimeBraidedProvenance
open Integration.Kernel.Welds.CommutingProvenanceSquare

variable {Lane R : Type} [DecidableEq Lane] [DecidableEq R]

/-! ## §1 The recurrence -/

/-- The coarse step on a lane's root set when event `e` is appended. -/
def laneStep (e : Event Lane R) (l : Lane) (s : Finset R) : Finset R :=
  if e.lane = l then s ∪ e.roots else s

/-- Appending an event unions in its roots exactly when it belongs to the lane. -/
theorem laneRoots_append (t : Trace Lane R) (e : Event Lane R) (l : Lane) :
    laneRoots (t ++ [e]) l = laneStep e l (laneRoots t l) := by
  induction t with
  | nil =>
      by_cases h : e.lane = l <;>
        simp [laneRoots, laneEvents, laneStep, h]
  | cons a t ih =>
      by_cases ha : a.lane = l
      · simp only [List.cons_append, laneRoots, laneEvents, List.filter_cons, ha,
          beq_self_eq_true, if_true, List.foldr_cons] at *
        rw [ih]
        by_cases h : e.lane = l <;> simp [laneStep, h, Finset.union_assoc]
      · have hb : (a.lane == l) = false := by simpa using ha
        simp only [List.cons_append, laneRoots, laneEvents, List.filter_cons, hb] at *
        exact ih

/-! ## §2 The square -/

/-- **Lane extraction is a projection.**  The lane-root map intertwines the
runtime step (append this event) with the coarse step on root sets, so a lane
reading is a genuine projection of the trace and not merely compatible with
it. -/
theorem lane_extraction_is_a_projection (e : Event Lane R) (l : Lane) :
    IsProjection (fun t : Trace Lane R => laneRoots t l) (fun t => t ++ [e]) (laneStep e l) :=
  fun t => laneRoots_append t e l

/-- Packaged with its square, so the transport theorem applies. -/
def laneProjectionClaim (e : Event Lane R) (l : Lane) :
    ProjectionClaim (Trace Lane R) (Finset R) where
  pi := fun t => laneRoots t l
  fine := fun t => t ++ [e]
  coarse := laneStep e l
  square := lane_extraction_is_a_projection e l

/-- **The lane reading survives the whole pipeline.**  After `n` appends of the
same event, the coarse computation and the recomputed lane roots agree. -/
theorem lane_roots_transport (e : Event Lane R) (l : Lane) (t : Trace Lane R) (n : ℕ) :
    (laneStep e l)^[n] (laneRoots t l) = laneRoots ((fun s => s ++ [e])^[n] t) l :=
  (laneProjectionClaim e l).transports t n

/-! ## §3 The flat log fails the same test -/

/-- **No projection claim is available for the flat log.**  The payload sequence
does not determine the lane assignment, so it is not a coarsening of the
lane-indexed record at all — the first obligation of a projection claim already
fails. -/
theorem flat_log_is_not_a_projection_of_the_lane_state :
    ¬ DescendsThrough (fun t : Trace Bool ℕ => t.map Event.lane) payloads :=
  payload_pooling_does_not_determine_lane

end Integration.Kernel.Welds.LaneProjectionSquare
