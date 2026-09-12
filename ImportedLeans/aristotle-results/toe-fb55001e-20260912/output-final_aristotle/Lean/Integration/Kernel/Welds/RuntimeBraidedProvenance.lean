import Integration.Kernel.BraidedTrace
import Integration.Kernel.LineageEdge

/-!
# Weld: braided evidence → runtime provenance

`Integration.Kernel.BraidedTrace` owns the braid abstractly (strands, authorities,
crossings) and `Integration.Kernel.EvidenceDependence` owns provenance roots.  The
two sat side by side: nothing forced an actual *runtime trace* — an ordered list
of emitted events — to carry strand-local provenance and authority lanes.

This file supplies that consumer.  A `Trace` is a list of events, each stamped
with a lane and the provenance roots the event rests on.  The lane structure is
then shown to be genuine structure on the trace and not a relabelling of it.

## What is proved

* `laneEvents_idem`, `laneRoots_extract` — **extraction is lane-local**: pulling
  lane `l` out of the trace and recomputing its provenance gives exactly the
  provenance lane `l` had inside the full trace.  This is the property that
  makes a lane a strand rather than a filter applied after the fact.
* `payload_pooling_does_not_determine_lane`,
  `payload_pooling_does_not_determine_authority` — the erased runtime log (the
  payload sequence) does not recover which lane, or whose authority, produced
  each event.  Both are instances of
  `Integration.Kernel.Quotient.not_descendsThrough_of_collision`.
* `laneBraid` — the braid a trace induces, so a trace *is* an object of
  `BraidedTrace`, with `laneBraid_claim` identifying its claims with the
  lane-local root sets.
* **`no_lawful_crossing_of_disjoint_lanes`** — lanes whose provenance differs
  admit no lawful crossing at all: a runtime step cannot silently carry one
  lane's authority onto another's evidence.
* **`pooling_destroys_independence`** — the payoff against a single-lane
  runtime log.  In the two-lane fixture the lanes are `Independent` in the sense
  of `EvidenceDependence`; the pooled one-lane reading of the same events makes
  them share a root, so a flat log reports dependence where the braided trace
  proves independence.
* `flat_event_count_is_not_root_count` — four events, two roots.

**Claim boundary.**  Events, lanes, authorities and roots are finite labels
introduced here; "authority" is a tag on a lane index.  Nothing models an actual
runtime, permission system, log format or knowledge holder.
-/

namespace Integration.Kernel.Welds.RuntimeBraidedProvenance

open Integration.Kernel.Quotient Integration.Kernel.BraidedTrace
open Integration.Kernel.EvidenceDependence

/-! ## §1 Traces with lanes -/

/-- One runtime event: which lane emitted it, what it carried, and the
provenance roots it rests on. -/
structure Event (Lane R : Type) where
  /-- The strand that emitted the event. -/
  lane : Lane
  /-- The payload visible in a flat log. -/
  payload : ℕ
  /-- The provenance roots the event rests on. -/
  roots : Finset R
  deriving DecidableEq

/-- A runtime trace. -/
abbrev Trace (Lane R : Type) := List (Event Lane R)

variable {Lane R : Type} [DecidableEq Lane] [DecidableEq R]

/-- The events of one lane, in order. -/
def laneEvents (t : Trace Lane R) (l : Lane) : Trace Lane R :=
  t.filter (fun e => e.lane == l)

/-- The provenance of a lane: the union of the roots of its events. -/
def laneRoots (t : Trace Lane R) (l : Lane) : Finset R :=
  (laneEvents t l).foldr (fun e acc => e.roots ∪ acc) ∅

/-- The provenance assignment on lanes, in the sense of
`Integration.Kernel.EvidenceDependence`. -/
def laneProvenance (t : Trace Lane R) : Provenance Lane R := ⟨laneRoots t⟩

/-- The flat log: the payload sequence with the lane stamps erased. -/
def payloads (t : Trace Lane R) : List ℕ := t.map Event.payload

/-! ## §2 Extraction is lane-local -/

omit [DecidableEq R] in
/-- Extracting a lane twice is extracting it once. -/
theorem laneEvents_idem (t : Trace Lane R) (l : Lane) :
    laneEvents (laneEvents t l) l = laneEvents t l := by
  simp [laneEvents, List.filter_filter, Bool.and_self]

/-- **Lane-local provenance survives extraction.**  The roots of lane `l`
computed inside the whole trace and the roots of the extracted sub-trace agree,
so a lane can be handed to a consumer without recomputing the braid. -/
theorem laneRoots_extract (t : Trace Lane R) (l : Lane) :
    laneRoots (laneEvents t l) l = laneRoots t l := by
  unfold laneRoots
  rw [laneEvents_idem]

omit [DecidableEq R] in
/-- Every event of an extracted lane really belongs to that lane. -/
theorem mem_laneEvents_iff {t : Trace Lane R} {l : Lane} {e : Event Lane R} :
    e ∈ laneEvents t l ↔ e ∈ t ∧ e.lane = l := by
  simp [laneEvents]

/-! ## §3 The flat log is a quotient of the trace -/

/-- Two traces with the same payload sequence and different lane stamps. -/
def traceA : Trace Bool ℕ := [⟨true, 7, {0}⟩, ⟨false, 9, {1}⟩]

/-- The same payloads, the lanes swapped. -/
def traceB : Trace Bool ℕ := [⟨false, 7, {0}⟩, ⟨true, 9, {1}⟩]

theorem payloads_agree : payloads traceA = payloads traceB := rfl

/-- **The flat log does not recover the lane.** -/
theorem payload_pooling_does_not_determine_lane :
    ¬ DescendsThrough (fun t : Trace Bool ℕ => t.map Event.lane) payloads :=
  not_descendsThrough_of_collision (x := traceA) (y := traceB) payloads_agree (by decide)

/-- **Nor the authority.**  With authority read off the lane, the flat log
cannot say who emitted what. -/
theorem payload_pooling_does_not_determine_authority :
    ¬ DescendsThrough (fun t : Trace Bool ℕ => t.map (fun e => not e.lane)) payloads :=
  not_descendsThrough_of_collision (x := traceA) (y := traceB) payloads_agree (by decide)

/-! ## §4 A trace is a braid -/

/-- The braid carried by a trace: one strand per lane, the strand's claim being
its own provenance, its authority supplied by the deployment. -/
def laneBraid {A : Type} (t : Trace Lane R) (auth : Lane → A) :
    Braid Lane A (Finset R) where
  authority := auth
  claim := laneRoots t

@[simp] theorem laneBraid_claim {A : Type} (t : Trace Lane R) (auth : Lane → A) (l : Lane) :
    (laneBraid t auth).claim l = laneRoots t l := rfl

/-- **Lanes resting on different provenance cannot be crossed lawfully.**  The
invariant taken is the lane's own root set, so a runtime step that would carry
one lane's claim onto another's is not merely unlicensed — no such lawful
crossing exists. -/
theorem no_lawful_crossing_of_disjoint_lanes {A : Type} (t : Trace Lane R) (auth : Lane → A)
    {l l' : Lane} (h : laneRoots t l ≠ laneRoots t l') :
    IsEmpty (LawfulCrossing (laneBraid t auth) id l l') :=
  no_lawful_crossing_of_different_invariant h

/-! ## §5 Two lanes, and the flat reading of them -/

/-- Two lanes, resting on disjoint roots. -/
def twoLaneTrace : Trace Bool ℕ :=
  [⟨true, 1, {0}⟩, ⟨true, 2, {0}⟩, ⟨false, 3, {1}⟩, ⟨false, 4, {1}⟩]

theorem lane_true_roots : laneRoots twoLaneTrace true = {0} := by decide

theorem lane_false_roots : laneRoots twoLaneTrace false = {1} := by decide

/-- Inside the braided trace the two lanes are independent evidence. -/
theorem lanes_are_independent :
    Independent (laneProvenance twoLaneTrace) true false := by
  show Disjoint (laneRoots twoLaneTrace true) (laneRoots twoLaneTrace false)
  rw [lane_true_roots, lane_false_roots]
  exact Finset.disjoint_singleton.2 (by decide)

/-- The same four events, all stamped into a single lane. -/
def pooledTrace : Trace Bool ℕ :=
  [⟨true, 1, {0}⟩, ⟨true, 2, {0}⟩, ⟨true, 3, {1}⟩, ⟨true, 4, {1}⟩]

/-- **A flat log destroys the independence the braid records.**  Collapsing the
lanes makes the very same events share a lane, and the pooled lane is not
independent of itself, while the braided reading proves the two lanes
independent. -/
theorem pooling_destroys_independence :
    Independent (laneProvenance twoLaneTrace) true false ∧
      ¬ Independent (laneProvenance pooledTrace) true true := by
  refine ⟨lanes_are_independent, ?_⟩
  have hne : (laneProvenance pooledTrace).rootsOf true = {0, 1} := by decide
  exact not_independent_self (by rw [hne]; exact ⟨0, by decide⟩)

/-- Four events; two provenance roots. -/
theorem flat_event_count_is_not_root_count :
    twoLaneTrace.length = 4 ∧
      (rootSupport (laneProvenance twoLaneTrace) [true, false]).card = 2 := by decide

end Integration.Kernel.Welds.RuntimeBraidedProvenance
