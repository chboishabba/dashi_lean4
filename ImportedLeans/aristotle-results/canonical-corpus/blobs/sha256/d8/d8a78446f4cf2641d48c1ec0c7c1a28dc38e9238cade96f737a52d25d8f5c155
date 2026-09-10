import Integration.Kernel.Probe
import Integration.Experiment.ModelSelection

/-!
# The model-selection lane is a thin instance of the kernel

`Integration.Experiment.ModelSelection` derives the admissible-hypothesis flag
from data: a hypothesis survives when it was admissible before and its predicted
trace agrees with the observed one, at the instrument's tolerance.  This file
identifies that operation with the kernel's backward refinement.

The dictionary:

* the residual fibre is `e.admissibleSet`, the hypotheses the evidence leaves
  open;
* the observed trace `y` is a kernel event `agreeEvent e m y`;
* **`refined_admissibleSet_eq_refineBy`** — the refined admissible set *is*
  `refineBy` applied to the prior fibre and that event;
* **`refineAll_observations`** — a sequence of observations is the kernel's
  iterated refinement;
* **`exact_agreeEvent_eq_event`** — for the *exact* instrument the event is
  literally `event (traceChannel e) y`, the kernel channel event of the trace
  channel.  Instrument tolerance is exactly the gap between a channel event and
  a general event.

The lane's theorems become kernel instances:

* `refined_refines_prior` (`refineBy_refines`);
* `truth_survives_kernel`;
* `identical_traces_are_a_persistent_collision` — the lane's
  `data_cannot_separate_identical_traces` in kernel form: hypotheses agreeing on
  the trace channel are never separated by refining on that channel, whatever is
  observed;
* `coarser_instrument_refines_less` — a looser tolerance yields a larger residual
  fibre, so tolerance is paid for in fibre width;
* `refutation_empties_the_fibre` — an observation no candidate predicts empties
  the fibre; by `determines_empty` the consumer question is then closed
  *vacuously*, which is refutation of the family, not identification inside it.
-/

namespace Integration.Kernel.Instances.ModelSelectionBridge

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Probe
open Integration.Experiment.Compiler Integration.Experiment.ModelSelection

variable {H State Control Obs : Type}

/-- The lane's data-driven refinement of a specification, under an
unambiguous name (`refine` is also a kernel operation and a tactic). -/
abbrev dataRefine (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) : ExperimentSpec H State Control Obs :=
  Integration.Experiment.ModelSelection.refine e m y

/-! ## §1 The trace channel and the observation event -/

/-- The channel that reads off the trace a hypothesis predicts. -/
def traceChannel (e : ExperimentSpec H State Control Obs) : Channel H (List Obs) :=
  ⟨e.traceOf⟩

/-- The event of observing `y` through an instrument of tolerance `m`. -/
def agreeEvent (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) : Set H :=
  {h | traceAgree m (e.traceOf h) y = true}

@[simp] theorem mem_agreeEvent {e : ExperimentSpec H State Control Obs}
    {m : InstrumentModel Obs} {y : List Obs} {h : H} :
    h ∈ agreeEvent e m y ↔ traceAgree m (e.traceOf h) y = true := Iff.rfl

theorem traceAgree_exact_iff [DecidableEq Obs] (l₁ l₂ : List Obs) :
    traceAgree (exactInstrument Obs) l₁ l₂ = true ↔ l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [traceAgree]
  | cons a as ih =>
      cases l₂ with
      | nil => simp [traceAgree]
      | cons b bs =>
          simp only [traceAgree_cons, exactInstrument, Bool.and_eq_true, decide_eq_true_eq,
            List.cons.injEq]
          exact and_congr_right fun _ => ih bs

/-- **An exact instrument gives exactly a kernel channel event.**  Tolerance is
the whole difference between a channel event and a general event. -/
theorem exact_agreeEvent_eq_event [DecidableEq Obs] (e : ExperimentSpec H State Control Obs)
    (y : List Obs) :
    agreeEvent e (exactInstrument Obs) y = event (traceChannel e) y := by
  ext h
  simp only [mem_agreeEvent, traceAgree_exact_iff, mem_event, traceChannel]

/-! ## §2 The identification -/

/-- **Data-driven refinement is kernel refinement.** -/
theorem refined_admissibleSet_eq_refineBy (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (dataRefine e m y).admissibleSet = refineBy e.admissibleSet (agreeEvent e m y) := by
  ext h
  simp only [ExperimentSpec.admissibleSet, mem_setOf_eq, refine_admissible, dataAdmissible,
    Bool.and_eq_true, refineBy, mem_inter_iff, mem_agreeEvent]

theorem refineAll_agreeEvents (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (P : Set H) (ys : List (List Obs)) :
    refineAll P (ys.map (agreeEvent e m)) =
      {h | h ∈ P ∧ ∀ y ∈ ys, traceAgree m (e.traceOf h) y = true} := by
  induction ys generalizing P with
  | nil => ext h; simp
  | cons y ys ih =>
      ext h
      simp only [List.map_cons, refineAll_cons, ih, mem_setOf_eq, refineBy, mem_inter_iff,
        mem_agreeEvent, List.mem_cons]
      constructor
      · rintro ⟨⟨hP, hy⟩, hys⟩
        exact ⟨hP, by rintro y' (rfl | hy') ; exacts [hy, hys y' hy']⟩
      · rintro ⟨hP, hall⟩
        exact ⟨⟨hP, hall y (Or.inl rfl)⟩, fun y' hy' => hall y' (Or.inr hy')⟩

/-- **A sequence of observations is the kernel's iterated refinement.** -/
theorem refineAll_observations (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (ys : List (List Obs)) :
    refineAll e.admissibleSet (ys.map (agreeEvent e m)) =
      {h | e.admissible h = true ∧ ∀ y ∈ ys, traceAgree m (e.traceOf h) y = true} := by
  rw [refineAll_agreeEvents]
  rfl

/-! ## §3 The lane's theorems, as kernel instances -/

theorem refined_refines_prior (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    Refines (dataRefine e m y).admissibleSet e.admissibleSet := by
  rw [refined_admissibleSet_eq_refineBy]
  exact refineBy_refines _ _

theorem truth_survives_kernel (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) {h : H} (hprior : h ∈ e.admissibleSet)
    (hfit : h ∈ agreeEvent e m y) :
    h ∈ (dataRefine e m y).admissibleSet := by
  rw [refined_admissibleSet_eq_refineBy]
  exact ⟨hprior, hfit⟩

/-- **Hypotheses with the same predicted trace are a persistent collision.**
If a consumer question separates two hypotheses that the trace channel cannot
tell apart, no amount of data through that channel closes it: the collision
survives every refinement.  The lane's `data_cannot_separate_identical_traces`
in kernel form. -/
theorem identical_traces_are_a_persistent_collision {C : Type*}
    (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs) (c : H → C)
    {h₁ h₂ : H} (hprior₁ : h₁ ∈ e.admissibleSet) (hprior₂ : h₂ ∈ e.admissibleSet)
    (htr : e.traceOf h₁ = e.traceOf h₂) (hc : c h₁ ≠ c h₂) (y : List Obs)
    (hy : h₁ ∈ agreeEvent e m y) :
    Collision (dataRefine e m y).admissibleSet c := by
  have h₂mem : h₂ ∈ agreeEvent e m y := by
    rw [mem_agreeEvent, ← htr]
    exact hy
  exact ⟨h₁, truth_survives_kernel e m y hprior₁ hy, h₂,
    truth_survives_kernel e m y hprior₂ h₂mem, hc⟩

/-- **A coarser instrument refines less.** -/
theorem coarser_instrument_refines_less (e : ExperimentSpec H State Control Obs)
    {m₁ m₂ : InstrumentModel Obs}
    (hle : ∀ a b : Obs, m₁.agree a b = true → m₂.agree a b = true) (y : List Obs) :
    Refines (refineBy e.admissibleSet (agreeEvent e m₁ y))
      (refineBy e.admissibleSet (agreeEvent e m₂ y)) := by
  have e₁ := refined_admissibleSet_eq_refineBy e m₁ y
  have e₂ := refined_admissibleSet_eq_refineBy e m₂ y
  rw [← e₁, ← e₂]
  exact coarser_instrument_admits_more e hle y

/-- **Refutation closes the consumer question vacuously.**  If nothing predicts
the observation the fibre is empty, and `determines_empty` then reports every
consumer as settled — an empty fibre is refutation of the family, never
identification inside it. -/
theorem refutation_empties_the_fibre {C : Type*} [Nonempty C]
    (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs) (y : List Obs)
    (hno : ∀ h : H, traceAgree m (e.traceOf h) y = false) (c : H → C) :
    refineBy e.admissibleSet (agreeEvent e m y) = ∅ ∧
      Determines (refineBy e.admissibleSet (agreeEvent e m y)) c := by
  have hempty : refineBy e.admissibleSet (agreeEvent e m y) = ∅ := by
    have h := refined_admissibleSet_eq_refineBy e m y
    rw [← h]
    exact refutation_is_total e m y hno
  exact ⟨hempty, hempty ▸ determines_empty c⟩

end Integration.Kernel.Instances.ModelSelectionBridge
