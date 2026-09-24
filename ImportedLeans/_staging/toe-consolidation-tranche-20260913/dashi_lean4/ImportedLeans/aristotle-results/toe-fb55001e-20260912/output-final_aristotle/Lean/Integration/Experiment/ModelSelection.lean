import Integration.Experiment.Compiler

/-!
# Data-driven model selection

The compiler of `Integration.Experiment.Compiler` takes the admissible set of
hypotheses as *declared data*: the specification says which candidates the prior
evidence leaves open, and nothing derives that flag from an observation.  This
file closes that gap.

An **instrument model** says which observed readings count as agreeing with a
predicted one; it is the tolerance of the instrument, not a probability
distribution.  Given an observed trace, a hypothesis is **data-admissible** when
it was admissible before *and* its predicted trace agrees with the observation
pointwise.  `refine` rebuilds the specification with that flag, and the compiler
is then run unchanged.

What is proved:

* `refine_shrinks` — refinement never enlarges the admissible set, and hence
  never enlarges the prediction or risk envelopes (`refined_envelope_subset`,
  `refined_risk_envelope_subset`);
* `truth_survives_refinement` and `truth_in_refined_envelope` — **the derived
  set still contains the truth**: if the true hypothesis was admissible and the
  observation agrees with what it predicts, it is data-admissible, so the
  refined envelope still covers the true value.  This is the soundness statement
  the declared-`admissible` version could not make;
* `refinement_is_idempotent_on_its_own_prediction` — re-observing the trace a
  surviving hypothesis predicts removes nothing further;
* `data_cannot_separate_identical_traces` — a *negative*: hypotheses with equal
  predicted traces are data-admissible together or not at all, whatever is
  observed.  No quantity of data from the current instrumentation splits a
  Lane-5 collision; only a new sensor can;
* `coarser_instrument_admits_more` — a *negative* on the tolerance: widening the
  instrument model can only keep more hypotheses alive, so a loose tolerance is
  paid for in envelope width;
* `refutation_is_total` — if the observation agrees with no candidate's
  prediction, the refined admissible set is empty; the model family, not the
  parameters, is what failed.

No probabilistic claim is made: there is no likelihood, no posterior and no
fit.  Agreement is a decidable relation supplied with the instrument, and
selection is exact enumeration over the declared family.
-/

namespace Integration.Experiment.ModelSelection

open Integration.CoordinateSufficiency
open Integration.Experiment.Compiler

/-! ## §1 Instrument models -/

/-- **An instrument model**: the tolerance with which a predicted reading is
compared with an observed one.  `agree p o` says the observation `o` is
compatible with the prediction `p` at the instrument's resolution.  The only
requirement is that an instrument agrees with what it itself would read. -/
structure InstrumentModel (Obs : Type) where
  /-- Compatibility of a predicted reading with an observed one. -/
  agree : Obs → Obs → Bool
  /-- An exact reading is always compatible with itself. -/
  agree_self : ∀ o, agree o o = true

/-- The exact instrument: agreement is equality. -/
def exactInstrument (Obs : Type) [DecidableEq Obs] : InstrumentModel Obs where
  agree a b := decide (a = b)
  agree_self _ := by simp

/-- Pointwise agreement of a predicted trace with an observed one.  Traces of
different lengths never agree: a missing sample is a failed comparison, not a
free pass. -/
def traceAgree {Obs : Type} (m : InstrumentModel Obs) : List Obs → List Obs → Bool
  | [], [] => true
  | a :: as, b :: bs => m.agree a b && traceAgree m as bs
  | [], _ :: _ => false
  | _ :: _, [] => false

variable {Obs : Type}

@[simp] theorem traceAgree_nil_nil (m : InstrumentModel Obs) :
    traceAgree m [] [] = true := rfl

@[simp] theorem traceAgree_cons (m : InstrumentModel Obs) (a b : Obs) (as bs : List Obs) :
    traceAgree m (a :: as) (b :: bs) = (m.agree a b && traceAgree m as bs) := rfl

/-- A trace always agrees with itself. -/
@[simp] theorem traceAgree_self (m : InstrumentModel Obs) (l : List Obs) :
    traceAgree m l l = true := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [m.agree_self a, ih]

/-- Equal predicted traces are indistinguishable to the comparison. -/
theorem traceAgree_congr (m : InstrumentModel Obs) {l₁ l₂ y : List Obs} (h : l₁ = l₂) :
    traceAgree m l₁ y = traceAgree m l₂ y := by rw [h]

/-! ## §2 Data-driven admissibility -/

variable {H State Control : Type}

/-- **Data-admissibility**: admissible before, and predicting what was seen. -/
def dataAdmissible (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) (h : H) : Bool :=
  e.admissible h && traceAgree m (e.traceOf h) y

/-- **The refined specification.**  Only the admissible flag changes; the
dynamics, instrumentation, consumers, hazards, budget and support cone are the
ones the analyst declared.  The compiler is then run unchanged. -/
def refine (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) : ExperimentSpec H State Control Obs :=
  { e with admissible := dataAdmissible e m y }

@[simp] theorem refine_admissible (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (h : H) :
    (refine e m y).admissible h = dataAdmissible e m y h := rfl

@[simp] theorem refine_initialState (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).initialState = e.initialState := rfl

@[simp] theorem refine_dynamics (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).dynamics = e.dynamics := rfl

@[simp] theorem refine_controls (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).controls = e.controls := rfl

@[simp] theorem refine_observe (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).observe = e.observe := rfl

@[simp] theorem refine_hazards (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).hazards = e.hazards := rfl

/-- Refinement does not move any state, so it does not move any prediction:
only the set of hypotheses allowed to contribute changes. -/
@[simp] theorem refine_finalState (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (h : H) :
    (refine e m y).finalState h = e.finalState h := rfl

@[simp] theorem refine_traceOf (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (h : H) :
    (refine e m y).traceOf h = e.traceOf h := rfl

@[simp] theorem refine_riskOf (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (h : H) :
    (refine e m y).riskOf h = e.riskOf h := rfl

/-! ## §3 Refinement shrinks, and keeps the truth -/

/-- **Refinement never enlarges the admissible set.** -/
theorem refine_shrinks (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) : (refine e m y).admissibleSet ⊆ e.admissibleSet := by
  intro h hh
  have : dataAdmissible e m y h = true := hh
  exact (Bool.and_eq_true _ _ |>.mp this).1

/-- **The derived set contains the truth.**  If the true hypothesis was
admissible and the observation is compatible with what it predicts, then the
data-driven selection keeps it.  This is exactly what the declared-`admissible`
version could only assume. -/
theorem truth_survives_refinement (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (h : H) (hprior : e.admissible h = true)
    (hfit : traceAgree m (e.traceOf h) y = true) :
    (refine e m y).admissible h = true := by
  simp [dataAdmissible, hprior, hfit]

/-- In particular, observing exactly what the true hypothesis predicts keeps
it. -/
theorem truth_survives_exact_observation (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (h : H) (hprior : e.admissible h = true) :
    (refine e m (e.traceOf h)).admissible h = true :=
  truth_survives_refinement e m _ h hprior (by simp)

/-- The refined prediction envelope of every consumer is contained in the
unrefined one: **data can only tighten a prediction, never widen it.** -/
theorem refined_envelope_subset (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (c : Consumer State) :
    (fun h => c.quantity ((refine e m y).finalState h)) '' (refine e m y).admissibleSet ⊆
      (fun h => c.quantity (e.finalState h)) '' e.admissibleSet := by
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h, refine_shrinks e m y hh, rfl⟩

/-- The same for the risk envelope. -/
theorem refined_risk_envelope_subset (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) :
    (refine e m y).riskOf '' (refine e m y).admissibleSet ⊆ e.riskOf '' e.admissibleSet := by
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h, refine_shrinks e m y hh, rfl⟩

/-- **Soundness of the refined prediction.**  Under a measurement model, the
refined envelope still covers the true value of every declared quantity. -/
theorem truth_in_refined_envelope (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) (c : Consumer State) (h : H)
    (hprior : e.admissible h = true) (hfit : traceAgree m (e.traceOf h) y = true) :
    c.quantity (e.finalState h) ∈
      (fun h' => c.quantity ((refine e m y).finalState h')) '' (refine e m y).admissibleSet :=
  ⟨h, truth_survives_refinement e m y h hprior hfit, rfl⟩

/-- **Idempotence on a surviving prediction.**  Re-observing the trace that a
surviving hypothesis predicts removes nothing further: refinement by the same
data twice equals refinement once. -/
theorem refinement_is_idempotent_on_its_own_prediction
    (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs) (y : List Obs) (h : H) :
    (refine (refine e m y) m y).admissible h = (refine e m y).admissible h := by
  simp [dataAdmissible]

/-! ## §4 The negatives -/

/-- **Data cannot separate a Lane-5 collision.**  Two hypotheses whose predicted
traces are equal are data-admissible together or not at all, no matter what is
observed and no matter how fine the instrument's tolerance.  Refinement is
therefore not an alternative to the next-measurement recommendation: it is
orthogonal to it. -/
theorem data_cannot_separate_identical_traces (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) {h₁ h₂ : H}
    (htr : e.traceOf h₁ = e.traceOf h₂) (hpr : e.admissible h₁ = e.admissible h₂) :
    (refine e m y).admissible h₁ = (refine e m y).admissible h₂ := by
  simp [dataAdmissible, hpr, traceAgree_congr m htr]

/-- **A coarser instrument admits more.**  If everything `m₁` accepts `m₂` also
accepts, then every hypothesis surviving selection under `m₁` survives under
`m₂`; a loose tolerance is paid for in envelope width. -/
theorem coarser_instrument_admits_more (e : ExperimentSpec H State Control Obs)
    {m₁ m₂ : InstrumentModel Obs}
    (hle : ∀ a b : Obs, m₁.agree a b = true → m₂.agree a b = true) (y : List Obs) :
    (refine e m₁ y).admissibleSet ⊆ (refine e m₂ y).admissibleSet := by
  have key : ∀ l₁ l₂ : List Obs, traceAgree m₁ l₁ l₂ = true → traceAgree m₂ l₁ l₂ = true := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ h; cases l₂ with
      | nil => rfl
      | cons _ _ => exact absurd h (by simp [traceAgree])
    | cons a as ih =>
      intro l₂ h
      cases l₂ with
      | nil => exact absurd h (by simp [traceAgree])
      | cons b bs =>
        rw [traceAgree_cons] at h ⊢
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
        exact Bool.and_eq_true _ _ |>.mpr ⟨hle a b h1, ih bs h2⟩
  intro h hh
  have hh' : dataAdmissible e m₁ y h = true := hh
  obtain ⟨hp, hf⟩ := Bool.and_eq_true _ _ |>.mp hh'
  show dataAdmissible e m₂ y h = true
  exact Bool.and_eq_true _ _ |>.mpr ⟨hp, key _ _ hf⟩

/-- **Total refutation.**  If the observation is compatible with no candidate's
prediction, the refined admissible set is empty.  The compiler then has no
envelope to report, and the failure is at the level of the model family rather
than of any parameter inside it. -/
theorem refutation_is_total (e : ExperimentSpec H State Control Obs) (m : InstrumentModel Obs)
    (y : List Obs) (hno : ∀ h : H, traceAgree m (e.traceOf h) y = false) :
    (refine e m y).admissibleSet = ∅ := by
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  have hh' : dataAdmissible e m y h = true := hh
  have := (Bool.and_eq_true _ _ |>.mp hh').2
  rw [hno h] at this
  exact Bool.noConfusion this

/-- **An unrefuted family is not a confirmed one.**  If two hypotheses predict
the same trace and both were admissible, the refined set is not a singleton even
after an observation that keeps them — unless they were the same hypothesis. -/
theorem surviving_pair_is_not_a_selection (e : ExperimentSpec H State Control Obs)
    (m : InstrumentModel Obs) (y : List Obs) {h₁ h₂ : H} (hne : h₁ ≠ h₂)
    (htr : e.traceOf h₁ = e.traceOf h₂) (hpr : e.admissible h₁ = e.admissible h₂)
    (hsurv : (refine e m y).admissible h₁ = true) :
    ¬ (refine e m y).admissibleSet.Subsingleton := by
  intro hsub
  have h2 : (refine e m y).admissible h₂ = true := by
    rw [← data_cannot_separate_identical_traces e m y htr hpr]
    exact hsurv
  exact hne (hsub hsurv h2)

end Integration.Experiment.ModelSelection
