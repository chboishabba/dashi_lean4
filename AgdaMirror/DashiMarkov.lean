import Mathlib

/-!
# Lean mirror of `DASHI/Core/DashiMarkov.agda` (genuine interface + witness)

Faithful transcription of the "DASHI Markov" core:

* `JoinedState` — the typed joined task slice,
* `Transition State Input` — the structural update law `step`,
* `Sufficiency` — a history summary that factors through the current state
  (`summarize (append h x) = step (summarize h) x`),
* `DASHIMarkov` — the bundle, and the compatibility kernel
  `MarkovCompatibility` whose realizations agree with the deterministic step.

We give genuine *witnesses*: taking `History = State` with `summarize = id` and
`append = step` gives a real `Sufficiency`, hence a real `DASHIMarkov`; and the
deterministic kernel realizes the step.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.DashiMarkov

/-- The typed joined task slice (Agda `record JoinedState`). -/
structure JoinedState (Carrier Residual Obligation Authority Boundary : Type) where
  carrier : Carrier
  residual : Residual
  obligations : Obligation
  authorities : Authority
  boundary : Boundary

/-- The structural update law (Agda `record Transition`). -/
structure Transition (State Input : Type) where
  step : State → Input → State

/-- A history summary that factors through the current state (Agda
`record Sufficiency`). -/
structure Sufficiency (State Input History : Type) (transition : Transition State Input) where
  summarize : History → State
  append : History → Input → History
  sufficient : ∀ (h : History) (x : Input),
    summarize (append h x) = transition.step (summarize h) x

/-- The DASHI–Markov bundle (Agda `record DASHIMarkov`). -/
structure DASHIMarkov (State Input History : Type) where
  transition : Transition State Input
  sufficiency : Sufficiency State Input History transition

/-- A relation-valued compatibility kernel (Agda `record MarkovCompatibility`). -/
structure MarkovCompatibility (State Input Observation : Type)
    (transition : Transition State Input) where
  kernel : State → Input → State → Prop
  emit : State → Observation → Prop
  realizes : ∀ (s : State) (x : Input) (s' : State),
    kernel s x s' → s' = transition.step s x

/-- Genuine witness: with `History = State`, the identity summary is sufficient. -/
def idSufficiency {State Input : Type} (transition : Transition State Input) :
    Sufficiency State Input State transition where
  summarize := id
  append := transition.step
  sufficient := fun _ _ => rfl

/-- Genuine witness: any transition yields a DASHI–Markov bundle over its own
state history. -/
def idDASHIMarkov {State Input : Type} (transition : Transition State Input) :
    DASHIMarkov State Input State where
  transition := transition
  sufficiency := idSufficiency transition

/-- Genuine witness: the deterministic kernel realizes the step. -/
def deterministicCompatibility {State Input Observation : Type}
    (transition : Transition State Input) (e : State → Observation → Prop) :
    MarkovCompatibility State Input Observation transition where
  kernel := fun s x s' => s' = transition.step s x
  emit := e
  realizes := fun _ _ _ h => h

end AgdaMirror.DashiMarkov
