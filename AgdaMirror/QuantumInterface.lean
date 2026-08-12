import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/QuantumInterface.agda` (genuine interface + witness)

Faithful transcription of the abstract quantum-system interface `QuantumSys`:
a state space `QState`, a unitary-like (invertible) evolution `step`/`inv` with
both inverse laws, an idempotent measurement `meas`, and a general scalar measure
`H` (entropy / action / code length).  These are honest structure fields, never
axioms.  We give a genuine *witness* model on `Unit` (identity evolution and
measurement), so the interface is inhabited.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.QuantumInterface

universe u

/-- Abstract quantum system (Agda `record QuantumSys`). -/
structure QuantumSys where
  QState : Type u
  step : QState → QState
  inv : QState → QState
  left : ∀ s, inv (step s) = s
  right : ∀ s, step (inv s) = s
  meas : QState → QState
  meas_idem : ∀ s, meas (meas s) = meas s
  H : QState → Type u

/-- Genuine witness: the trivial system on `Unit` with identity evolution and
measurement satisfies every law. -/
def trivialSys : QuantumSys where
  QState := PUnit
  step := id
  inv := id
  left := fun _ => rfl
  right := fun _ => rfl
  meas := id
  meas_idem := fun _ => rfl
  H := fun _ => PUnit

end AgdaMirror.QuantumInterface
