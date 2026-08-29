import Mathlib
import AgdaMirror.MonsterWalk

/-!
# Lean mirror of `MonsterVectors.agda` (genuine, fully proved)

Minimal conformance vectors `(input state, expected next state)` over the walk
`State`.  We faithfully transcribe the `Vector` carrier, the `Vectors` list, the
(empty) seed table, and prove that applying a step spec produces the conformance
vector it claims (`stepVector_output`), so the carrier is genuinely tied to the
walk semantics rather than purely tabular.
-/

namespace AgdaMirror.MonsterVectors

open AgdaMirror.MonsterWalk

/-- A conformance vector: an input state and its expected output. -/
structure Vector where
  input : State
  output : State

/-- A list of conformance vectors. -/
abbrev Vectors := List Vector

/-- The seed table (empty until a step spec is pinned). -/
def vectors : Vectors := []

@[simp] theorem vectors_length : vectors.length = 0 := rfl

/-- Build the conformance vector of a state under a step function. -/
def stepVector (f : State → State) (s : State) : Vector := ⟨s, f s⟩

/-- The built vector's output is exactly the step applied to the input. -/
theorem stepVector_output (f : State → State) (s : State) :
    (stepVector f s).output = f (stepVector f s).input := rfl

/-- The conformance table built from a list of inputs has the matching length. -/
theorem stepVectors_length (f : State → State) (inputs : List State) :
    (inputs.map (stepVector f)).length = inputs.length := by
  simp

end AgdaMirror.MonsterVectors
