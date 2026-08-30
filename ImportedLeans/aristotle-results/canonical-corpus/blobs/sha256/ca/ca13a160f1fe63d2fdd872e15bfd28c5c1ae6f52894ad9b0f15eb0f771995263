import Integration.FieldControlledDynamics
import Integration.CoordinateSufficiency

/-!
# State-dependent transducers as field-controlled dynamics

`Agda/DASHI/Biology/StateDependentMultiplexTransducer.agda` defines an
executable record

```
step : Input → State → Modulator → Output × State
```

and proves two separations on a concrete Boolean instance: the same input and
state with different modulators give a different output, and a different
successor state.  `Agda/DASHI/Biology/QuantitativeStateDynamics.agda` strengthens
the second instance with an internal store: one step deposits a pending
magnitude and the next releases it.

`Integration.FieldControlledDynamics.FieldControlled` is the Lean owner of
"a background field selects which transitions are available".  This file
supplies the **adapter** making the transducer an instance of it, with the
modulator as the field, and mirrors the two Agda instances as consumers.

Contents.

* `StatefulTransducer` (as `Transducer`), `runOutput`, `runState` — the mirrored record;
* `toFieldControlled` — the adapter: at a fixed input token, a transducer *is* a
  field-controlled system on its state space, with `Field = Modulator`;
* `effStep_iff`, `field_changes_successor_of_split` — the general theorem: any
  modulator pair the successor map separates gives the owner's separation;
* `canonicalBoolTransducer` and the four mirrored Agda facts;
* `canonical_field_separation` — the adapter applied to it;
* `canonical_output_all_essential` — the coordinate statement: input, state and
  modulator are each essential for the output, so the output factors through no
  projection forgetting any one of them.  In particular **the input token alone
  does not determine the output**;
* `constant_modulator_fixed`, `flipping_modulator_cycle` — the attractor
  vocabulary of the owner, instantiated: the unmodulated dynamics fixes every
  state, the modulated one is a two-cycle;
* the quantitative instance: `respond`, `quantitativeStep`, the Agda module's
  regime separations, the delayed store/release pair, and
  `pending_is_a_residual` — two states with the same regime and different
  pending value produce different outputs, so the regime alone is not a
  sufficient description of the effective law.

Carriers here are `Bool`, a six-element label type and `ℕ`.  No claim is made
about neurons, dendrites, cells or any physical system; what is proved is that
the corpus's transducer records instantiate the field-control owner.
-/

namespace Integration.StatefulTransducer

open Integration.FieldControlledDynamics
open Integration.CoordinateSufficiency

/-! ## The mirrored record -/

/-- Mirror of the Agda `StatefulTransducer` (as `Transducer`). -/
structure Transducer where
  /-- The input alphabet. -/
  Input : Type
  /-- The internal state. -/
  State : Type
  /-- The modulatory context. -/
  Modulator : Type
  /-- The output alphabet. -/
  Output : Type
  /-- One step: consume an input, a prior state and a modulator; emit an output
  and a successor state. -/
  step : Input → State → Modulator → Output × State

/-- Mirror of the Agda `runOutput`. -/
def runOutput (T : Transducer) (i : T.Input) (s : T.State) (m : T.Modulator) :
    T.Output := (T.step i s m).1

/-- Mirror of the Agda `runState`. -/
def runState (T : Transducer) (i : T.Input) (s : T.State) (m : T.Modulator) :
    T.State := (T.step i s m).2

/-! ## The adapter -/

/-- **The adapter.**  At a fixed input token a stateful transducer is a
field-controlled system on its own state space, the modulator playing the role
of the background field.  The structural edge relation is "some modulator makes
this a successor"; the effective one fixes the modulator. -/
def toFieldControlled (T : Transducer) (i : T.Input) :
    FieldControlled T.Modulator T.State where
  structEdge := fun s s' => ∃ m, runState T i s m = s'
  effStep := fun m s s' => runState T i s m = s'
  effStep_le := fun m _ _ h => ⟨m, h⟩

@[simp] theorem effStep_iff (T : Transducer) (i : T.Input) (m : T.Modulator)
    (s s' : T.State) : (toFieldControlled T i).effStep m s s' ↔ runState T i s m = s' :=
  Iff.rfl

/-- **The general separation.**  Any modulator pair whose successor states
differ realises the owner's "same state, different field, different successor"
pattern. -/
theorem field_changes_successor_of_split (T : Transducer) (i : T.Input)
    (s : T.State) (m m' : T.Modulator) (h : runState T i s m ≠ runState T i s m') :
    (toFieldControlled T i).effStep m s (runState T i s m) ∧
      ¬ (toFieldControlled T i).effStep m' s (runState T i s m) :=
  ⟨rfl, fun hc => h (by rw [← hc])⟩

/-- And the structural edge does not see the difference: both successors are
structural edges of the same state. -/
theorem structEdge_blind (T : Transducer) (i : T.Input) (s : T.State)
    (m m' : T.Modulator) :
    (toFieldControlled T i).structEdge s (runState T i s m) ∧
      (toFieldControlled T i).structEdge s (runState T i s m') :=
  ⟨⟨m, rfl⟩, ⟨m', rfl⟩⟩

/-! ## The Boolean instance -/

/-- Mirror of the Agda `canonicalBoolTransducer`: output is the parity of input,
state and modulator; the successor state is the parity of state and modulator. -/
def canonicalBoolTransducer : Transducer where
  Input := Bool
  State := Bool
  Modulator := Bool
  Output := Bool
  step := fun x s m => (Bool.xor (Bool.xor x s) m, Bool.xor s m)

theorem canonical_state_changes_output :
    runOutput canonicalBoolTransducer false false false ≠
      runOutput canonicalBoolTransducer false true false :=
  fun h => Bool.noConfusion (show (false : Bool) = true from h)

theorem canonical_modulator_changes_output :
    runOutput canonicalBoolTransducer true false false ≠
      runOutput canonicalBoolTransducer true false true :=
  fun h => Bool.noConfusion (show (true : Bool) = false from h)

theorem canonical_modulator_changes_successor_state :
    runState canonicalBoolTransducer false false true = true := rfl

theorem canonical_unmodulated_state_persists :
    runState canonicalBoolTransducer true true false = true := rfl

/-- **The adapter applied.**  With the modulator as background field, the
canonical transducer exhibits the owner's separation. -/
theorem canonical_field_separation :
    (toFieldControlled canonicalBoolTransducer false).effStep true false true ∧
      ¬ (toFieldControlled canonicalBoolTransducer false).effStep false false true := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Bool.noConfusion (show (false : Bool) = true from h)

/-- The output read as a consumer of the three-coordinate product
`(input, state, modulator)`. -/
def canonicalOutput (x : Fin 3 → Bool) : Bool :=
  runOutput canonicalBoolTransducer (x 0) (x 1) (x 2)

/-- **Every coordinate is essential for the output.**  In particular the input
token alone does not determine the output: the consumer factors through no
projection that forgets the state or the modulator.  This is the corpus
module's informal point, discharged by the generic coordinate theorem. -/
theorem canonical_output_all_essential :
    Essential (A := fun _ : Fin 3 => Bool) 0 canonicalOutput ∧
      Essential (A := fun _ : Fin 3 => Bool) 1 canonicalOutput ∧
      Essential (A := fun _ : Fin 3 => Bool) 2 canonicalOutput := by
  refine ⟨⟨![false, false, false], ![true, false, false], ?_, by decide⟩,
    ⟨![false, false, false], ![false, true, false], ?_, by decide⟩,
    ⟨![false, false, false], ![false, false, true], ?_, by decide⟩⟩ <;>
  · intro i hi
    fin_cases i <;> simp_all

/-- Hence the output does not factor through the input alone. -/
theorem canonical_output_not_input_only :
    ¬ FactorsOn (A := fun _ : Fin 3 => Bool) {0} canonicalOutput := by
  intro h
  exact absurd (essential_mem_of_factorsOn h canonical_output_all_essential.2.1)
    (by decide)

/-! ### The attractor vocabulary, at fixed modulators -/

/-- The successor map at modulator `m`. -/
def canonicalSucc (m : Bool) (s : Bool) : Bool := Bool.xor s m

/-- The unmodulated dynamics fixes every state. -/
theorem constant_modulator_fixed (s : Bool) : Fixed (canonicalSucc false) s := by
  cases s <;> rfl

/-- The modulated dynamics has no fixed point and is a two-cycle. -/
theorem flipping_modulator_cycle :
    (∀ s, ¬ Fixed (canonicalSucc true) s) ∧ Cycle (canonicalSucc true) false 2 := by
  refine ⟨fun s => ?_, ⟨by norm_num, by decide⟩⟩
  cases s <;> simp [Fixed, canonicalSucc]

/-- The two together: the *same* carrier has qualitatively different attractor
structure at the two field values. -/
theorem attractor_class_depends_on_field :
    Fixed (canonicalSucc false) false ∧ ¬ Fixed (canonicalSucc true) false :=
  ⟨constant_modulator_fixed false, flipping_modulator_cycle.1 false⟩

/-! ## The quantitative instance, with memory -/

/-- Mirror of the Agda `CellularRegime`. -/
inductive Regime
  | amplified | attenuated | shunted | delayed | inverted | ineffective
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `QuantitativeResponse`. -/
structure Response where
  /-- The magnitude of the response. -/
  magnitude : ℕ
  /-- Its polarity. -/
  polarity : Bool
  /-- Whether it is deferred. -/
  delayed : Bool
  deriving DecidableEq, Repr

/-- Mirror of the Agda `respond`. -/
def respond : Bool → Regime → Response
  | false, _ => ⟨0, false, false⟩
  | true, .amplified => ⟨3, true, false⟩
  | true, .attenuated => ⟨1, true, false⟩
  | true, .shunted => ⟨0, true, false⟩
  | true, .delayed => ⟨0, true, true⟩
  | true, .inverted => ⟨1, false, false⟩
  | true, .ineffective => ⟨0, false, false⟩

/-- The Agda module's regime separations, at one fixed input. -/
theorem respond_separations :
    (respond true .amplified).magnitude = 3 ∧
      (respond true .attenuated).magnitude = 1 ∧
      (respond true .shunted).magnitude = 0 ∧
      (respond true .delayed).delayed = true ∧
      (respond true .inverted).polarity = false ∧
      respond true .amplified ≠ respond true .attenuated ∧
      respond true .attenuated ≠ respond true .inverted ∧
      respond true .shunted ≠ respond true .delayed := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide⟩

/-- **The response is not a function of the input.**  One input token, several
responses. -/
theorem respond_not_determined_by_input :
    ¬ Determines (fun p : Bool × Regime => p.1) (fun p : Bool × Regime => respond p.1 p.2) :=
  not_determines_of_collision (x₁ := (true, .amplified)) (x₂ := (true, .attenuated))
    rfl (by decide)

/-- Mirror of the Agda `QuantitativeCellState`: a regime together with a stored
pending magnitude. -/
structure CellState where
  /-- The current regime. -/
  regime : Regime
  /-- The magnitude held over from the previous step. -/
  pending : ℕ
  deriving DecidableEq, Repr

/-- Mirror of the Agda `quantitativeStep`.  In the delayed regime the emitted
magnitude is the stored one and the current response is deposited instead. -/
def quantitativeStep (input : Bool) (c : CellState) : Response × CellState :=
  match c.regime with
  | .delayed => (⟨c.pending, true, false⟩, ⟨.delayed, (respond input .delayed).magnitude + 1⟩)
  | r => (respond input r, ⟨r, 0⟩)

/-- Mirror of the Agda `initialDelayedCell`. -/
def initialDelayedCell : CellState := ⟨.delayed, 0⟩

/-- **Store then release**, exactly as in the Agda module. -/
theorem delayed_store_then_release :
    (quantitativeStep true initialDelayedCell).1.magnitude = 0 ∧
      (quantitativeStep true initialDelayedCell).2.pending = 1 ∧
      (quantitativeStep false (quantitativeStep true initialDelayedCell).2).1.magnitude = 1 := by
  refine ⟨rfl, rfl, rfl⟩

/-- **The pending magnitude is a genuine residual.**  Two cell states with the
same regime and different stored magnitude are separated by the very next
output, so the regime — the visible label — is not a sufficient description of
the effective law. -/
theorem pending_is_a_residual :
    ¬ Determines (fun c : CellState => c.regime) (fun c => (quantitativeStep true c).1) :=
  not_determines_of_collision (x₁ := ⟨.delayed, 0⟩) (x₂ := ⟨.delayed, 1⟩) rfl (by decide)

/-- The quantitative transducer, mirroring the Agda bridge: the modulator is the
regime, which is installed into the state before stepping. -/
def quantitativeTransducer : Transducer where
  Input := Bool
  State := CellState
  Modulator := Regime
  Output := Response
  step := fun input state modulation => quantitativeStep input ⟨modulation, state.pending⟩

theorem quantitative_amplifies :
    (runOutput quantitativeTransducer true ⟨.ineffective, 0⟩ .amplified).magnitude = 3 := rfl

theorem quantitative_inverts :
    (runOutput quantitativeTransducer true ⟨.amplified, 0⟩ .inverted).polarity = false := rfl

/-- **The quantitative transducer is a field-controlled system too**, and the
regime separates successor states: after a step in the delayed regime the store
is non-empty, and after a step in any immediate regime it is empty. -/
theorem quantitative_field_separation :
    (toFieldControlled quantitativeTransducer true).effStep .delayed ⟨.ineffective, 0⟩
        ⟨.delayed, 1⟩ ∧
      ¬ (toFieldControlled quantitativeTransducer true).effStep .amplified
        ⟨.ineffective, 0⟩ ⟨.delayed, 1⟩ := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (congrArg CellState.regime
    (show (⟨.amplified, 0⟩ : CellState) = ⟨.delayed, 1⟩ from h)) (by decide)

end Integration.StatefulTransducer
