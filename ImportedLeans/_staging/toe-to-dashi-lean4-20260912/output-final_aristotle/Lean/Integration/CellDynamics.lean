import Integration.FieldControlledDynamics
import Integration.CoordinateSufficiency

/-!
# The cell/bioelectric lane as a consumer of the field-control and attractor owners

Three corpus modules are read here.

`Agda/DASHI/Biology/Cell/BioelectricNetwork.agda` declares a network state with
an update

```
update : Environment → ChemicalSignal → MechanicalState → RegulatoryState →
         NetworkState → NetworkState
```

which is the shape `x_{t+1} = F(x_t, φ_t)` owned by
`Integration.FieldControlledDynamics.FieldControlled`, together with a
`BioelectricPatternProjection` giving an observation layer on top.

`Agda/DASHI/Biology/Cell/CellStateAttractor.agda` declares `InBasin`,
`StableIn` and a `forwardInvariant` *field* — an obligation the record demands
of whoever inhabits it.  Here that obligation is discharged as a theorem for
basins of fixed points, and the record's own boundary
(`attractorIsNotSemanticIdentityByDefinition`, declared there as an
uninterpreted `Set`) is proved as a statement.

`Agda/DASHI/Biology/Morphogenesis/ReactionDiffusionModeSelection.agda` is
included as a deliberate negative: all of its conditions are uninterpreted
`Set`-valued fields, so its witness record is inhabited by trivial data and
constrains nothing.  That is recorded here, not papered over.

Contents.

* `BioelectricNetwork`, `toFieldControlled` — the adapter, with the four control
  channels as the background field;
* `xorNetwork`, `chemical_modulation_changes_update` — the corpus's own Boolean
  instance and its separation;
* `update_all_coordinates_essential` — each of the five arguments of the update
  is essential, so the update factors through no projection forgetting one;
* `patternNetwork`, `pattern_no_effective_law` — the pattern projection has
  **no** effective dynamics: two states with the same pattern are driven to
  states with different patterns;
* `CellSystem`, `basin_forward_invariant` — the Agda `forwardInvariant`
  obligation, proved;
* `cellStep`, `attractor_depends_on_environment`, `attractor_not_identity` — a
  four-state instance: which attractor a state belongs to depends on the
  environment, and the attractor class does not determine the state;
* `ModeSelectionWitness`, `modeSelection_trivially_inhabited` — the
  reaction–diffusion record constrains nothing.

Carriers are `Bool`, `Bool × Bool` and `Fin 4`.  Nothing here is a claim about
cells, voltages, morphogenesis or pattern formation.
-/

namespace Integration.CellDynamics

open Integration.FieldControlledDynamics
open Integration.CoordinateSufficiency

/-! ## Bioelectric networks as field-controlled dynamics -/

/-- Mirror of the Agda `BioelectricNetwork`, restricted to the fields that carry
executable content: a state space, four control channels, and the update. -/
structure BioelectricNetwork where
  /-- The network state. -/
  NetworkState : Type
  /-- The environment channel. -/
  Environment : Type
  /-- The chemical channel. -/
  ChemicalSignal : Type
  /-- The mechanical channel. -/
  MechanicalState : Type
  /-- The regulatory channel. -/
  RegulatoryState : Type
  /-- The coupled update. -/
  update : Environment → ChemicalSignal → MechanicalState → RegulatoryState →
    NetworkState → NetworkState

/-- The four control channels, bundled as the background field. -/
abbrev BioelectricNetwork.Control (B : BioelectricNetwork) : Type :=
  B.Environment × B.ChemicalSignal × B.MechanicalState × B.RegulatoryState

/-- The update at a given control setting. -/
def BioelectricNetwork.stepAt (B : BioelectricNetwork) (f : B.Control) :
    B.NetworkState → B.NetworkState :=
  B.update f.1 f.2.1 f.2.2.1 f.2.2.2

/-- **The adapter.**  A bioelectric network is a field-controlled system whose
background field is the tuple of control channels. -/
def BioelectricNetwork.toFieldControlled (B : BioelectricNetwork) :
    FieldControlled B.Control B.NetworkState where
  structEdge := fun s s' => ∃ f, B.stepAt f s = s'
  effStep := fun f s s' => B.stepAt f s = s'
  effStep_le := fun f _ _ h => ⟨f, h⟩

/-- Mirror of the corpus's own Boolean bioelectric instance: the update is the
parity of the four controls and the state. -/
def xorNetwork : BioelectricNetwork where
  NetworkState := Bool
  Environment := Bool
  ChemicalSignal := Bool
  MechanicalState := Bool
  RegulatoryState := Bool
  update := fun e c m r s => Bool.xor e (Bool.xor c (Bool.xor m (Bool.xor r s)))

/-- Mirror of the Agda `canonicalBioelectricChemicalModulation`: the chemical
channel alone changes the update. -/
theorem chemical_modulation_changes_update :
    xorNetwork.update false false false false false ≠
      xorNetwork.update false true false false false :=
  fun h => Bool.noConfusion (show (false : Bool) = true from h)

/-- The update read as a consumer of the five-coordinate product
`(environment, chemical, mechanical, regulatory, state)`. -/
def updateOfCoords (x : Fin 5 → Bool) : Bool :=
  xorNetwork.update (x 0) (x 1) (x 2) (x 3) (x 4)

/-- **Every channel is essential.**  The successor state factors through no
projection that forgets any one of the four controls or the current state: the
coupled system is not a function of any proper subset of its inputs. -/
theorem update_all_coordinates_essential (j : Fin 5) :
    Essential (A := fun _ : Fin 5 => Bool) j updateOfCoords := by
  refine ⟨fun _ => false, Function.update (fun _ => false) j true, ?_, ?_⟩
  · intro i hi
    simp [Function.update_of_ne hi]
  · fin_cases j <;> simp [updateOfCoords, xorNetwork, Function.update]

/-- Hence the update does not factor through the state alone: the field is not
removable. -/
theorem update_not_state_only :
    ¬ FactorsOn (A := fun _ : Fin 5 => Bool) {4} updateOfCoords := by
  intro h
  exact absurd (essential_mem_of_factorsOn h (update_all_coordinates_essential 0)) (by decide)

/-! ### The pattern projection has no effective dynamics -/

/-- A two-node network whose two nodes are driven by different channels. -/
def patternNetwork : BioelectricNetwork where
  NetworkState := Bool × Bool
  Environment := Unit
  ChemicalSignal := Bool
  MechanicalState := Bool
  RegulatoryState := Unit
  update := fun _ c m _ s => (Bool.xor s.1 c, Bool.xor s.2 m)

/-- Mirror of `observePattern`: the pattern is "some node is active". -/
def observePattern (s : Bool × Bool) : Bool := s.1 || s.2

/-- The control setting used below: chemical on, mechanical off. -/
def chemOn : patternNetwork.Control := ((), true, false, ())

/-- **The pattern layer has no effective law.**  Two states with the same
observed pattern are driven by the same control to states with different
patterns, so no dynamics on patterns reproduces the network dynamics. -/
theorem pattern_no_effective_law :
    ¬ ∃ F : Bool → Bool, ∀ s : Bool × Bool,
        observePattern (patternNetwork.stepAt chemOn s) = F (observePattern s) := by
  rintro ⟨F, hF⟩
  have h1 : (false : Bool) = F true := hF (true, false)
  have h2 : (true : Bool) = F true := hF (false, true)
  exact absurd (h1.trans h2.symm) (by decide)

/-- The collision that causes it, stated on its own. -/
theorem pattern_collision :
    observePattern (true, false) = observePattern (false, true) ∧
      (true, false) ≠ ((false, true) : Bool × Bool) := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (congrArg Prod.fst h) (by decide)

/-! ## Cell states, basins and attractors -/

/-- Mirror of the executable content of the Agda `CoupledCellState` together
with its phenotype quotient. -/
structure CellSystem where
  /-- The environment. -/
  Environment : Type
  /-- The cell state. -/
  CellState : Type
  /-- The phenotype. -/
  Phenotype : Type
  /-- The cell type. -/
  CellType : Type
  /-- The environment-controlled dynamics. -/
  step : Environment → CellState → CellState
  /-- The phenotype projection. -/
  phenotype : CellState → Phenotype
  /-- The classification of phenotypes. -/
  classify : Phenotype → CellType

/-- A cell system is a field-controlled system with the environment as field. -/
def CellSystem.toFieldControlled (C : CellSystem) :
    FieldControlled C.Environment C.CellState where
  structEdge := fun s s' => ∃ e, C.step e s = s'
  effStep := fun e s s' => C.step e s = s'
  effStep_le := fun e _ _ h => ⟨e, h⟩

/-- **The Agda `forwardInvariant` field, discharged.**  The basin of a fixed
point of the dynamics at a given environment is forward invariant for that
environment.  In the Agda record this is an obligation on the inhabitant; here
it is a theorem about the owner's `Basin`. -/
theorem basin_forward_invariant (C : CellSystem) (e : C.Environment) {a : C.CellState}
    (hfix : Fixed (C.step e) a) {x : C.CellState} (hx : x ∈ Basin (C.step e) a) :
    C.step e x ∈ Basin (C.step e) a :=
  basin_step_of_fixed hfix hx

/-! ### A four-state instance -/

/-- The dynamics: at environment `false` there are two fixed points, `0` and
`2`; at environment `true` everything is driven to `3`. -/
def cellStep : Bool → Fin 4 → Fin 4
  | false, 0 => 0
  | false, 1 => 0
  | false, 2 => 2
  | false, 3 => 2
  | true, 0 => 1
  | true, 1 => 2
  | true, _ => 3

/-- Two distinct fixed points at environment `false`. -/
theorem cell_two_attractors : Fixed (cellStep false) 0 ∧ Fixed (cellStep false) 2 :=
  ⟨rfl, rfl⟩

/-- Their basins each contain a second state. -/
theorem cell_basins : (1 : Fin 4) ∈ Basin (cellStep false) 0 ∧
    (3 : Fin 4) ∈ Basin (cellStep false) 2 :=
  ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩

/-- **The attractor structure depends on the environment.**  The same state is a
fixed point at one environment and not at the other; this is the owner's
field-control separation, on the cell carrier. -/
theorem attractor_depends_on_environment :
    Fixed (cellStep false) 0 ∧ ¬ Fixed (cellStep true) 0 := by
  refine ⟨rfl, fun h => ?_⟩
  exact absurd (congrArg (fun z : Fin 4 => z.val) h) (by decide)

/-- The phenotype projection: the two states of each basin share a phenotype. -/
def cellPhenotype : Fin 4 → Bool
  | 0 => true
  | 1 => true
  | _ => false

/-- **The attractor class is not a semantic identity.**  Two distinct states lie
in the same basin and carry the same phenotype, so neither the attractor nor the
phenotype determines the state.  The Agda module states this as an
uninterpreted boundary field; here it is a proof. -/
theorem attractor_not_identity :
    ∃ x y : Fin 4, x ≠ y ∧ x ∈ Basin (cellStep false) 0 ∧ y ∈ Basin (cellStep false) 0 ∧
      cellPhenotype x = cellPhenotype y := by
  refine ⟨0, 1, ?_, ⟨0, rfl⟩, ⟨1, rfl⟩, rfl⟩
  intro h
  exact absurd (congrArg (fun z : Fin 4 => z.val) h) (by decide)

/-- And the phenotype is a genuinely lossy consumer: it does not determine which
state one is in. -/
theorem phenotype_not_injective : ¬ Function.Injective cellPhenotype := by
  intro h
  exact absurd (congrArg (fun z : Fin 4 => z.val) (h (show cellPhenotype 0 = cellPhenotype 1 from rfl)))
    (by decide)

/-! ## Reaction–diffusion mode selection: an empty record -/

/-- Mirror of the Agda `TuringModeSelectionWitness`: every condition of the
reaction–diffusion module is an uninterpreted predicate supplied by whoever
inhabits the record. -/
structure ModeSelectionWitness where
  /-- The parameter carrier. -/
  Parameter : Type
  /-- The mode carrier. -/
  Mode : Type
  /-- The chosen parameter. -/
  parameter : Parameter
  /-- The chosen mode. -/
  mode : Mode
  /-- The local-excitation condition, as supplied. -/
  LocalExcitation : Parameter → Prop
  /-- The lateral-inhibition condition, as supplied. -/
  LateralInhibition : Parameter → Prop
  /-- The finite-wavelength instability condition, as supplied. -/
  FiniteWavelengthUnstable : Parameter → Mode → Prop
  /-- Its witness. -/
  excitation : LocalExcitation parameter
  /-- Its witness. -/
  inhibition : LateralInhibition parameter
  /-- Its witness. -/
  finiteMode : FiniteWavelengthUnstable parameter mode

/-- **The record constrains nothing.**  Because the conditions are fields rather
than definitions, the witness record is inhabited by taking every condition to
be trivially true.  Any reading of an inhabitant as evidence of a Turing
instability would therefore be unsupported; the module is an open socket, not a
result. -/
theorem modeSelection_trivially_inhabited : Nonempty ModeSelectionWitness :=
  ⟨{ Parameter := Unit
     Mode := Unit
     parameter := ()
     mode := ()
     LocalExcitation := fun _ => True
     LateralInhibition := fun _ => True
     FiniteWavelengthUnstable := fun _ _ => True
     excitation := trivial
     inhibition := trivial
     finiteMode := trivial }⟩

end Integration.CellDynamics
