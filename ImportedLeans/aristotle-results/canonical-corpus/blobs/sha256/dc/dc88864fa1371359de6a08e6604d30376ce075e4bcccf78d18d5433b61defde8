import Integration.TernaryHub
import Integration.Refinement
import Cuisine.LoomBridge

/-!
# A cognition domain instance at the supervoxel / ternary junction

Lean mirror of `DASHI/Cognition/ClopenPsychologicalSupervoxel.agda`, together
with the pieces of `DASHI/Cognition/PhaseEnrichedTrit.agda` and
`DASHI/Cognition/ReflexivePresentationFamily.agda` that it depends on.

The cognition layer is the largest consumer of the supervoxel/clopen vocabulary
after physics, and this module is its cleanest statement: a nine-constraint
`ConstraintSystem` over a hidden psychological state, two refinements of the
"public zero" constraint, and the claim that the public zero is *not* atomic —
distinct hidden dynamics share one observable zero.

Provenance and what is new here.  The Agda module states the non-atomicity as a
**`Bool` placeholder**:

```agda
record ClopenPsychologyBoundary : Set where
  field
    publicZeroIsAtomic : Bool
    publicZeroIsAtomicIsFalse : publicZeroIsAtomic ≡ false
```

i.e. it *records* the value `false` rather than proving anything about the
constraint system. `publicZero_not_atomic` below proves the corresponding
statement about `Atomic`, in the same interface the loom, publication and
supervoxel lanes use.  The record's second field,
`subvoxelMechanismClinicallyValidated ≡ false`, is an *empirical* socket and is
deliberately left as one: nothing here is clinical, psychological or empirical
evidence, and `mechanism_not_validated_here` says exactly that.

Two further links, which the source does not state:

* `phase3Transport` — the cognition layer's cyclic `Phase3` is the ternary hub's
  `ZMod 3` with rotation `+1`, a level-4 transport;
* `observeTrit_flip` — reversing the polarity weights of a phase-enriched trit
  negates its observable, so the cognition observable is polarity-equivariant
  for the hub's involution.  This is the level-4 statement that the cognition
  layer's "balanced trit" really is the corpus's balanced trit.

Boundary: `HiddenState` is a record of finite tags and natural numbers, and the
reasoning component is left as an arbitrary type parameter `R` because the
source never inspects it.  No dynamics, no probability, no continuum.
-/

namespace Integration.CognitionSupervoxel

open Integration.TernaryHub
open Integration.Levels
open Cuisine.SupervoxelClopen (ConstraintSystem FineExtendsCoarse Atomic AdmissibleRegion)
open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth)

/-! ## `PhaseEnrichedTrit`: a cyclic phase over the balanced digit -/

/-- Mirror of `Phase3`. -/
inductive Phase3 | phase0 | phase1 | phase2
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `rotatePhase`. -/
def rotatePhase : Phase3 → Phase3
  | .phase0 => .phase1
  | .phase1 => .phase2
  | .phase2 => .phase0

theorem rotatePhase_three (p : Phase3) : rotatePhase (rotatePhase (rotatePhase p)) = p := by
  cases p <;> rfl

/-- The phase coordinate, in the hub's `ZMod 3`. -/
def phaseIdx : Phase3 → ZMod 3
  | .phase0 => 0 | .phase1 => 1 | .phase2 => 2

/-- `Phase3` is the hub's ternary carrier. -/
def phase3Equiv : Phase3 ≃ ZMod 3 where
  toFun := phaseIdx
  invFun z := if z = 0 then .phase0 else if z = 1 then .phase1 else .phase2
  left_inv := by decide
  right_inv := by decide

/-- **The cognition phase is the hub's `ZMod 3` with rotation `+1`** — a level-4
transport, not merely a three-element coincidence. -/
def phase3Transport : Transport Phase3 (ZMod 3) rotatePhase (fun z => z + 1) :=
  ⟨phase3Equiv, by decide⟩

/-- Mirror of `PhaseEnrichedTrit`. -/
structure PhaseTrit where
  /-- Weight of the negative polarity. -/
  negativeWeight : ℕ
  /-- Weight of the neutral position. -/
  neutralWeight : ℕ
  /-- Weight of the positive polarity. -/
  positiveWeight : ℕ
  /-- The cyclic phase. -/
  phase : Phase3
  deriving DecidableEq, Repr

/-- Mirror of `observeTrit`: a polarity is observed only when it is *strictly*
dominant over both of the others; ties and neutral dominance observe zero. -/
def observeTrit (s : PhaseTrit) : Trit :=
  if s.neutralWeight < s.negativeWeight ∧ s.positiveWeight < s.negativeWeight then .neg
  else if s.negativeWeight < s.positiveWeight ∧ s.neutralWeight < s.positiveWeight then .pos
  else .zer

/-- Mirror of the five named phase-enriched trits. -/
def negativeDominant : PhaseTrit := ⟨5, 1, 2, .phase0⟩
/-- The positively dominant profile. -/
def positiveDominant : PhaseTrit := ⟨1, 2, 5, .phase1⟩
/-- The neutrally dominant profile. -/
def neutralDominant : PhaseTrit := ⟨1, 5, 1, .phase2⟩
/-- Equal opposing weights, phase 0. -/
def balancedOpposition : PhaseTrit := ⟨4, 1, 4, .phase0⟩
/-- Equal opposing weights, phase 1. -/
def phaseShiftedBalancedOpposition : PhaseTrit := ⟨4, 1, 4, .phase1⟩

theorem negativeDominant_observes : observeTrit negativeDominant = .neg := by decide
theorem positiveDominant_observes : observeTrit positiveDominant = .pos := by decide
theorem neutralDominant_observes : observeTrit neutralDominant = .zer := by decide
theorem balancedOpposition_observes : observeTrit balancedOpposition = .zer := by decide
theorem phaseShifted_observes : observeTrit phaseShiftedBalancedOpposition = .zer := by decide

/-! ## The observable is the hub's balanced digit -/

/-- Reversing the two polarity weights. -/
def flipPolarity (s : PhaseTrit) : PhaseTrit :=
  ⟨s.positiveWeight, s.neutralWeight, s.negativeWeight, s.phase⟩

theorem flipPolarity_involutive (s : PhaseTrit) : flipPolarity (flipPolarity s) = s := rfl

/-- **The cognition observable is polarity-equivariant.**  Reversing the weights
negates the observed digit, so `observeTrit` intertwines `flipPolarity` with the
hub's involution `Trit.inv` — the sense in which the cognition layer's
"balanced trit" is the corpus's balanced trit. -/
theorem observeTrit_flip (s : PhaseTrit) : observeTrit (flipPolarity s) = Trit.inv (observeTrit s) := by
  simp only [observeTrit, flipPolarity]
  split_ifs with h1 h2 h3 h4 <;> first
    | rfl
    | (exfalso; omega)

/-- In balanced coordinates the observable's polarity is negation. -/
theorem balTrit_observeTrit_flip (s : PhaseTrit) :
    balTrit (observeTrit (flipPolarity s)) = - balTrit (observeTrit s) := by
  rw [observeTrit_flip]; exact (tritHub.equivariant _)

/-- The observable is onto the digit. -/
theorem observeTrit_surjective : Function.Surjective observeTrit := by
  intro t
  cases t
  · exact ⟨negativeDominant, negativeDominant_observes⟩
  · exact ⟨neutralDominant, neutralDominant_observes⟩
  · exact ⟨positiveDominant, positiveDominant_observes⟩

/-- …and genuinely lossy: the zero fibre is not a singleton.  This is the
structural content the source's `ZeroFibreWitness` gestures at. -/
theorem observeTrit_not_injective : ¬ Function.Injective observeTrit := by
  intro h
  have : balancedOpposition = phaseShiftedBalancedOpposition :=
    h (balancedOpposition_observes.trans phaseShifted_observes.symm)
  exact absurd this (by decide)

/-! ## The psychological hidden state and its constraint system -/

/-- Mirror of `PsychologicalHiddenState`.  The reasoning component is an
arbitrary type: the source module never inspects it. -/
structure HiddenState (R : Type) where
  /-- The (uninspected) reasoning component. -/
  reasoning : R
  /-- The avoided tone. -/
  avoidedValue : TriTruth
  /-- The remembered phase-enriched trit. -/
  rememberedValue : PhaseTrit
  /-- The expected phase-enriched trit. -/
  expectedValue : PhaseTrit
  /-- Depth of context. -/
  contextDepth : ℕ
  /-- Salience. -/
  salience : ℕ
  /-- Confidence. -/
  confidence : ℕ
  /-- The wave phase. -/
  wavePhase : Phase3
  /-- Number of active attractors. -/
  activeAttractorCount : ℕ

/-- Mirror of `balancedProjection`. -/
def balancedProjection {R : Type} (s : HiddenState R) : Trit :=
  observeTrit s.rememberedValue

/-- Mirror of `PsychologicalConstraint`. -/
inductive PsychConstraint
  | publicZero | inactiveZero | balancedOpposition | activeAppraisal
  | rapidSwitching | phaseCancellation | socialInhibition
  | insufficientEvidence | memoryFreeze
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `Satisfies`. -/
def Satisfies {R : Type} (s : HiddenState R) : PsychConstraint → Prop
  | .publicZero => balancedProjection s = .zer
  | .inactiveZero => s.salience = 0
  | .balancedOpposition => s.rememberedValue = balancedOpposition
  | .activeAppraisal => s.contextDepth = 1
  | .rapidSwitching => s.wavePhase = .phase2
  | .phaseCancellation => s.rememberedValue = phaseShiftedBalancedOpposition
  | .socialInhibition => s.avoidedValue = TriTruth.high
  | .insufficientEvidence => s.confidence = 0
  | .memoryFreeze => s.expectedValue = negativeDominant

/-- Mirror of `psychologicalConstraintSystem`, as an instance of the same
`ConstraintSystem` interface used by the supervoxel, loom and publication
lanes. -/
def psychSystem (R : Type) : ConstraintSystem where
  State := HiddenState R
  Constraint := PsychConstraint
  satisfies := Satisfies

/-- Mirror of `balancedOppositionRefinesPublicZero`. -/
theorem balancedOpposition_refines_publicZero (R : Type) :
    FineExtendsCoarse (psychSystem R) .publicZero .balancedOpposition :=
  ⟨fun {_} h => by
    show balancedProjection _ = _
    rw [balancedProjection, show _ = balancedOpposition from h]
    exact balancedOpposition_observes⟩

/-- Mirror of `phaseCancellationRefinesPublicZero`. -/
theorem phaseCancellation_refines_publicZero (R : Type) :
    FineExtendsCoarse (psychSystem R) .publicZero .phaseCancellation :=
  ⟨fun {_} h => by
    show balancedProjection _ = _
    rw [balancedProjection, show _ = phaseShiftedBalancedOpposition from h]
    exact phaseShifted_observes⟩

/-! ## The two canonical hidden states, and non-atomicity -/

variable {R : Type} [Inhabited R]

/-- Mirror of `canonicalHiddenState`. -/
def canonicalHiddenState (R : Type) [Inhabited R] : HiddenState R :=
  ⟨default, TriTruth.low, balancedOpposition, positiveDominant, 2, 4, 3, .phase0, 2⟩

/-- Mirror of `phaseShiftedHiddenState`. -/
def phaseShiftedHiddenState (R : Type) [Inhabited R] : HiddenState R :=
  { canonicalHiddenState R with
    rememberedValue := phaseShiftedBalancedOpposition
    wavePhase := .phase1 }

theorem canonical_satisfies_publicZero :
    Satisfies (canonicalHiddenState R) .publicZero := balancedOpposition_observes

theorem phaseShifted_satisfies_publicZero :
    Satisfies (phaseShiftedHiddenState R) .publicZero := phaseShifted_observes

theorem canonical_ne_phaseShifted :
    canonicalHiddenState R ≠ phaseShiftedHiddenState R := by
  intro h
  have h2 : balancedOpposition = phaseShiftedBalancedOpposition :=
    congrArg HiddenState.rememberedValue h
  exact absurd h2 (by decide)

/-- **The public zero is not atomic.**  Two distinct hidden states satisfy it,
so the coarse observable does not determine the fine state.  The Agda module
records this as the `Bool` value `false`; this is the statement about the
constraint system itself, in the same `Atomic` interface as
`Cuisine.SupervoxelClopen.cuisineNeutrality_not_atomic`,
`Cuisine.LoomBridge.loomRoot_not_atomic` and
`Integration.ClopenBalls.no_atomic_ball`. -/
theorem publicZero_not_atomic : ¬ Atomic (psychSystem R) .publicZero := by
  intro h
  exact canonical_ne_phaseShifted
    (h ⟨canonicalHiddenState R, canonical_satisfies_publicZero⟩
       ⟨phaseShiftedHiddenState R, phaseShifted_satisfies_publicZero⟩)

/-- Sharper: the coarse region has at least two elements, and both refinements
of the coarse constraint are inhabited, so the supervoxel really does split. -/
theorem publicZero_region_has_two :
    ∃ x y : AdmissibleRegion (psychSystem R) .publicZero, x.1 ≠ y.1 :=
  ⟨⟨canonicalHiddenState R, canonical_satisfies_publicZero⟩,
   ⟨phaseShiftedHiddenState R, phaseShifted_satisfies_publicZero⟩,
   canonical_ne_phaseShifted⟩

/-! ## The empirical socket, left as a socket -/

/-- Mirror of `ClopenPsychologyBoundary`.  The first pair of fields is now
redundant — `publicZero_not_atomic` proves the corresponding statement — and the
second pair is an *empirical* claim that nothing in this development addresses. -/
structure PsychologyBoundary where
  /-- Whether the public zero is atomic (the source records `false`). -/
  publicZeroIsAtomic : Bool
  /-- …and that it is `false`. -/
  publicZeroIsAtomicIsFalse : publicZeroIsAtomic = false
  /-- Whether the subvoxel mechanism has clinical validation. -/
  mechanismClinicallyValidated : Bool
  /-- …and that it is `false`. -/
  mechanismClinicallyValidatedIsFalse : mechanismClinicallyValidated = false

/-- The supplied inhabitant. -/
def canonicalPsychologyBoundary : PsychologyBoundary := ⟨false, rfl, false, rfl⟩

/-- **The empirical field is a socket and stays one.**  The record is
equivalent to the unit type: inhabiting it asserts nothing, and in particular
nothing in this file is clinical or psychological evidence. -/
def boundaryContentless : PsychologyBoundary ≃ Unit where
  toFun _ := ()
  invFun _ := canonicalPsychologyBoundary
  left_inv := by
    rintro ⟨a, ha, b, hb⟩
    subst ha; subst hb; rfl
  right_inv _ := rfl

/-- The junction, as one checked conjunction. -/
theorem cognition_supervoxel_junction :
    (∀ s : PhaseTrit, observeTrit (flipPolarity s) = Trit.inv (observeTrit s)) ∧
      Function.Surjective observeTrit ∧
      ¬ Function.Injective observeTrit ∧
      FineExtendsCoarse (psychSystem Unit) .publicZero .balancedOpposition ∧
      FineExtendsCoarse (psychSystem Unit) .publicZero .phaseCancellation ∧
      ¬ Atomic (psychSystem Unit) .publicZero :=
  ⟨observeTrit_flip, observeTrit_surjective, observeTrit_not_injective,
    balancedOpposition_refines_publicZero Unit, phaseCancellation_refines_publicZero Unit,
    publicZero_not_atomic⟩

end Integration.CognitionSupervoxel
