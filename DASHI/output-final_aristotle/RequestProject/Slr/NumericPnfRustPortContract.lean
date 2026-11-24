import Lean

/-!
P0 native numeric-PNF Rust port: mathematical contract, not a port acceptance.

This model separates exact source identity, semantic carrier, scheduling,
typed open-world coverage, witnessed unique numeric identity and measured
structural work. It deliberately proves no parity for a Rust binary not yet
implemented, nor a canonical-source bridge between different documents.
-/

namespace Wikidata.Slr.NumericPnfRustPortContract

structure Manifest where
  documentRef : String
  revisionRef : String
  canonicalSha256 : String
  canonicalByteLength : Nat
  unicodeCodepointLength : Nat
  coordinateContractRef : String
  normalizationContractRef : String
  parserRunRef : String
  compilerRuleSetRef : String
  deriving Repr, BEq, DecidableEq

abbrev NumericId := Nat
abbrev OwnerId := Nat

structure SemanticCarrier where
  manifest : Manifest
  observations : List String
  factors : List String
  represented : List NumericId
  semanticRefutations : List NumericId
  residuals : List String
  provenance : List String
  outsideModelPossible : Bool
  coverageWitness : Option String
  admittedWitnesses : List NumericId
  levelThreeDerivations : List String
  deriving Repr, BEq, DecidableEq

structure ExecutionState where
  active : List NumericId
  deferred : List NumericId
  dirtyOwners : List OwnerId
  replayCursor : Nat
  deriving Repr, BEq, DecidableEq

structure State where
  semantic : SemanticCarrier
  execution : ExecutionState
  deriving Repr, BEq, DecidableEq

def observe (s : State) : SemanticCarrier := s.semantic

def ConsumerEquivalent (a b : State) : Prop := observe a = observe b

theorem consumer_equivalent_refl (a : State) :
    ConsumerEquivalent a a := rfl

theorem consumer_equivalent_symm {a b : State}
    (h : ConsumerEquivalent a b) : ConsumerEquivalent b a := h.symm

theorem consumer_equivalent_trans {a b c : State}
    (ab : ConsumerEquivalent a b)
    (bc : ConsumerEquivalent b c) : ConsumerEquivalent a c :=
  Eq.trans ab bc

theorem equivalent_preserves_original_manifest {a b : State}
    (eq : ConsumerEquivalent a b) :
    a.semantic.manifest = b.semantic.manifest :=
  congrArg SemanticCarrier.manifest eq

theorem foreign_source_cannot_replay {a b : State}
    (different : a.semantic.manifest ≠ b.semantic.manifest) :
    ¬ ConsumerEquivalent a b := by
  intro eq
  exact different (equivalent_preserves_original_manifest eq)

def executionPrune (s : State) (candidate : NumericId) : State :=
  { s with execution := {
      s.execution with
      active := s.execution.active.filter (fun id => id != candidate)
      deferred := candidate :: s.execution.deferred
    }
  }

theorem pruning_preserves_source (s : State) (candidate : NumericId) :
    (executionPrune s candidate).semantic.manifest =
      s.semantic.manifest := rfl

theorem pruning_cannot_refute (s : State) (candidate : NumericId) :
    (executionPrune s candidate).semantic.semanticRefutations =
      s.semantic.semanticRefutations := rfl

theorem pruning_cannot_admit_identity (s : State) (candidate : NumericId) :
    (executionPrune s candidate).semantic.admittedWitnesses =
      s.semantic.admittedWitnesses := rfl

def admitObservation (s : State) (ref : String) : State :=
  { s with semantic := {
      s.semantic with observations := ref :: s.semantic.observations
    }
  }

theorem parsing_cannot_admit_identity (s : State) (ref : String) :
    (admitObservation s ref).semantic.admittedWitnesses =
      s.semantic.admittedWitnesses := rfl

theorem parsing_cannot_materialize_level_three (s : State) (ref : String) :
    (admitObservation s ref).semantic.levelThreeDerivations =
      s.semantic.levelThreeDerivations := rfl

/-- A closed world demands an owner-issued completeness certificate.
    A finite set of names, a pruning event and a 64-item cap are insufficient. -/
structure VerifiedCoverage (s : State) (Live : NumericId → Prop) where
  closed : s.semantic.outsideModelPossible = false
  witnessRef : String
  nonemptyRef : witnessRef ≠ ""
  exactReceipt : s.semantic.coverageWitness = some witnessRef
  allLiveRepresented : ∀ id, Live id → id ∈ s.semantic.represented

theorem omitted_live_candidate_defeats_coverage
    (s : State) (Live : NumericId → Prop)
    (id : NumericId) (live : Live id)
    (missing : id ∉ s.semantic.represented) :
    ¬ Nonempty (VerifiedCoverage s Live) := by
  intro all
  cases all with
  | intro cover =>
    exact missing (cover.allLiveRepresented id live)

/-- The numeric actor, not the text label, must be uniquely supported. -/
structure OriginalUniqueIdentity
    (s : State) (Live : NumericId → Prop)
    (chosen : NumericId) where
  coverage : VerifiedCoverage s Live
  chosenLive : Live chosen
  allLiveSame : ∀ id, Live id → id = chosen
  sourceObjectId : NumericId
  targetObjectId : NumericId
  originalOwnerWitnessRef : String
  authorityRef : String
  originalAdmission : Prop
  admissionChecked : originalAdmission

theorem unique_numeric_actor {s : State}
    {Live : NumericId → Prop} {chosen : NumericId}
    (w : OriginalUniqueIdentity s Live chosen) :
    ∀ id, Live id → id = chosen :=
  w.allLiveSame

/-- Only different-owner keyed replacements commute automatically.
    Same-owner canonical first-compatible grouping still needs its
    own factorization theorem; this one does not confer it. -/
def writeOwner (store : OwnerId → Nat) (owner : OwnerId)
    (value : Nat) : OwnerId → Nat :=
  fun key => if key = owner then value else store key

theorem distinct_owner_updates_commute
    (store : OwnerId → Nat) (a b va vb : Nat) (different : a ≠ b) :
    writeOwner (writeOwner store a va) b vb =
      writeOwner (writeOwner store b vb) a va := by
  funext key
  by_cases ha : key = a
  · subst key
    simp [writeOwner, different, Ne.symm different]
  · by_cases hb : key = b
    · subst key
      simp [writeOwner, different, Ne.symm different]
    · simp [writeOwner, ha, hb]

structure DeltaWork where
  newObservations : Nat
  touchedDependencyEdges : Nat
  outputRows : Nat
  actualVisitedUnits : Nat
  workMultiplier : Nat

def charge (d : DeltaWork) : Nat :=
  d.newObservations + d.touchedDependencyEdges + d.outputRows

def WorkBounded (d : DeltaWork) : Prop :=
  d.actualVisitedUnits ≤ d.workMultiplier * charge d

theorem zero_delta_cannot_hide_whole_document_work
    (d : DeltaWork) (empty : charge d = 0)
    (bounded : WorkBounded d) : d.actualVisitedUnits = 0 := by
  have upper : d.actualVisitedUnits ≤ 0 := by
    simpa [WorkBounded, empty] using bounded
  exact Nat.eq_zero_of_le_zero upper

inductive Replay where
  | current
  | invalidated
  deriving Repr, BEq, DecidableEq

def replay (before after : State) : Replay :=
  if observe before = observe after then .current else .invalidated

theorem exact_replay_current (s : State) : replay s s = .current := by
  simp [replay]

theorem foreign_manifest_invalidates_replay
    (a b : State)
    (different : a.semantic.manifest ≠ b.semantic.manifest) :
    replay a b = .invalidated := by
  have neq : observe a ≠ observe b :=
    foreign_source_cannot_replay different
  simp [replay, neq]

theorem schedule_change_cannot_change_source_semantics
    (s : State) (other : ExecutionState) :
    ConsumerEquivalent s { s with execution := other } := rfl

end Wikidata.Slr.NumericPnfRustPortContract

#print axioms Wikidata.Slr.NumericPnfRustPortContract.equivalent_preserves_original_manifest
#print axioms Wikidata.Slr.NumericPnfRustPortContract.pruning_cannot_refute
#print axioms Wikidata.Slr.NumericPnfRustPortContract.parsing_cannot_admit_identity
#print axioms Wikidata.Slr.NumericPnfRustPortContract.omitted_live_candidate_defeats_coverage
#print axioms Wikidata.Slr.NumericPnfRustPortContract.distinct_owner_updates_commute
#print axioms Wikidata.Slr.NumericPnfRustPortContract.zero_delta_cannot_hide_whole_document_work
#print axioms Wikidata.Slr.NumericPnfRustPortContract.foreign_manifest_invalidates_replay
