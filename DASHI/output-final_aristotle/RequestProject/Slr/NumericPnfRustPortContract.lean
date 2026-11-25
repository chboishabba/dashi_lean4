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
  targetMatchesChosen : targetObjectId = chosen
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
  canonicalDirtyOwnerCost : Nat
  outputRows : Nat
  actualVisitedUnits : Nat
  workMultiplier : Nat

def charge (d : DeltaWork) : Nat :=
  d.newObservations + d.touchedDependencyEdges + d.canonicalDirtyOwnerCost + d.outputRows

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


/-- Candidate keys include the target kind; object and entity IDs can collide
    numerically. Only evidence for the same key can eliminate a possibility. -/
structure CandidateKey where
  kind : Nat
  id : Nat
  deriving Repr, BEq, DecidableEq

structure CandidateEvidence where
  demand : Nat
  target : CandidateKey
  evidenceRef : String
  deriving Repr, BEq, DecidableEq

def RefutedBy (demand : Nat) (candidate : CandidateKey)
    (evidence : CandidateEvidence) : Prop :=
  evidence.demand = demand ∧ evidence.target = candidate ∧
    evidence.evidenceRef ≠ ""

theorem foreign_candidate_evidence_cannot_refute
    (demand : Nat) (a b : CandidateKey) (e : CandidateEvidence)
    (different : a ≠ b) (bound : e.target = a) :
    ¬ RefutedBy demand b e := by
  intro h
  exact different (bound.symm.trans h.2.1)

/-- The coverage proof applies to every typed live key, not just currently
    scheduled object candidates. The planner target and survivor must agree. -/
structure ExactTypedSelection (Live : CandidateKey → Prop)
    (represented : List CandidateKey) (selected : CandidateKey) where
  complete : ∀ k, Live k → k ∈ represented
  selectedLive : Live selected
  unique : ∀ k, k ∈ represented → Live k → k = selected
  objectKind : selected.kind = 1

theorem typed_selection_global_unique {Live : CandidateKey → Prop}
    {represented : List CandidateKey} {selected : CandidateKey}
    (cert : ExactTypedSelection Live represented selected) :
    ∀ k, Live k → k = selected := by
  intro k live
  exact cert.unique k (cert.complete k live) live

theorem second_typed_live_key_blocks_selection
    {Live : CandidateKey → Prop} {represented : List CandidateKey}
    {selected other : CandidateKey} (live : Live other)
    (different : other ≠ selected) :
    ¬ Nonempty (ExactTypedSelection Live represented selected) := by
  intro h
  obtain ⟨cert⟩ := h
  exact different (typed_selection_global_unique cert other live)

theorem unique_actor_target_matches_live {s : State}
    {Live : NumericId → Prop} {chosen : NumericId}
    (w : OriginalUniqueIdentity s Live chosen) :
    ∀ id, Live id → id = w.targetObjectId := by
  intro id live
  exact (w.allLiveSame id live).trans w.targetMatchesChosen.symm

/-- A failed owner transaction leaves both the dirty key and its former
    materialisation intact. This is an atomicity specification, not a
    verification of PostgreSQL isolation or of the Rust client. -/
structure DirtyFrontier where
  dirty : List OwnerId
  materialised : OwnerId → Nat

def finishOwner (s : DirtyFrontier) (owner : OwnerId)
    (value : Nat) (commit : Bool) : DirtyFrontier :=
  if commit then
    { dirty := s.dirty.filter (fun k => k != owner),
      materialised := writeOwner s.materialised owner value }
  else s

theorem failed_owner_transaction_preserves_state
    (s : DirtyFrontier) (owner : OwnerId) (value : Nat) :
    finishOwner s owner value false = s := rfl

theorem committed_owner_preserves_other_materialisation
    (s : DirtyFrontier) (owner other : OwnerId) (value : Nat)
    (different : other ≠ owner) :
    (finishOwner s owner value true).materialised other =
      s.materialised other := by
  simp [finishOwner, writeOwner, different]


/-- Original Level-1 premises and witness history are immutable; the current
    dependent view is the authority-changing part. Multiple alternative
    witnesses may support a re-materialised derivation after withdrawal. -/
structure WitnessedDerivation where
  ref : String
  premise : Nat
  witnessIds : List NumericId
  deriving Repr, BEq, DecidableEq

structure IdentityProjectionState where
  levelOne : List Nat
  witnessHistory : List NumericId
  admitted : List NumericId
  current : List WitnessedDerivation
  deriving Repr, BEq, DecidableEq

def withdrawWitness (s : IdentityProjectionState) (w : NumericId) :
    IdentityProjectionState :=
  { s with admitted := s.admitted.filter (fun i => i != w)
           current := s.current.filter (fun d => !d.witnessIds.contains w) }

theorem withdrawal_preserves_level_one (s : IdentityProjectionState)
    (w : NumericId) :
    (withdrawWitness s w).levelOne = s.levelOne := rfl

theorem withdrawal_preserves_history (s : IdentityProjectionState)
    (w : NumericId) :
    (withdrawWitness s w).witnessHistory = s.witnessHistory := rfl

theorem withdrawal_keeps_unrelated_derivation
    (s : IdentityProjectionState) (w : NumericId) (d : WitnessedDerivation)
    (present : d ∈ s.current) (unrelated : d.witnessIds.contains w = false) :
    d ∈ (withdrawWitness s w).current := by
  simp [withdrawWitness, present, unrelated]

theorem withdrawal_excludes_revoked_dependency
    (s : IdentityProjectionState) (w : NumericId) (d : WitnessedDerivation)
    (dependent : d.witnessIds.contains w = true) :
    d ∉ (withdrawWitness s w).current := by
  simp [withdrawWitness, dependent]


/-- Occurrence transport extends represented possibilities, not the
    admitted identity relation. The two distinct source objects remain
    distinct even if their labels agree. -/
def transportOccurrence (s : State) (id : NumericId) : State :=
  { s with semantic := {
      s.semantic with represented := id :: s.semantic.represented
    }
  }

theorem occurrence_transport_preserves_manifest (s : State) (id : NumericId) :
    (transportOccurrence s id).semantic.manifest = s.semantic.manifest := rfl

theorem occurrence_transport_preserves_open_world (s : State) (id : NumericId) :
    (transportOccurrence s id).semantic.outsideModelPossible =
      s.semantic.outsideModelPossible := rfl

theorem occurrence_transport_preserves_refutation (s : State) (id : NumericId) :
    (transportOccurrence s id).semantic.semanticRefutations =
      s.semantic.semanticRefutations := rfl

theorem occurrence_transport_cannot_admit (s : State) (id : NumericId) :
    (transportOccurrence s id).semantic.admittedWitnesses =
      s.semantic.admittedWitnesses := rfl

theorem occurrence_transport_cannot_substitute (s : State) (id : NumericId) :
    (transportOccurrence s id).semantic.levelThreeDerivations =
      s.semantic.levelThreeDerivations := rfl

theorem occurrence_transport_retains_both (s : State) (a b : NumericId) :
    a ∈ (transportOccurrence (transportOccurrence s a) b).semantic.represented ∧
    b ∈ (transportOccurrence (transportOccurrence s a) b).semantic.represented := by
  simp [transportOccurrence]


/-- The source occurrence fibre and the identity-class fibre are distinct.
    The class map is partial until existing proof-relevant, source-bound
    admission licenses it. It is not computed from spellings or QIDs. -/
structure AdmittedClassProjection (Class : NumericId → Option NumericId)
    (Admitted : NumericId → NumericId → Prop) where
  sound : ∀ o e, Class o = some e → Admitted o e

/-- This is a different endpoint from ExactTypedSelection: all live original
    occurrences must be covered, and every one must have a licensed map to
    the same entity. A class-level endpoint does not fabricate the unique
    source-object witness required by the older m069/m072 demand API. -/
structure VerifiedClassSelection (s : State) (Live : NumericId → Prop)
    (Class : NumericId → Option NumericId)
    (Admitted : NumericId → NumericId → Prop) (chosen : NumericId) where
  coverage : VerifiedCoverage s Live
  classProjection : AdmittedClassProjection Class Admitted
  inhabited : ∃ o, Live o
  allLiveInClass : ∀ o, Live o → Class o = some chosen

theorem unique_class_preserves_occurrence_evidence
    {s : State} {Live : NumericId → Prop}
    {Class : NumericId → Option NumericId}
    {Admitted : NumericId → NumericId → Prop} {chosen : NumericId}
    (cert : VerifiedClassSelection s Live Class Admitted chosen)
    (o : NumericId) (live : Live o) :
    o ∈ s.semantic.represented ∧ Admitted o chosen :=
  ⟨cert.coverage.allLiveRepresented o live,
    cert.classProjection.sound o chosen (cert.allLiveInClass o live)⟩

theorem unknown_class_blocks_selection
    {s : State} {Live : NumericId → Prop}
    {Class : NumericId → Option NumericId}
    {Admitted : NumericId → NumericId → Prop} {chosen o : NumericId}
    (live : Live o) (unknown : Class o = none) :
    ¬ Nonempty (VerifiedClassSelection s Live Class Admitted chosen) := by
  intro h
  obtain ⟨cert⟩ := h
  have contradictionEq := cert.allLiveInClass o live
  rw [unknown] at contradictionEq
  cases contradictionEq

theorem different_class_blocks_selection
    {s : State} {Live : NumericId → Prop}
    {Class : NumericId → Option NumericId}
    {Admitted : NumericId → NumericId → Prop} {chosen o other : NumericId}
    (live : Live o) (mapped : Class o = some other) (different : other ≠ chosen) :
    ¬ Nonempty (VerifiedClassSelection s Live Class Admitted chosen) := by
  intro h
  obtain ⟨cert⟩ := h
  exact different (Option.some.inj (mapped.symm.trans (cert.allLiveInClass o live)))

theorem two_occurrences_can_have_one_class :
    ∃ (a b e : NumericId) (Class : NumericId → Option NumericId),
      a ≠ b ∧ Class a = some e ∧ Class b = some e := by
  exact ⟨1, 2, 3, fun _ => some 3, by decide, rfl, rfl⟩


/-- Consumer-relative physical workset: original region IDs are selected
    before publication. Unavailable coverage is a separate residual, not
    a reason to execute unrelated corpus regions. This specializes the
    existing DeltaWork contract, not a new semantic reducer. -/
def consumerRegionWork {α : Type} [BEq α] (required published : List α) : List α :=
  required.filter (fun id => !published.contains id)

theorem consumer_work_cannot_include_unrequested
    {α : Type} [BEq α] (required published : List α) (id : α)
    (h : id ∈ consumerRegionWork required published) :
    id ∈ required := by
  exact (List.mem_filter.mp h).1

theorem consumer_work_empty_if_required_published
    {α : Type} [BEq α] (required published : List α)
    (covered : ∀ id, id ∈ required → published.contains id = true) :
    consumerRegionWork required published = [] := by
  induction required with
  | nil => rfl
  | cons id rest ih =>
    have head : published.contains id = true := covered id (by simp)
    have tail : ∀ x, x ∈ rest → published.contains x = true := by
      intro x hx
      exact covered x (by simp [hx])
    simp [consumerRegionWork, head, ih tail]

/-- One owner refresh supplies both observation and prospective admission.
    Equality is a pure snapshot law, not a claim about an arbitrary SQL
    function's transactional semantics. Callers must establish same input
    and preserve candidate-only versus admitted output boundaries. -/
def sharedProducer {Input Output Admission : Type}
    (produce : Input → Output) (admit : Output → Admission) (i : Input) :
    Output × Admission :=
  let observed := produce i
  (observed, admit observed)

theorem shared_producer_same_snapshot {Input Output Admission : Type}
    (produce : Input → Output) (admit : Output → Admission) (i : Input) :
    sharedProducer produce admit i = (produce i, admit (produce i)) := rfl

example : consumerRegionWork ([1, 2, 3] : List Nat) [1, 3, 99] = [2] := by decide
example : consumerRegionWork ([1, 2] : List Nat) [1, 2, 99] = [] := by decide
example : consumerRegionWork ["s1", "s2", "s3"] ["s1", "s3", "unrelated"] = ["s2"] := by decide

end Wikidata.Slr.NumericPnfRustPortContract

#print axioms Wikidata.Slr.NumericPnfRustPortContract.equivalent_preserves_original_manifest
#print axioms Wikidata.Slr.NumericPnfRustPortContract.pruning_cannot_refute
#print axioms Wikidata.Slr.NumericPnfRustPortContract.parsing_cannot_admit_identity
#print axioms Wikidata.Slr.NumericPnfRustPortContract.omitted_live_candidate_defeats_coverage
#print axioms Wikidata.Slr.NumericPnfRustPortContract.distinct_owner_updates_commute
#print axioms Wikidata.Slr.NumericPnfRustPortContract.zero_delta_cannot_hide_whole_document_work
#print axioms Wikidata.Slr.NumericPnfRustPortContract.foreign_manifest_invalidates_replay

#print axioms Wikidata.Slr.NumericPnfRustPortContract.typed_selection_global_unique
#print axioms Wikidata.Slr.NumericPnfRustPortContract.second_typed_live_key_blocks_selection
#print axioms Wikidata.Slr.NumericPnfRustPortContract.unique_actor_target_matches_live
#print axioms Wikidata.Slr.NumericPnfRustPortContract.failed_owner_transaction_preserves_state

#print axioms Wikidata.Slr.NumericPnfRustPortContract.withdrawal_preserves_level_one
#print axioms Wikidata.Slr.NumericPnfRustPortContract.withdrawal_keeps_unrelated_derivation
#print axioms Wikidata.Slr.NumericPnfRustPortContract.withdrawal_excludes_revoked_dependency

#print axioms Wikidata.Slr.NumericPnfRustPortContract.occurrence_transport_preserves_open_world
#print axioms Wikidata.Slr.NumericPnfRustPortContract.occurrence_transport_cannot_admit
#print axioms Wikidata.Slr.NumericPnfRustPortContract.occurrence_transport_retains_both

#print axioms Wikidata.Slr.NumericPnfRustPortContract.unique_class_preserves_occurrence_evidence
#print axioms Wikidata.Slr.NumericPnfRustPortContract.unknown_class_blocks_selection
#print axioms Wikidata.Slr.NumericPnfRustPortContract.different_class_blocks_selection
#print axioms Wikidata.Slr.NumericPnfRustPortContract.two_occurrences_can_have_one_class

#print axioms Wikidata.Slr.NumericPnfRustPortContract.consumer_work_cannot_include_unrequested
#print axioms Wikidata.Slr.NumericPnfRustPortContract.consumer_work_empty_if_required_published
#print axioms Wikidata.Slr.NumericPnfRustPortContract.shared_producer_same_snapshot
