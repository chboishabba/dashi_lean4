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
  apply List.mem_filter.mpr
  constructor
  · exact present
  · have hnot : ¬ w ∈ d.witnessIds := by
      simpa [List.contains_eq_mem] using unrelated
    simpa [hnot]

theorem withdrawal_excludes_revoked_dependency
    (s : IdentityProjectionState) (w : NumericId) (d : WitnessedDerivation)
    (dependent : d.witnessIds.contains w = true) :
    d ∉ (withdrawWitness s w).current := by
  intro h
  have hkeep := (List.mem_filter.mp h).2
  have hmem : w ∈ d.witnessIds := by
    simpa [List.contains_eq_mem] using dependent
  have hbad : false = true := by
    simpa [List.contains_eq_mem, hmem] using hkeep
  cases hbad


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
    simp only [consumerRegionWork, List.filter_cons]
    have hnot : ¬ ((!published.contains id) = true) := by simp [head]
    rw [if_neg hnot]
    exact ih tail

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

/-- A repaired segmentation adds source-indexed candidate regions, never
    replaces existing region IDs or grants semantic authority. Coverage here
    is structural; actual parser token coverage is a separate obligation. -/
structure SourceRegionSpan where
  ref : String
  parentRef : String
  startChar : Nat
  endChar : Nat
  deriving Repr, BEq, DecidableEq

def coversChar (r : SourceRegionSpan) (i : Nat) : Prop :=
  r.startChar ≤ i ∧ i < r.endChar

def regionCovered (rs : List SourceRegionSpan) (i : Nat) : Prop :=
  ∃ r, r ∈ rs ∧ coversChar r i

def extendPartition (old added : List SourceRegionSpan) : List SourceRegionSpan :=
  old ++ added

theorem extension_preserves_original_region
    (old added : List SourceRegionSpan) (r : SourceRegionSpan)
    (h : r ∈ old) : r ∈ extendPartition old added := by
  simp [extendPartition, h]

theorem extension_exact_coverage
    (old added : List SourceRegionSpan) (i : Nat) :
    regionCovered (extendPartition old added) i ↔
      regionCovered old i ∨ regionCovered added i := by
  constructor
  · rintro ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with ho | ha
    · exact Or.inl ⟨r, ho, hc⟩
    · exact Or.inr ⟨r, ha, hc⟩
  · intro h
    rcases h with ⟨r, hr, hc⟩ | ⟨r, hr, hc⟩
    · exact ⟨r, List.mem_append.mpr (Or.inl hr), hc⟩
    · exact ⟨r, List.mem_append.mpr (Or.inr hr), hc⟩

theorem extension_preserves_unaffected_coverage
    (old added : List SourceRegionSpan) (i : Nat)
    (outside : ¬ regionCovered added i) :
    regionCovered (extendPartition old added) i ↔ regionCovered old i := by
  rw [extension_exact_coverage]
  exact or_iff_left outside

/-- Region insertion must wake consumers which depended on absence or
    completeness over the repaired interval, not only existing positive
    observations. A dependency predicate comes from the original owner. -/
def insertionAffects (depends : Nat → Prop) (added : List SourceRegionSpan) : Prop :=
  ∃ i, depends i ∧ regionCovered added i

theorem newly_covered_dependency_requires_wake
    (depends : Nat → Prop) (old added : List SourceRegionSpan) (i : Nat)
    (dep : depends i) (absent : ¬ regionCovered old i)
    (present : regionCovered (extendPartition old added) i) :
    insertionAffects depends added := by
  rcases (extension_exact_coverage old added i).mp present with h | h
  · exact False.elim (absent h)
  · exact ⟨i, dep, h⟩

theorem outside_insertion_preserves_dependency_coverage
    (depends : Nat → Prop) (old added : List SourceRegionSpan)
    (outside : ¬ insertionAffects depends added) (i : Nat) (dep : depends i) :
    regionCovered (extendPartition old added) i ↔ regionCovered old i := by
  apply extension_preserves_unaffected_coverage
  intro h
  exact outside ⟨i, dep, h⟩

/-- A typed refutation is an original admission event with same-demand,
    same-target evidence, not a numerical sign or execution-prune event. -/
def checkedRefutation (demand : Nat) (candidate : CandidateKey)
    (e : CandidateEvidence) : Bool :=
  decide (e.demand = demand ∧ e.target = candidate ∧ e.evidenceRef ≠ "")

theorem checked_refutation_sound (demand : Nat) (candidate : CandidateKey)
    (e : CandidateEvidence) (h : checkedRefutation demand candidate e = true) :
    RefutedBy demand candidate e := by
  exact of_decide_eq_true h

def liveTypedKeys (represented refuted : List CandidateKey) : List CandidateKey :=
  represented.filter (fun k => !refuted.contains k)

theorem live_typed_keys_sound (represented refuted : List CandidateKey)
    (k : CandidateKey) (h : k ∈ liveTypedKeys represented refuted) :
    k ∈ represented ∧ k ∉ refuted := by
  have hm := List.mem_filter.mp h
  refine ⟨hm.1, ?_⟩
  simpa [List.contains_eq_mem] using hm.2

theorem live_typed_keys_complete (represented refuted : List CandidateKey)
    (k : CandidateKey) (hr : k ∈ represented) (hn : k ∉ refuted) :
    k ∈ liveTypedKeys represented refuted := by
  apply List.mem_filter.mpr
  exact ⟨hr, by simp [List.contains_eq_mem, hn]⟩

/-- Numerical ABI specialization of the existing Agda
    DASHI.Cognition.PNF.IdentityEvidenceProduction permission boundary
    and SensibLaw m079/m080, not a new identity rule. The full family
    cardinality, not the bounded retained member count, controls permission.
    Actual original admitted witness/authority remains an independent premise. -/
def parserEvidencePermission (kind fullCardinality : Nat)
    (independentlyCorroborated : Bool) : Bool :=
  (fullCardinality == 1) &&
    ((kind == 2) || (kind == 4) || (kind == 6) ||
      ((kind == 3) && independentlyCorroborated))

theorem ambiguous_parser_evidence_cannot_license
    (kind fullCardinality : Nat) (corroborated : Bool)
    (ambiguous : fullCardinality ≠ 1) :
    parserEvidencePermission kind fullCardinality corroborated = false := by
  simp [parserEvidencePermission, ambiguous]

theorem proper_name_cannot_bootstrap (fullCardinality : Nat) :
    parserEvidencePermission 3 fullCardinality false = false := by
  simp [parserEvidencePermission]

/-- Bounded family execution retains the original full count. Even a
    one-member execution packet cannot manufacture unique admissibility. -/
structure BoundedParserFamily where
  fullCardinality : Nat
  retainedCardinality : Nat
  retainedBound : retainedCardinality ≤ fullCardinality

theorem retained_singleton_does_not_pay_ambiguous_family
    (f : BoundedParserFamily) (kind : Nat) (corroborated : Bool)
    (_retained : f.retainedCardinality = 1)
    (ambiguous : f.fullCardinality ≠ 1) :
    parserEvidencePermission kind f.fullCardinality corroborated = false :=
  ambiguous_parser_evidence_cannot_license kind f.fullCardinality corroborated ambiguous

example : parserEvidencePermission 2 1 false = true := by decide
example : parserEvidencePermission 4 1 false = true := by decide
example : parserEvidencePermission 6 1 false = true := by decide
example : parserEvidencePermission 3 1 true = true := by decide
example : parserEvidencePermission 3 1 false = false := by decide
example : parserEvidencePermission 3 17 true = false := by decide
example : parserEvidencePermission 5 1 true = false := by decide

/-- Original m090 excludes the same object and the same containing PERSON
    span. Their intersection must be subtracted only once. This is the
    exact finite family carrier used by the SLR bounded SQL refinement. -/
def eligibleParserFamily {α : Type} (family : List α)
    (sameAnchor sameSpan : α → Bool) : List α :=
  family.filter (fun x => !sameAnchor x && !sameSpan x)

def anchorExcludedFamily {α : Type} (family : List α)
    (sameAnchor : α → Bool) : List α :=
  family.filter sameAnchor

def spanOnlyExcludedFamily {α : Type} (family : List α)
    (sameAnchor sameSpan : α → Bool) : List α :=
  family.filter (fun x => !sameAnchor x && sameSpan x)

theorem parser_family_exact_cardinality {α : Type} (family : List α)
    (sameAnchor sameSpan : α → Bool) :
    (eligibleParserFamily family sameAnchor sameSpan).length +
      (anchorExcludedFamily family sameAnchor).length +
      (spanOnlyExcludedFamily family sameAnchor sameSpan).length =
      family.length := by
  induction family with
  | nil => rfl
  | cons x xs ih =>
    cases ha : sameAnchor x <;> cases hs : sameSpan x <;>
      simp [eligibleParserFamily, anchorExcludedFamily, spanOnlyExcludedFamily,
        ha, hs] at ih ⊢ <;> omega

/-- Retained and deferred members are an exact ordered partition. The
    deferred suffix is execution debt, never semantic refutation. -/
theorem parser_family_retained_deferred_exact {α : Type}
    (family : List α) (sameAnchor sameSpan : α → Bool) (limit : Nat) :
    (eligibleParserFamily family sameAnchor sameSpan).take limit ++
      (eligibleParserFamily family sameAnchor sameSpan).drop limit =
      eligibleParserFamily family sameAnchor sameSpan := by
  exact List.take_append_drop limit _

example :
    eligibleParserFamily ([1,2,3,4] : List Nat) (fun x => x == 1 || x == 2)
      (fun x => x == 2 || x == 3) = [4] := by decide

example : parserEvidencePermission 3 4 true = false := by decide

/-- Source-permission refinement of the original Agda
    BoundedProperNameEvidenceExecution.embeddedPersonTokenCannotExpand.
    The m090 reference producer by itself does not discharge this premise.
    This is a golden boundary, not authority to change the SQL producer. -/
def parserEvidencePermissionWithSourceContext
    (kind fullCardinality : Nat) (corroborated embeddedInPerson : Bool) : Bool :=
  parserEvidencePermission kind fullCardinality corroborated &&
    (!(kind == 3) || !embeddedInPerson)

theorem embedded_proper_name_cannot_license
    (fullCardinality : Nat) (corroborated : Bool) :
    parserEvidencePermissionWithSourceContext 3 fullCardinality corroborated true = false := by
  simp [parserEvidencePermissionWithSourceContext]

theorem standalone_name_retains_original_permission
    (fullCardinality : Nat) (corroborated : Bool) :
    parserEvidencePermissionWithSourceContext 3 fullCardinality corroborated false =
      parserEvidencePermission 3 fullCardinality corroborated := by
  simp [parserEvidencePermissionWithSourceContext]

example : parserEvidencePermissionWithSourceContext 3 1 true true = false := by decide
example : parserEvidencePermissionWithSourceContext 3 1 true false = true := by decide


/-- A nonmonotone source delta is an outstanding authority obligation,
not a flag on a single execution pass. Only a separately checked owner
reconciliation can discharge it. An empty scheduling pass cannot do so. -/
def pendingAuthorityAfter (pending withdrawn checkedReconciliation : Bool) : Bool :=
  (pending || withdrawn) && !checkedReconciliation

theorem empty_pass_preserves_pending_authority (pending : Bool) :
    pendingAuthorityAfter pending false false = pending := by
  cases pending <;> rfl

theorem withdrawal_blocks_without_reconciliation (pending : Bool) :
    pendingAuthorityAfter pending true false = true := by
  cases pending <;> rfl

def authorityUsable (pending currentEvidenceValid : Bool) : Bool :=
  !pending && currentEvidenceValid

theorem pending_authority_cannot_be_used (valid : Bool) :
    authorityUsable true valid = false := by
  cases valid <;> rfl

/-- Evidence withdrawal does not delete the represented carrier or
change semantic admissibility by itself. The physical support predicate
is supplied by the original producer, not inferred from residual sign. -/
def currentOwnedAtoms {α : Type} (history : List α) (supported : α → Bool) :=
  history.filter supported

theorem current_owned_atom_exact {α : Type} (history : List α)
    (supported : α → Bool) (a : α) :
    a ∈ currentOwnedAtoms history supported ↔ a ∈ history ∧ supported a = true := by
  simp [currentOwnedAtoms]

example : pendingAuthorityAfter (pendingAuthorityAfter false true false) false false = true := by decide
example : pendingAuthorityAfter true false true = false := by decide

/-- A drained represented slice may reconcile execution debt without a
semantic proof only if every original current authority lane is absent.
This is the authority-free branch, not a proof of typed coverage. -/
def candidateOnlyReconciliation
    (drained projectionExact admissibility proof coverage sufficiency : Bool) : Bool :=
  drained && projectionExact && !admissibility && !proof && !coverage && !sufficiency

theorem candidate_only_reconciliation_no_authority
    (d e a p c s : Bool)
    (h : candidateOnlyReconciliation d e a p c s = true) :
    d = true ∧ e = true ∧ a = false ∧ p = false ∧ c = false ∧ s = false := by
  cases d <;> cases e <;> cases a <;> cases p <;> cases c <;> cases s <;>
    simp_all [candidateOnlyReconciliation]

theorem candidate_only_reconciliation_clears_debt
    (pending withdrawn : Bool) :
    pendingAuthorityAfter pending withdrawn
      (candidateOnlyReconciliation true true false false false false) = false := by
  cases pending <;> cases withdrawn <;> rfl

example : candidateOnlyReconciliation true true true false false false = false := by decide
example : candidateOnlyReconciliation true true false true false false = false := by decide
example : candidateOnlyReconciliation true true false false true false = false := by decide
example : candidateOnlyReconciliation true true false false false true = false := by decide
example : candidateOnlyReconciliation false true false false false false = false := by decide
example : candidateOnlyReconciliation true false false false false false = false := by decide

/-- Journal insertion records physical withdrawal for either represented
horizon. Restoration is not an owner reconciliation. Initial supported
observation is neutral. Reuse pendingAuthorityAfter rather than minting
another semantic authority state. -/
def pendingAfterValidityObservation (pending supported : Bool) : Bool :=
  pendingAuthorityAfter pending (!supported) false

theorem validity_withdrawal_then_restoration_preserves_debt (pending : Bool) :
    pendingAfterValidityObservation
      (pendingAfterValidityObservation pending false) true = true := by
  cases pending <;> rfl

theorem restored_physical_support_cannot_reactivate_unreconciled_authority
    (pending : Bool) :
    authorityUsable
      (pendingAfterValidityObservation
        (pendingAfterValidityObservation pending false) true) true = false := by
  cases pending <;> rfl

theorem supported_observation_preserves_debt (pending : Bool) :
    pendingAfterValidityObservation pending true = pending := by
  cases pending <;> rfl

/-- A signed contribution and its observation count are separate. In
particular zero evidence has count one; an absent observation has count
zero. This is the exact three-threshold aggregate used by the SLR SQL
production view, not a new preference or authority rule. -/
abbrev HorizonAtom := Nat × Int
abbrev HorizonTally := Int × Nat

def horizonAtomTally (cutoff : Nat) (atom : HorizonAtom) : HorizonTally :=
  if atom.1 ≤ cutoff then (atom.2, 1) else (0, 0)

def addHorizonTally (a b : HorizonTally) : HorizonTally :=
  (a.1 + b.1, a.2 + b.2)

def oneHorizonTally (cutoff : Nat) : List HorizonAtom → HorizonTally
  | [] => (0, 0)
  | a :: rest => addHorizonTally (horizonAtomTally cutoff a)
      (oneHorizonTally cutoff rest)

/-- One traversal carries all three independent exact threshold tallies. -/
def threeHorizonTallies : List HorizonAtom → HorizonTally × HorizonTally × HorizonTally
  | [] => ((0, 0), (0, 0), (0, 0))
  | a :: rest =>
      let t := threeHorizonTallies rest
      (addHorizonTally (horizonAtomTally 3 a) t.1,
       addHorizonTally (horizonAtomTally 6 a) t.2.1,
       addHorizonTally (horizonAtomTally 9 a) t.2.2)

theorem three_horizon_tallies_exact (atoms : List HorizonAtom) :
    threeHorizonTallies atoms =
      (oneHorizonTally 3 atoms, oneHorizonTally 6 atoms, oneHorizonTally 9 atoms) := by
  induction atoms with
  | nil => rfl
  | cons a rest ih =>
      simp only [threeHorizonTallies, oneHorizonTally, ih]

example : threeHorizonTallies [(3, 0), (3, 5), (6, -5), (9, -2)] =
    ((5, 2), (0, 3), (-2, 4)) := by decide
example : threeHorizonTallies [] = ((0, 0), (0, 0), (0, 0)) := by decide

/-- The original ITIR source-bound referee receipt is necessary but not
sufficient for paying an exact SLR formal premise. The independently
issued binding must match all coordinates of the persisted demand and
artifact, and its receipt store must not be writable by the consumer.
No conclusion about legal truth or typed coverage follows. -/
structure RefereePremiseBinding where
  demandRef : String
  obligationRef : String
  consumerRef : String
  pnfRevisionRef : String
  statementDigest : String
  resultKind : String
  sourceRevisions : List String
  artifactDigest : String
  checkerRevision : String
  dependencies : List String
  residualRef : String
  propositionRef : Option String
  da51Address : Option String
  artifactRef : String
  sourceRevision : String
  evidenceRef : String
  producer : String
  checker : String
  statementLanguage : String
  targetProver : String
  dependentRefs : List String
  deriving DecidableEq

def authenticatedPremiseCheck (readOnly sourceBound : Bool)
    (expected : RefereePremiseBinding) (observed : Option RefereePremiseBinding) : Bool :=
  readOnly && sourceBound && decide (observed = some expected)

theorem authenticated_premise_requires_exact_binding
    (ro sb : Bool) (expected : RefereePremiseBinding)
    (observed : Option RefereePremiseBinding)
    (h : authenticatedPremiseCheck ro sb expected observed = true) :
    ro = true ∧ sb = true ∧ observed = some expected := by
  cases ro <;> cases sb <;> simp_all [authenticatedPremiseCheck]

theorem source_only_receipt_cannot_pay
    (expected : RefereePremiseBinding) :
    authenticatedPremiseCheck true true expected none = false := by
  simp [authenticatedPremiseCheck]

/-- Original authority is demand-scoped. If any consumer projection
uses that demand, newly recorded withdrawal invalidates its authority
regardless of whether it registered the particular evidence atom. -/
def demandAuthorityAffected (withdrawn : List Nat) (demand : Nat) : Bool :=
  withdrawn.contains demand

theorem same_demand_authority_must_reopen
    (withdrawn : List Nat) (demand : Nat) (h : demand ∈ withdrawn) :
    demandAuthorityAffected withdrawn demand = true := by
  simp [demandAuthorityAffected, List.contains_eq_mem, h]

theorem unrelated_demand_authority_not_affected
    (withdrawn : List Nat) (demand : Nat) (h : demand ∉ withdrawn) :
    demandAuthorityAffected withdrawn demand = false := by
  simp [demandAuthorityAffected, List.contains_eq_mem, h]

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

#print axioms Wikidata.Slr.NumericPnfRustPortContract.extension_exact_coverage
#print axioms Wikidata.Slr.NumericPnfRustPortContract.newly_covered_dependency_requires_wake
#print axioms Wikidata.Slr.NumericPnfRustPortContract.outside_insertion_preserves_dependency_coverage

#print axioms Wikidata.Slr.NumericPnfRustPortContract.checked_refutation_sound
#print axioms Wikidata.Slr.NumericPnfRustPortContract.live_typed_keys_sound
#print axioms Wikidata.Slr.NumericPnfRustPortContract.live_typed_keys_complete

#print axioms Wikidata.Slr.NumericPnfRustPortContract.ambiguous_parser_evidence_cannot_license
#print axioms Wikidata.Slr.NumericPnfRustPortContract.proper_name_cannot_bootstrap
#print axioms Wikidata.Slr.NumericPnfRustPortContract.retained_singleton_does_not_pay_ambiguous_family

#print axioms Wikidata.Slr.NumericPnfRustPortContract.parser_family_exact_cardinality
#print axioms Wikidata.Slr.NumericPnfRustPortContract.parser_family_retained_deferred_exact

#print axioms Wikidata.Slr.NumericPnfRustPortContract.embedded_proper_name_cannot_license
#print axioms Wikidata.Slr.NumericPnfRustPortContract.standalone_name_retains_original_permission

#print axioms Wikidata.Slr.NumericPnfRustPortContract.empty_pass_preserves_pending_authority
#print axioms Wikidata.Slr.NumericPnfRustPortContract.withdrawal_blocks_without_reconciliation
#print axioms Wikidata.Slr.NumericPnfRustPortContract.pending_authority_cannot_be_used
#print axioms Wikidata.Slr.NumericPnfRustPortContract.current_owned_atom_exact

#print axioms Wikidata.Slr.NumericPnfRustPortContract.candidate_only_reconciliation_no_authority
#print axioms Wikidata.Slr.NumericPnfRustPortContract.candidate_only_reconciliation_clears_debt

#print axioms Wikidata.Slr.NumericPnfRustPortContract.validity_withdrawal_then_restoration_preserves_debt
#print axioms Wikidata.Slr.NumericPnfRustPortContract.restored_physical_support_cannot_reactivate_unreconciled_authority
#print axioms Wikidata.Slr.NumericPnfRustPortContract.supported_observation_preserves_debt

#print axioms Wikidata.Slr.NumericPnfRustPortContract.three_horizon_tallies_exact

#print axioms Wikidata.Slr.NumericPnfRustPortContract.authenticated_premise_requires_exact_binding
#print axioms Wikidata.Slr.NumericPnfRustPortContract.source_only_receipt_cannot_pay

#print axioms Wikidata.Slr.NumericPnfRustPortContract.same_demand_authority_must_reopen
#print axioms Wikidata.Slr.NumericPnfRustPortContract.unrelated_demand_authority_not_affected
