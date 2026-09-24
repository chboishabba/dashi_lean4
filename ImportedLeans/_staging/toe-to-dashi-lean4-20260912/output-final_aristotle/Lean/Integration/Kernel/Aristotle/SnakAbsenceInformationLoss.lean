import Integration.Kernel.Bridges.InformationLossLocus
import RequestProject.Snaks

/-!
# Aristotle instantiation: absence, `novalue`, and where the distinction is lost

The generic bridge `Integration.Kernel.Bridges.InformationLossLocus` says that a
distinction collapsed by one stage of a pipeline is never restored downstream,
and that *where* it is lost is a property of the pair, not of the stack.  This
file instantiates both halves on the snak semantics of the archive module
`RequestProject.Snaks`, where the three states that a naive pipeline flattens
are genuinely different:

* `uninspected (Q,P)` — the pair has not been looked at;
* `noStatementObserved (Q,P)` — the pair was inspected and the base records no
  statement for it;
* `nativeNoValue (Q,P)` — the base carries an explicit Wikidata `novalue` snak.

## What is proved

* **`empty_result_does_not_entail_novalue`** — the firewall, in the archive's own
  model theory: there is a satisfiable base whose recorded value list for `(Q,P)`
  is empty and which does **not** entail `novalue` for `(Q,P)`.  An empty query
  result is not a `novalue` claim.
* `novalue_gives_empty_result` — the other direction does hold in a clash-free
  base, which is exactly why the value projection collapses the two states.
* **`value_projection_collapses_absence`** — two bases with the *same* recorded
  values for every subject–property pair, exactly one of which entails
  `novalue`.
* **`downstream_cannot_restore_novalue`** — consequently every downstream
  function of the value projection gives the same answer on the two bases: no
  deterministic post-processing recovers the distinction without new
  information.
* `locus_is_pair_relative_for_snak_absence` — the pair-relative locus, on a
  two-stage flattening of the three states: the pair
  `(noStatementObserved, nativeNoValue)` is lost at stage 1, the pair
  `(uninspected, nativeNoValue)` only at stage 2, so no function of the stack
  alone reports where absence information is destroyed.
* `absence_collapse_persists` — once collapsed, always collapsed (the bridge's
  `collapse_persists`, instantiated).

**Claim boundary.**  `absentBase`, `noValueBase` and `otherBase` are finite
bases defined here; `Status` is a three-label type.  The entailment semantics
(`Satisfies`, `Models`, `Entails`) is the archive's, and
`empty_result_does_not_entail_novalue` is proved through the archive's
`entails_noValue_iff`, not stipulated.
-/

namespace Integration.Kernel.Aristotle.SnakAbsenceInformationLoss

open Integration.Kernel

/-! ## §1 The three states, as bases -/

/-- The subject of the fixture. -/
def subj : Wikidata.Qid := .wd "Q42"

/-- The property of the fixture. -/
def prop : Wikidata.Qid := .wd "P40"

/-- Another property, used to make a base non-empty without touching `prop`. -/
def otherProp : Wikidata.Qid := .wd "P22"

/-- The base recording nothing at all about `(subj, prop)`. -/
def absentBase : Wikidata.SnakBase := []

/-- A base that was inspected and records a statement about a *different*
property: for `(subj, prop)` the observed result is still empty. -/
def otherBase : Wikidata.SnakBase :=
  [ ⟨subj, otherProp, .value (.item (.wd "Q1"))⟩ ]

/-- The base carrying the native Wikidata `novalue` snak for `(subj, prop)`. -/
def noValueBase : Wikidata.SnakBase :=
  [ ⟨subj, prop, .noValue⟩ ]

theorem absentBase_satisfiable : Wikidata.SnakBase.Satisfiable absentBase :=
  ⟨fun _ _ => ∅, by intro st hst; cases hst⟩

theorem otherBase_satisfiable : Wikidata.SnakBase.Satisfiable otherBase :=
  Wikidata.SnakBase.satisfiable_iff_clashFreeB.2 (by decide)

theorem noValueBase_clashFree : Wikidata.SnakBase.ClashFree noValueBase :=
  Wikidata.SnakBase.clashFreeB_iff.1 (by decide)

/-! ## §2 The firewall: empty result is not `novalue` -/

/-- **An empty result is not a `novalue` claim.**  The base is satisfiable, its
recorded values for `(subj, prop)` are empty, and it does not entail `novalue`
there. -/
theorem empty_result_does_not_entail_novalue :
    Wikidata.SnakBase.Satisfiable otherBase ∧
    Wikidata.SnakBase.valuesOf otherBase subj prop = [] ∧
    ¬ Wikidata.SnakBase.Entails otherBase ⟨subj, prop, .noValue⟩ := by
  refine ⟨otherBase_satisfiable, by decide, ?_⟩
  intro h
  have hmem := (Wikidata.SnakBase.entails_noValue_iff otherBase_satisfiable).1 h
  revert hmem
  decide

/-- A native `novalue` really does give an empty result: this is the collapse. -/
theorem novalue_gives_empty_result :
    Wikidata.SnakBase.valuesOf noValueBase subj prop = [] :=
  Wikidata.SnakBase.valuesOf_eq_nil_of_noValue noValueBase_clashFree (by simp [noValueBase])

/-! ## §3 The collapsed projection and its irreversibility -/

/-- The value projection: what a consumer sees if it only reads returned values. -/
def valueProjection (B : Wikidata.SnakBase) (s p : Wikidata.Qid) : List Wikidata.Value :=
  Wikidata.SnakBase.valuesOf B s p

theorem valuesOf_absentBase (s p : Wikidata.Qid) :
    Wikidata.SnakBase.valuesOf absentBase s p = [] := rfl

theorem valuesOf_noValueBase (s p : Wikidata.Qid) :
    Wikidata.SnakBase.valuesOf noValueBase s p = [] := by
  simp [Wikidata.SnakBase.valuesOf, noValueBase]

/-- **The value projection collapses absence into `novalue`.**  Two bases agree
on every recorded value, for every subject and property, yet exactly one of them
entails `novalue` for `(subj, prop)`. -/
theorem value_projection_collapses_absence :
    (∀ s p, valueProjection absentBase s p = valueProjection noValueBase s p) ∧
    Wikidata.SnakBase.Entails noValueBase ⟨subj, prop, .noValue⟩ ∧
    ¬ Wikidata.SnakBase.Entails absentBase ⟨subj, prop, .noValue⟩ := by
  refine ⟨fun s p => by rw [valueProjection, valueProjection, valuesOf_absentBase,
      valuesOf_noValueBase], ?_, ?_⟩
  · exact Wikidata.SnakBase.entails_of_mem (by simp [noValueBase])
  · intro h
    have hmem := (Wikidata.SnakBase.entails_noValue_iff absentBase_satisfiable).1 h
    exact (List.not_mem_nil hmem)

/-- **No downstream stage restores the distinction.**  Every function of the
value projection — however elaborate the pipeline behind it — returns the same
answer on the two bases. -/
theorem downstream_cannot_restore_novalue {β : Type} (F : List Wikidata.Value → β)
    (s p : Wikidata.Qid) :
    F (valueProjection absentBase s p) = F (valueProjection noValueBase s p) :=
  congrArg F (value_projection_collapses_absence.1 s p)

/-! ## §4 The locus is pair-relative -/

/-- The three epistemic states a pipeline over the snak layer can be in for a
subject–property pair. -/
inductive Status where
  /-- The pair has not been inspected. -/
  | uninspected
  /-- The pair was inspected and no statement was observed. -/
  | noStatementObserved
  /-- The base carries a native Wikidata `novalue` snak. -/
  | nativeNoValue
deriving DecidableEq, Repr, Inhabited

/-- A two-stage flattening: stage `0` reports "nothing came back" for a native
`novalue`, stage `1` forgets whether the pair was inspected at all. -/
def stack : ℕ → Status → Status
  | 0, .nativeNoValue => .noStatementObserved
  | 0, s => s
  | 1, .uninspected => .noStatementObserved
  | 1, s => s
  | _, s => s

/-- The `novalue`/no-statement distinction is destroyed by the first stage. -/
theorem novalue_pair_lost_at_one :
    Bridges.InformationLossLocus.firstLoss stack Status.noStatementObserved
      Status.nativeNoValue 3 = some 1 := by decide

/-- The uninspected/`novalue` distinction survives it and is destroyed by the
second. -/
theorem uninspected_pair_lost_at_two :
    Bridges.InformationLossLocus.firstLoss stack Status.uninspected
      Status.nativeNoValue 3 = some 2 := by decide

/-- **The locus is pair-relative for snak absence.**  One stack, two pairs, two
different loci: "which stage loses absence information" is not a function of the
stack. -/
theorem locus_is_pair_relative_for_snak_absence :
    Bridges.InformationLossLocus.firstLoss stack Status.noStatementObserved
        Status.nativeNoValue 3
      ≠ Bridges.InformationLossLocus.firstLoss stack Status.uninspected
        Status.nativeNoValue 3 := by decide

/-- Once the two absence states are collapsed they stay collapsed at every later
stage: the bridge's `collapse_persists`, instantiated on the snak statuses. -/
theorem absence_collapse_persists :
    ∀ m, 1 ≤ m →
      Bridges.InformationLossLocus.run stack m Status.noStatementObserved
        = Bridges.InformationLossLocus.run stack m Status.nativeNoValue :=
  Bridges.InformationLossLocus.collapse_persists (by decide)

end Integration.Kernel.Aristotle.SnakAbsenceInformationLoss
