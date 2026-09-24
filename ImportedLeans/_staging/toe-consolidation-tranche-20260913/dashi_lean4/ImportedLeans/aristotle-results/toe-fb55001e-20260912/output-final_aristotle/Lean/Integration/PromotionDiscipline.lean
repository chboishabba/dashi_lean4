import Integration.OutstandingObligations
import Integration.SourceExactWelds

/-!
# Promotion discipline: which evidence licenses which reclassification

`Integration.OutstandingObligations` records, for each open registry row, *what
it is waiting for*.  This file adds the missing half: **not every piece of
evidence permits every transition.**  It models the registry as a transition
system on the seven classes, with the licensed transitions declared and — for
the three that matter — the *negative* entries proved rather than stipulated.

## The transition system

`EvidenceKind` enumerates the kinds of evidence a row can acquire, and
`EvidenceKind.mayPromoteTo` is the declared transition table.  A row of class
`k` may move to class `k'` on evidence `e` exactly when
`MayPromote k e k'` holds, i.e. when `k` is an open obligation and the table
licenses `k'`.

## What is proved, not declared

* `shared_shape_gives_no_transport` — two carriers can satisfy the same
  predicate while admitting no equivalence at all, hence no `Transport`.  So a
  shared shape (a fortiori a shared *name*) can produce a `structuralAnalogue`
  and can never produce an `exactInstance`:
  `naming_resemblance_cannot_promote_to_exactInstance`.
* `coverage_flag_cannot_discharge_exhaustiveness` — a Boolean coverage
  declaration is compatible with a non-exhaustive carrier, so it supplies no
  `Exhaustive` evidence; the corresponding table row is `false` everywhere
  (`coverage_flag_promotes_nothing`).
* `enumeration_completeness_does_promote` — the contrasting positive: the
  corpus's decided `SSP` enumeration *does* yield `Exhaustive` evidence and does
  license the upgrade.  So the discipline is discriminating, not uniformly
  negative.

## Consistency with the existing bookkeeping

* `promotion_never_lands_in_an_open_class` — no licensed transition leaves the
  row open, matching `OutstandingObligations.discharge_always_closes`.
* `agda_typecheck_promotes_nothing` — an Agda checker result changes validation
  status, not class, matching `MissingEvidence.wouldReclassifyTo = none`.
* `ledger_transitions_are_licensed` — every entry of the live obligation ledger
  names a transition this table licenses.  A ledger entry claiming an
  unlicensed promotion breaks the build.

No registry row is added or reclassified here.
-/

namespace Integration.PromotionDiscipline

open Integration.SewingTaxonomy
open Integration.OutstandingObligations
open Integration.Levels
open Integration.RealisationAdequacy

/-! ## §1 The evidence kinds and the transition table -/

/-- The kinds of evidence a row can acquire. -/
inductive EvidenceKind
  /-- The two sides share a name, or a name fragment. -/
  | namingResemblance
  /-- The two carriers provably satisfy a common predicate, with no map between
  them. -/
  | sharedShapePredicate
  /-- A corpus record declares its own coverage with a `Bool` field. -/
  | booleanCoverageDeclaration
  /-- A corpus surface inhabiting a proved implication's hypothesis. -/
  | exactSourceCarrier
  /-- A theorem pinning a field that the corpus leaves free. -/
  | inhabitingTheorem
  /-- A proof that an enumeration exhausts its ambient type. -/
  | enumerationCompleteness
  /-- A refutation of the row's claim. -/
  | collisionWitness
  /-- A run of the Agda typechecker. -/
  | agdaTypecheckResult
  deriving DecidableEq, Repr, Fintype

/-- **The transition table.**  Which class each kind of evidence can license a
row into.  The three `false` rows are justified by the theorems in §2; the
positive rows say only that the evidence *is of the kind* the target class
demands, and each still requires the witness to be supplied. -/
def EvidenceKind.mayPromoteTo : EvidenceKind → Kind → Bool
  | .namingResemblance, _ => false
  | .sharedShapePredicate, .structuralAnalogue => true
  | .sharedShapePredicate, _ => false
  | .booleanCoverageDeclaration, _ => false
  | .exactSourceCarrier, .exactInstance => true
  | .exactSourceCarrier, _ => false
  | .inhabitingTheorem, .exactInstance => true
  | .inhabitingTheorem, _ => false
  | .enumerationCompleteness, .exactInstance => true
  | .enumerationCompleteness, _ => false
  | .collisionWitness, .negativeResult => true
  | .collisionWitness, _ => false
  | .agdaTypecheckResult, _ => false

/-- A licensed transition: the row is currently open, and the evidence licenses
the target class. -/
def MayPromote (source : Kind) (e : EvidenceKind) (target : Kind) : Prop :=
  source.isOpenObligation = true ∧ e.mayPromoteTo target = true

instance (source : Kind) (e : EvidenceKind) (target : Kind) :
    Decidable (MayPromote source e target) := by
  unfold MayPromote; infer_instance

/-! ## §2 The negative entries, proved -/

/-- **A shared shape yields no equivalence of carriers.**  `Unit` and `Bool` are
both nonempty, and there is no bijection between them, so the predicate they
share transports nothing. -/
theorem shared_shape_gives_no_transport :
    ∃ (P : Type → Prop) (A B : Type), P A ∧ P B ∧ IsEmpty (A ≃ B) := by
  refine ⟨fun T => Nonempty T, Unit, Bool, ⟨()⟩, ⟨true⟩, ⟨fun e => ?_⟩⟩
  have := Fintype.card_congr e
  simp at this

/-- Hence there is no `Transport` either, for any choice of operations. -/
theorem shared_shape_gives_no_transport_structure :
    IsEmpty (Transport Unit Bool id id) :=
  ⟨fun t => by
    have := Fintype.card_congr t.map
    simp at this⟩

/-- **Naming resemblance cannot promote a `candidateBridge` to an
`exactInstance`.**  The table says so, and the previous theorem is why: the
strongest object a shared name or shape can produce is a `structuralAnalogue`,
which by construction carries no map between the carriers. -/
theorem naming_resemblance_cannot_promote_to_exactInstance :
    ¬ MayPromote .candidateBridge .namingResemblance .exactInstance ∧
      IsEmpty (Transport Unit Bool id id) ∧
      (Relation.structuralAnalogue (fun T => Nonempty T) Unit Bool ⟨()⟩ ⟨true⟩).kind =
        Kind.structuralAnalogue :=
  ⟨by decide, shared_shape_gives_no_transport_structure, rfl⟩

/-- And the same for a shared shape predicate: it reaches `structuralAnalogue`
and stops there. -/
theorem shared_shape_reaches_only_structuralAnalogue (k : Kind) :
    EvidenceKind.mayPromoteTo .sharedShapePredicate k = true ↔ k = .structuralAnalogue := by
  revert k; decide

/-- **A Boolean coverage declaration cannot discharge an exhaustiveness
obligation.**  The declaration's flag can be set on a carrier that is not
exhaustive, so it yields no `Exhaustive` evidence. -/
theorem coverage_flag_cannot_discharge_exhaustiveness :
    ∃ d : CoverageDeclaration ℕ,
      d.claimsExhaustive = true ∧ ¬ Nonempty (Exhaustive d.carrier) :=
  flag_does_not_give_exhaustive

/-- So that kind of evidence licenses no transition at all. -/
theorem coverage_flag_promotes_nothing (k : Kind) :
    EvidenceKind.mayPromoteTo .booleanCoverageDeclaration k = false := by
  revert k; decide

/-- **The contrasting positive.**  A proved enumeration completeness *is*
`Exhaustive` evidence, and it does license the upgrade — on the corpus's `SSP`
carrier, where the enumeration is decided.  The discipline is therefore
discriminating. -/
theorem enumeration_completeness_does_promote :
    EvidenceKind.mayPromoteTo .enumerationCompleteness Kind.exactInstance = true ∧
      Nonempty (Exhaustive (fun p : AgdaMirror.MonsterOntos.SSP =>
        p ∈ Integration.SourceExactWelds.SSPAdequacy.sspEnumeration)) :=
  ⟨rfl, ⟨Integration.SourceExactWelds.SSPAdequacy.sspExhaustive⟩⟩

/-! ## §3 Consistency with the registry bookkeeping -/

/-- **No licensed transition leaves the row open.**  Promotion always closes an
obligation; it never moves one open class to another. -/
theorem promotion_never_lands_in_an_open_class (source : Kind) (e : EvidenceKind) (target : Kind)
    (h : MayPromote source e target) : target.isOpenObligation = false := by
  revert h; revert source e target; decide

/-- **An Agda checker result changes validation status, not class.** -/
theorem agda_typecheck_promotes_nothing (k : Kind) :
    EvidenceKind.mayPromoteTo .agdaTypecheckResult k = false := by
  revert k; decide

/-- The ledger's typed missing evidence, read as an evidence kind. -/
def missingEvidenceKind : MissingEvidence → EvidenceKind
  | .exactSourceCarrier _ => .exactSourceCarrier
  | .theoremInhabitingField _ => .inhabitingTheorem
  | .collisionWitness _ => .collisionWitness
  | .enumerationCompleteness _ => .enumerationCompleteness
  | .agdaTypecheckResult => .agdaTypecheckResult

/-- **Every live obligation names a licensed transition.**  For each ledger
entry, the class it says it would move to is one this table permits for that
kind of evidence.  A ledger entry claiming an unlicensed promotion — say, a
`candidateBridge` promoted to `exactInstance` on a coverage flag — would break
this proof. -/
theorem ledger_transitions_are_licensed :
    ∀ o ∈ obligationLedger, ∀ k ∈ o.missing.wouldReclassifyTo,
      (missingEvidenceKind o.missing).mayPromoteTo k = true := by
  intro o ho k hk
  have h : obligationLedger.all (fun o =>
      match o.missing.wouldReclassifyTo with
      | none => true
      | some k => (missingEvidenceKind o.missing).mayPromoteTo k) = true := rfl
  have hall := List.all_eq_true.mp h o ho
  revert hall hk
  cases hw : o.missing.wouldReclassifyTo with
  | none => simp
  | some k' =>
    intro hk hall
    simp only [Option.mem_def] at hk
    cases hk
    simpa using hall

/-- And no ledger entry is waiting for evidence of a kind that licenses nothing:
every open row's evidence either reclassifies it or is explicitly recorded as
changing validation status only. -/
theorem ledger_evidence_is_actionable :
    ∀ o ∈ obligationLedger,
      o.missing.wouldReclassifyTo = none ∨
        ∃ k, o.missing.wouldReclassifyTo = some k ∧
          (missingEvidenceKind o.missing).mayPromoteTo k = true := by
  intro o ho
  cases hw : o.missing.wouldReclassifyTo with
  | none => exact Or.inl rfl
  | some k =>
    exact Or.inr ⟨k, rfl, ledger_transitions_are_licensed o ho k (by simp [hw])⟩

end Integration.PromotionDiscipline
