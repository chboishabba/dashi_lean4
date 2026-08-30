import Integration.SewingRegistry

/-!
# The frontier, extracted from the registry

`Integration.SewingRegistry` records what happened: eighty-one classified
relations between corpus surfaces and the owner set.  This file derives from it
the object that says what *remains provable*: the rows whose class is
`candidateBridge` or `openSocket`, each paired with the typed answer to

> what evidence would change this row's classification?

Two things are machine-checked rather than asserted.

* `outstanding_count` — the number of outstanding rows is exactly the
  `candidateBridge` count plus the `openSocket` count, computed from the
  registry by `Integration.SewingRegistry.kindCensus`.
* `ledger_covers_outstanding` — the ledger below lists exactly the outstanding
  rows, by their registry index.  A row that changes class, or a new open row
  added without a ledger entry, breaks this proof and therefore the build.

And one discipline is enforced:

* `discharge_always_closes` — every recorded missing evidence, if supplied,
  moves the row *out of* the two open classes.  An entry whose discharge would
  leave the row open would be a mis-filed obligation.

Nothing here is a mathematical claim about any domain; it is bookkeeping about
the registry, with the bookkeeping proved.
-/

namespace Integration.OutstandingObligations

open Integration.SewingTaxonomy
open Integration.SewingRegistry

/-! ## Typed missing evidence -/

/-- What a row is waiting for.  Each constructor names the *kind* of artefact
that would settle the row, and carries a description of the specific one. -/
inductive MissingEvidence
  /-- A `candidateBridge` waiting for the corpus surface that inhabits its
  hypothesis. -/
  | exactSourceCarrier (what : String)
  /-- An `openSocket` waiting for a theorem that would pin the free field. -/
  | theoremInhabitingField (field : String)
  /-- A row that would be settled *negatively* by exhibiting a collision. -/
  | collisionWitness (what : String)
  /-- A row waiting for a constructive completeness proof of an enumeration. -/
  | enumerationCompleteness (what : String)
  /-- A row waiting for an Agda checker result.  This changes the validation
  status, not the class, which is why the target below is `none`. -/
  | agdaTypecheckResult
  deriving DecidableEq, Repr

/-- The class the row would move to once the evidence is supplied, where the
evidence determines one. -/
def MissingEvidence.wouldReclassifyTo : MissingEvidence → Option Kind
  | .exactSourceCarrier _ => some .exactInstance
  | .theoremInhabitingField _ => some .exactInstance
  | .collisionWitness _ => some .negativeResult
  | .enumerationCompleteness _ => some .exactInstance
  | .agdaTypecheckResult => none

/-- A row of the frontier: which registry row, what it is waiting for, and a
one-line statement of the obligation. -/
structure Obligation where
  /-- The zero-based index of the row in `sewingRegistry`. -/
  rowIndex : ℕ
  /-- What the row is waiting for. -/
  missing : MissingEvidence
  /-- The obligation in words. -/
  note : String

/-! ## The ledger -/

/-- The frontier: one entry per outstanding registry row. -/
def obligationLedger : List Obligation :=
  [ { rowIndex := 5
      missing := .theoremInhabitingField "the DNA sheet record's Bool flags"
      note := "A theorem pinning the sheet flags to the chemistry margin they \
               are supposed to summarise; at present two inhabitants differ \
               only at the flag." }
  , { rowIndex := 11
      missing := .theoremInhabitingField "the Alice Brown projection record"
      note := "A theorem making the projection record's fields functions of \
               the state, rather than independently settable labels." }
  , { rowIndex := 12
      missing := .theoremInhabitingField "the governance emptiness declaration"
      note := "A theorem deriving the declared emptiness from the carrier, \
               rather than declaring it." }
  , { rowIndex := 15
      missing := .theoremInhabitingField "the chemistry reachability flags"
      note := "A theorem tying each reachability flag to the bounded search it \
               reports; row 17 is the bridge that would do it." }
  , { rowIndex := 16
      missing := .exactSourceCarrier "a corpus reaction graph with a decidable fixpoint"
      note := "The bridge is proved; its hypothesis is a corpus-supplied graph \
               at which the fixpoint condition is decidable." }
  , { rowIndex := 20
      missing := .theoremInhabitingField "the loom evidence-status field"
      note := "A theorem determining evidence status from the relation type; \
               the current negative shows it is not so determined." }
  , { rowIndex := 31
      missing := .exactSourceCarrier "a transducer/dynamics adapter in the corpus"
      note := "The adapter implication is proved; the corpus supplies no \
               instance of its hypothesis." }
  , { rowIndex := 37
      missing := .theoremInhabitingField "the reaction–diffusion witness record"
      note := "A theorem constraining the mode-selection witness record, which \
               at present constrains nothing." }
  , { rowIndex := 38
      missing := .theoremInhabitingField "the holonomy reference frame"
      note := "A theorem supplying the frame the commutator owner needs; the \
               socket is deliberately open." }
  , { rowIndex := 43
      missing := .exactSourceCarrier "a corpus sampling surface"
      note := "The statistic-of-any-sample-size bridge is proved; no corpus \
               surface supplies the sampling datum." }
  , { rowIndex := 53
      missing := .theoremInhabitingField "the Pareto boundary record"
      note := "A theorem pinning the boundary record's fields to the outcome \
               order they describe." }
  , { rowIndex := 55
      missing := .exactSourceCarrier "a corpus language inclusion"
      note := "Monotonicity under language enlargement is proved; the corpus \
               supplies no declared inclusion to apply it to." }
  , { rowIndex := 61
      missing := .exactSourceCarrier "a provisioning pipeline stated over ℕ"
      note := "The obligation this row records is met on a corpus carrier by \
               row 71; the row's own hypothesis is still stated over ℕ and no \
               corpus surface inhabits it in that form." }
  , { rowIndex := 62
      missing := .exactSourceCarrier "a corpus consumer valued in an ordered field with a weighting"
      note := "No corpus surface supplies two weightings with opposite-signed \
               contrasts.  Row 72 shows that the provisioning surface cannot \
               supply one, so the search must move to another lane." }
  , { rowIndex := 66
      missing := .enumerationCompleteness "an atlas enumeration of its ambient type"
      note := "The bridge's hypothesis is now discharged on the SSP carrier \
               (row 76); the corpus atlases still decline the claim, and their \
               disclaimers remain the honest form." }
  , { rowIndex := 68
      missing := .theoremInhabitingField "Bool coverage/exhaustiveness fields"
      note := "A coverage flag is compatible with a non-exhaustive carrier, so \
               only `Exhaustive` evidence closes this; see row 76 for a carrier \
               where such evidence exists." }
  ]

/-! ## The derived frontier and its proofs -/

/-- The outstanding rows of the registry, with their indices. -/
noncomputable def outstandingIndices : List ℕ :=
  (sewingRegistry.zipIdx.filter (fun p => p.1.kind.isOpenObligation)).map (fun p => p.2)

/-- **The ledger lists exactly the outstanding rows.**  Adding an open row
without a ledger entry, or changing a row's class, breaks this proof. -/
theorem ledger_covers_outstanding :
    obligationLedger.map (fun o => o.rowIndex) = outstandingIndices := rfl

/-- **The count is the census.**  The number of outstanding obligations is the
`candidateBridge` count plus the `openSocket` count. -/
theorem outstanding_count :
    obligationLedger.length = kindCensus .candidateBridge + kindCensus .openSocket := rfl

/-- And in numbers. -/
theorem outstanding_length : obligationLedger.length = 16 := rfl

/-- **Discharging an obligation always closes it.**  No recorded evidence, if
supplied, would leave the row in one of the two open classes. -/
theorem discharge_always_closes :
    ∀ o ∈ obligationLedger, ∀ k ∈ o.missing.wouldReclassifyTo,
      k ≠ Kind.candidateBridge ∧ k ≠ Kind.openSocket := by
  intro o ho k hk
  have h : obligationLedger.all (fun o =>
      match o.missing.wouldReclassifyTo with
      | none => true
      | some k => decide (k ≠ Kind.candidateBridge ∧ k ≠ Kind.openSocket)) = true := rfl
  have := List.all_eq_true.mp h o ho
  revert this hk
  cases hw : o.missing.wouldReclassifyTo with
  | none => simp
  | some k' =>
    intro hk hall
    simp only [Option.mem_def] at hk
    cases hk
    simpa using hall

/-- The frontier splits into the two kinds of thing a row can be waiting for:
a source carrier that would inhabit a proved implication, and a theorem that
would pin a free field. -/
theorem frontier_split :
    (obligationLedger.filter (fun o =>
      match o.missing with | .exactSourceCarrier _ => true | _ => false)).length = 6 ∧
    (obligationLedger.filter (fun o =>
      match o.missing with | .theoremInhabitingField _ => true | _ => false)).length = 9 ∧
    (obligationLedger.filter (fun o =>
      match o.missing with | .enumerationCompleteness _ => true | _ => false)).length = 1 :=
  ⟨rfl, rfl, rfl⟩

end Integration.OutstandingObligations
