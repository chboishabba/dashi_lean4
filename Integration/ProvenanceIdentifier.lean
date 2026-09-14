import Mathlib

/-!
# Typed identifiers, source status, and the identity/authority firewall

The corpus carries four kinds of external identifier — DOI, Wikidata QID, Dewey
class, and plain publication/URL handles — scattered across Agda records
(`DASHI.Core.AttributedSourceCore`, `DASHI.Biology.EducationCorpusSourceRegistry`,
`DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas`, the Wikidata lanes) and
across the Lean mirrors (`Cuisine.SourceAtlas`, `Cuisine.Publication`,
`RequestProject.Provenance`).  Every one of those places re-encodes "which paper
is this" as a bare `String`, and several of them sit next to a `Bool` flag whose
name suggests that having the identifier settles something.

This module is the single typed carrier for that data, together with the
**firewall theorems** that say what an identifier can and cannot do:

* `Ident`, `Scheme`, `wellFormed` — identity and syntactic classification.
  Well-formedness is decidable and is checked on `String.toList`, so the checks
  actually reduce in the kernel (`decide` works on them);
* `SourceRecord`, `SourceStatus` — acquisition status of a source: whether it
  was obtained, only cited, paywalled, absent, or retracted;
* `ProofStatus` — the seven *separate* status classes the consolidation brief
  requires: proved theorem, conditional compiler/interface, open (or
  false-pinned) payment, no-go/counterexample, empirical source receipt,
  bookkeeping/provenance, and conjectural/physical promotion.  The three classes
  that assert Lean content **carry the Lean name inside the constructor**, so a
  row cannot be filed as proved without naming a theorem;
* the firewall itself:
  * `status_invariant_under_reprovenance` — re-attributing a claim to different
    sources does not change its proof status;
  * `provenance_does_not_determine_status` — there is *no* function from
    provenance to proof status; identifiers are never sufficient;
  * `wellFormed_provenance_without_receipt` and `receipt_without_provenance` —
    both directions of the independence are inhabited: a perfectly identified
    claim may be an open payment, and a proved theorem may cite nothing.

Nothing here asserts that any particular source exists, is correct, or supports
any claim.  The carriers are `String`s, finite enumerations and lists.
-/

namespace Integration.ProvenanceId

/-! ## 1.  Identifier schemes -/

/-- The identifier schemes the corpus actually uses. -/
inductive Scheme
  | doi | qid | dewey | isbn | arxiv | url | agdaModule | leanModule | localPath
  deriving DecidableEq, Fintype, Repr

/-- A typed external identifier: a scheme plus its body. -/
structure Ident where
  scheme : Scheme
  body : String
  deriving DecidableEq, Repr

/-- DOIs begin with the `10.` registrant prefix and contain a `/`. -/
def doiWellFormed (s : String) : Bool :=
  "10.".toList.isPrefixOf s.toList && s.toList.any (· = '/')

/-- Wikidata item identifiers are `Q` followed by at least one digit. -/
def qidWellFormed (s : String) : Bool :=
  s.toList.head? = some 'Q' && 1 < s.toList.length && (s.toList.drop 1).all Char.isDigit

/-- A Dewey class is three digits, optionally followed by `.` and more digits. -/
def deweyWellFormed (s : String) : Bool :=
  let cs := s.toList
  3 ≤ cs.length && (cs.take 3).all Char.isDigit &&
    ((cs.drop 3).isEmpty || ((cs.drop 3).head? = some '.' && (cs.drop 4).all Char.isDigit))

/-- Syntactic well-formedness of an identifier.  For the schemes with no fixed
grammar this is only non-emptiness: the point of the predicate is that it is a
*syntactic* check and nothing more. -/
def wellFormed (i : Ident) : Bool :=
  match i.scheme with
  | .doi => doiWellFormed i.body
  | .qid => qidWellFormed i.body
  | .dewey => deweyWellFormed i.body
  | _ => !i.body.toList.isEmpty

example : wellFormed ⟨.doi, "10.1090/S0002-9904"⟩ = true := by decide
example : wellFormed ⟨.doi, "S0002-9904"⟩ = false := by decide
example : wellFormed ⟨.qid, "Q42"⟩ = true := by decide
example : wellFormed ⟨.qid, "Q"⟩ = false := by decide
example : wellFormed ⟨.dewey, "641.5"⟩ = true := by decide
example : wellFormed ⟨.dewey, "64"⟩ = false := by decide

/-! ## 2.  Sources and their acquisition status -/

/-- Acquisition status of an external source.  `citedNotAcquired` is the honest
default for most rows in the corpus. -/
inductive SourceStatus
  | acquired | citedNotAcquired | paywalled | absent | retracted
  deriving DecidableEq, Fintype, Repr

/-- A source record: what it is, and whether we actually have it. -/
structure SourceRecord where
  ident : Ident
  status : SourceStatus
  note : String := ""
  deriving DecidableEq, Repr

/-! ## 3.  Proof status classes, kept separate -/

/-- The status classes the consolidation discipline requires to stay distinct.
The three Lean-asserting classes carry the Lean declaration name, so the type
itself forbids filing a row as closed without naming the receipt. -/
inductive ProofStatus
  /-- A Lean theorem, proved outright, named here. -/
  | provedTheorem (leanName : String)
  /-- A Lean theorem or interface that *compiles a hypothesis into a
  conclusion*: real content, but conditional on the listed hypotheses. -/
  | conditionalCompiler (leanName : String) (hypotheses : List String)
  /-- An obligation nobody has paid.  `falsePinned` records the special case
  where an in-corpus ledger flag pins the obligation to `false`. -/
  | openPayment (what : String)
  | falsePinned (ledgerFlag : String)
  /-- A proved impossibility or an explicit counterexample. -/
  | noGo (leanName : String)
  /-- An empirical/source receipt: a fact about a document, not about maths. -/
  | sourceReceipt (src : Ident)
  /-- Pure bookkeeping: indexing, hashes, path ledgers. -/
  | bookkeeping
  /-- A conjecture, or a physical promotion that no proof supports. -/
  | conjectural (what : String)
  deriving DecidableEq, Repr

/-- Does this status assert *Lean* content that a kernel receipt could back? -/
def carriesLeanReceipt : ProofStatus → Bool
  | .provedTheorem _ => true
  | .conditionalCompiler _ _ => true
  | .noGo _ => true
  | _ => false

/-- The named Lean declaration of a status, when it has one. -/
def leanName? : ProofStatus → Option String
  | .provedTheorem n => some n
  | .conditionalCompiler n _ => some n
  | .noGo n => some n
  | _ => none

/-- **Structural discipline.**  Exactly the statuses that assert Lean content
name a Lean declaration; there is no way to file one without the other. -/
theorem leanName?_isSome_iff (s : ProofStatus) :
    (leanName? s).isSome = carriesLeanReceipt s := by
  cases s <;> rfl

/-- A source receipt is never a Lean receipt: having the paper is not having the
proof. -/
theorem sourceReceipt_carries_no_lean_receipt (i : Ident) :
    carriesLeanReceipt (.sourceReceipt i) = false := rfl

/-- A conjecture, however well sourced, is never a Lean receipt. -/
theorem conjectural_carries_no_lean_receipt (w : String) :
    carriesLeanReceipt (.conjectural w) = false := rfl

/-- A false-pinned ledger flag is not a receipt either — in the corpus it is an
*explicit record of non-payment*. -/
theorem falsePinned_carries_no_lean_receipt (f : String) :
    carriesLeanReceipt (.falsePinned f) = false := rfl

/-! ## 4.  Claims, and the firewall -/

/-- A claim: a statement, its status, and the sources attached to it. -/
structure Claim where
  statement : String
  status : ProofStatus
  provenance : List SourceRecord
  deriving DecidableEq, Repr

/-- Re-attribute a claim to a different source set. -/
def reprovenance (c : Claim) (p : List SourceRecord) : Claim := { c with provenance := p }

/-- **Firewall, part 1.**  Changing the sources attached to a claim changes
nothing about its proof status.  Identifiers supply identity, classification and
provenance; they do not move a claim between status classes. -/
@[simp] theorem status_invariant_under_reprovenance (c : Claim) (p : List SourceRecord) :
    (reprovenance c p).status = c.status := rfl

/-- **Firewall, part 2.**  There is no function computing a claim's proof status
from its provenance.  This is the precise sense in which an identifier carries
no mathematical authority: the two claims below differ in status while citing
exactly the same (empty) source list. -/
theorem provenance_does_not_determine_status :
    ¬ ∃ f : List SourceRecord → ProofStatus, ∀ c : Claim, c.status = f c.provenance := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨"s", .provedTheorem "T", []⟩
  have h₂ := hf ⟨"s", .openPayment "T", []⟩
  simp only at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-- The same, with a fully well-formed DOI/QID/Dewey provenance rather than an
empty one: the obstruction is not an artefact of citing nothing. -/
theorem wellFormed_provenance_does_not_determine_status :
    ∃ p : List SourceRecord,
      p.all (fun r => wellFormed r.ident) = true ∧
      ∃ c₁ c₂ : Claim,
        c₁.provenance = p ∧ c₂.provenance = p ∧
        carriesLeanReceipt c₁.status = true ∧ carriesLeanReceipt c₂.status = false := by
  refine ⟨[⟨⟨.doi, "10.1090/S0002-9904"⟩, .acquired, ""⟩, ⟨⟨.qid, "Q42"⟩, .acquired, ""⟩,
           ⟨⟨.dewey, "641.5"⟩, .citedNotAcquired, ""⟩], by decide, ?_⟩
  exact ⟨⟨"s", .provedTheorem "T", _⟩, ⟨"s", .conjectural "T", _⟩, rfl, rfl, rfl, rfl⟩

/-- **Firewall, part 3, the other direction.**  A proved theorem needs no
identifier at all: provenance is not necessary for mathematical status, just as
it is not sufficient. -/
theorem receipt_without_provenance :
    ∃ c : Claim, carriesLeanReceipt c.status = true ∧ c.provenance = [] :=
  ⟨⟨"s", .provedTheorem "T", []⟩, rfl, rfl⟩

/-- Acquisition status is likewise independent: a retracted, unobtained source
set is compatible with a proved claim, and an acquired one with an open
payment.  (Both are bad practice; neither is a type error, which is exactly why
the ledger keeps the two columns apart.) -/
theorem acquisition_does_not_determine_status :
    (∃ c : Claim, carriesLeanReceipt c.status = true ∧
        c.provenance.all (fun r => r.status = SourceStatus.retracted) = true) ∧
    (∃ c : Claim, carriesLeanReceipt c.status = false ∧
        c.provenance.all (fun r => r.status = SourceStatus.acquired) = true) := by
  constructor
  · exact ⟨⟨"s", .provedTheorem "T", [⟨⟨.doi, "10.1/x"⟩, .retracted, ""⟩]⟩, rfl, by decide⟩
  · exact ⟨⟨"s", .openPayment "T", [⟨⟨.doi, "10.1/x"⟩, .acquired, ""⟩]⟩, rfl, by decide⟩

end Integration.ProvenanceId
