import Integration.Kernel.AppendOnlyHistory
import RequestProject.Archive
import RequestProject.Sync

/-!
# Aristotle instantiation: content identity, revision identity, alignment

Four coordinates that publication pipelines routinely conflate are kept apart
here, each with the archive's own machinery behind it:

* **content identity** — the digest of the canonical export
  (`RequestProject.Archive.digestOf` of `RequestProject.Publish.jsonlOfKB`);
* **revision identity** — which revision the answer was read at;
* **semantic equivalence** — mutual entailment of the derived facts
  (`RequestProject.Sync`'s `KB.Equiv`);
* **revision alignment** — whether an alignment receipt has been obtained, which
  is an event in an append-only history
  (`Integration.Kernel.AppendOnlyHistory`).

## What is proved

* **`same_canonical_content_gives_same_content_identity`** — the one implication
  that does hold, general in the two bases.
* **`semantic_equivalence_does_not_give_content_identity`** — two replicas that
  entail each other, hence answer every derived question identically, with
  different content digests.  Content identity is finer than semantics.
* **`content_identity_does_not_give_revision_identity`** — the same content
  published as two revisions: the digest cannot distinguish them, so a content
  digest is not an authority or provenance statement.
* **`later_receipt_is_not_earlier_possession`** — non-retroactivity: an
  alignment receipt present in the later history is absent from the earlier one,
  although the later history extends it.  Obtaining a receipt now does not make
  the earlier state have been aligned.
* `correction_appends_rather_than_rewrites` — the append-only discipline for
  corrections, instantiated on alignment events.

**Claim boundary.**  `replicaA`, `replicaB` and the two revisions are finite
fixtures defined here; `digestOf`, `jsonlOfKB`, `Entails` and `Equiv` are the
archive's, and `Extends` is the kernel's.  A digest agreement is a statement
about these exports only.
-/

namespace Integration.Kernel.Aristotle.ContentIdentityRevisionSync

open Integration.Kernel

/-! ## §1 The four coordinates -/

/-- The content identity of a knowledge base: the digest of its canonical
export. -/
def contentIdentity (kb : Wikidata.KB) : String :=
  Wikidata.Archive.digestOf (Wikidata.Publish.jsonlOfKB kb)

/-- A published revision: an identifier and the base published at it. -/
structure Revision where
  /-- The revision identifier. -/
  rev : ℕ
  /-- The knowledge base published at that revision. -/
  content : Wikidata.KB
deriving Repr, DecidableEq, Inhabited

/-- **Same canonical content, same content identity.**  General in the bases:
the digest is a function of the export. -/
theorem same_canonical_content_gives_same_content_identity {kb kb' : Wikidata.KB}
    (h : Wikidata.Publish.jsonlOfKB kb = Wikidata.Publish.jsonlOfKB kb') :
    contentIdentity kb = contentIdentity kb' :=
  congrArg Wikidata.Archive.digestOf h

/-! ## §2 Semantics is not content -/

/-- A replica asserting `a ⊑ b` and `b ⊑ c`. -/
def replicaA : Wikidata.KB where
  name := "replica"
  items := [.wd "Q1", .wd "Q2", .wd "Q3"]
  levels := [(.wd "Q1", 1), (.wd "Q2", 1), (.wd "Q3", 1)]
  sub := [(.wd "Q1", .wd "Q2"), (.wd "Q2", .wd "Q3")]

/-- A replica asserting the same two edges and, redundantly, the derived edge
`a ⊑ c`. -/
def replicaB : Wikidata.KB where
  name := "replica"
  items := [.wd "Q1", .wd "Q2", .wd "Q3"]
  levels := [(.wd "Q1", 1), (.wd "Q2", 1), (.wd "Q3", 1)]
  sub := [(.wd "Q1", .wd "Q2"), (.wd "Q2", .wd "Q3"), (.wd "Q1", .wd "Q3")]

set_option maxRecDepth 40000 in
theorem replicas_are_equivalent : Wikidata.KB.Equiv replicaA replicaB = true := by decide

set_option maxRecDepth 40000 in
/-- **Semantic equivalence does not give content identity.**  The two replicas
answer every derived subclass and instance question identically and export
different bytes, hence different digests. -/
theorem semantic_equivalence_does_not_give_content_identity :
    Wikidata.KB.Equiv replicaA replicaB = true ∧
    contentIdentity replicaA ≠ contentIdentity replicaB := by
  refine ⟨replicas_are_equivalent, ?_⟩
  decide

/-! ## §3 Content is not authority -/

/-- The same content published at two revisions. -/
def revisionOne : Revision := ⟨17, replicaA⟩

/-- The later revision of the same content. -/
def revisionTwo : Revision := ⟨23, replicaA⟩

/-- **Content identity does not give revision identity.**  The digest is blind
to which revision a reader was looking at, so it carries no authority or
currency claim. -/
theorem content_identity_does_not_give_revision_identity :
    contentIdentity revisionOne.content = contentIdentity revisionTwo.content ∧
    revisionOne.rev ≠ revisionTwo.rev := by
  refine ⟨rfl, by decide⟩

/-! ## §4 Non-retroactivity of alignment receipts -/

/-- The events an alignment history records. -/
inductive Ev where
  /-- The base was published at a revision. -/
  | published (rev : ℕ)
  /-- An alignment receipt was obtained for a revision. -/
  | aligned (rev : ℕ)
  /-- A correction was issued for a revision. -/
  | corrected (rev : ℕ)
deriving DecidableEq, Repr, Inhabited

/-- The history as it stood earlier: published, not yet aligned. -/
def earlier : AppendOnlyHistory.History Ev := [Ev.published 17]

/-- The history after the alignment receipt arrives. -/
def later : AppendOnlyHistory.History Ev :=
  AppendOnlyHistory.append earlier (Ev.aligned 17)

/-- **A later receipt is not earlier possession.**  The alignment event is in
the later history and not in the earlier one, although the later history extends
the earlier: obtaining the receipt now does not make the earlier state have been
aligned. -/
theorem later_receipt_is_not_earlier_possession :
    Ev.aligned 17 ∈ later ∧ Ev.aligned 17 ∉ earlier ∧
    AppendOnlyHistory.Extends later earlier := by
  refine ⟨by decide, by decide, AppendOnlyHistory.append_extends earlier _⟩

/-- Corrections append rather than rewrite: everything the earlier history
recorded is still recorded after a correction. -/
theorem correction_appends_rather_than_rewrites :
    Ev.published 17 ∈ AppendOnlyHistory.append later (Ev.corrected 17) :=
  AppendOnlyHistory.correction_does_not_erase (by decide) _

end Integration.Kernel.Aristotle.ContentIdentityRevisionSync
