import Integration.Kernel.EvidenceDependence
import Integration.Kernel.Bridges.QuorumThreshold
import RequestProject.Provenance

/-!
# Aristotle instantiation: `full ⊇ sourced ⊇ reliable` and consumer adequacy

The generic owners `Integration.Kernel.EvidenceDependence` (support counted by
*roots*, not by items) and `Integration.Kernel.Bridges.QuorumThreshold` (a quorum
by headcount is not a quorum by independent provenance) had, until now, only
stipulated provenance assignments.  This file gives them the archive's real
Wikidata reference semantics from `RequestProject.Provenance`, where a statement
carries a list of `Ref`s, `imported from Wikimedia project` is explicitly *not*
a source, and the three knowledge bases

  `full ⊇ sourced ⊇ reliable`

are obtained by selecting on the reference list.

## What is proved

* `refRoots`, `supportProvenance` — the provenance assignment induced by the
  archive's `Ref`: a `stated in` reference is rooted at the work cited, a
  `reference URL` at the URL, and an `imported from` note contributes **no**
  root at all.
* **`counts_come_apart`** — on one statement's reference list:
  visible support `3`, source-bearing support `2`, independent reliable roots
  `1`.  So `count_full = n` does not entail `independentReliableSupport = n`.
* **`two_visible_refs_are_not_independent`** — the two source-bearing references
  cite the same work, hence are not `EvidenceDependence.Independent`.
* **`headcount_quorum_is_not_reliable_quorum`** — with a quorum of two: the
  visible headcount clears it, the independent reliable root count does not.
* **`pattern_in_full_absent_in_reliable`** — the archive-side version, on a real
  `RKB`: a derived `instance of` fact holds in `full` and in `sourced` and fails
  in `reliable`, because its only reference is an `imported from` note.  It is
  a typed residual, not a confidence discount.
* `reliable_le_sourced_le_full_on_fixture` — the tier inclusion, checked on the
  fixture, and `adequacy_policy_separates`: one and the same body of evidence is
  adequate for a `sourced` consumer and inadequate for a `reliable` consumer.

**Claim boundary.**  `cohort`, `supportRefs` and the two policies are finite
fixtures defined in this file; the reference semantics, the `select`/`full`/
`sourced`/`reliable` tiers and the derivation engine are the archive's.  No
claim is made about any real statement in Wikidata.
-/

namespace Integration.Kernel.Aristotle.ReliableSourceConsumerAdequacy

open Integration.Kernel

/-! ## §1 References as provenance roots -/

/-- The provenance roots of a Wikidata reference: the work cited by a
`stated in`, the URL cited by a `reference URL`, and **nothing** for an
`imported from Wikimedia project` note, which the archive already classifies as
not a source. -/
def refRoots (r : Wikidata.Ref) : Finset Wikidata.Qid :=
  match r.kind with
  | .statedIn => {r.source}
  | .referenceURL => {Wikidata.Qid.wd r.url}
  | .importedFrom => ∅

/-- The reference list of the fixture statement: one `imported from` note and
two source-bearing references that cite **the same** work. -/
def supportRefs : List Wikidata.Ref :=
  [ { kind := .importedFrom, source := .wd "Q328" },
    { kind := .statedIn, source := .wd "Q36578" },
    { kind := .statedIn, source := .wd "Q36578", url := "second row" } ]

/-- Visible support: how many reference rows there are. -/
def visibleCount : ℕ := supportRefs.length

/-- Source-bearing support: how many rows count as a source at all. -/
def reliableCount : ℕ := (supportRefs.filter (fun r => r.kind.reliable)).length

/-- The union of the provenance roots of the source-bearing rows. -/
def reliableRoots : Finset Wikidata.Qid :=
  supportRefs.foldr (fun r acc => refRoots r ∪ acc) ∅

/-- Independent reliable support: the number of distinct roots. -/
def independentReliableCount : ℕ := reliableRoots.card

/-- **The three counts come apart.**  Three visible reference rows, two of them
source-bearing, resting on a single independent root. -/
theorem counts_come_apart :
    visibleCount = 3 ∧ reliableCount = 2 ∧ independentReliableCount = 1 := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- In particular a visible count of `n` does not give independent reliable
support `n`. -/
theorem visible_count_does_not_give_independent_support :
    visibleCount ≠ independentReliableCount := by
  simp [visibleCount, independentReliableCount, supportRefs, reliableRoots, refRoots]

/-! ## §2 The generic owner, instantiated -/

/-- The three reference rows as evidence items, with the archive's roots. -/
def supportProvenance : EvidenceDependence.Provenance (Fin 3) Wikidata.Qid :=
  ⟨fun i => refRoots (supportRefs.getD i default)⟩

/-- **The two source-bearing rows are not independent**: they cite the same
work, so `EvidenceDependence.Independent` fails for them. -/
theorem two_visible_refs_are_not_independent :
    ¬ EvidenceDependence.Independent supportProvenance 1 2 := by
  intro h
  have hshared : EvidenceDependence.SharesRoot supportProvenance 1 2 := by
    refine ⟨Wikidata.Qid.wd "Q36578", ?_, ?_⟩ <;> decide
  exact EvidenceDependence.not_independent_iff_sharesRoot.2 hshared h

/-- The `imported from` note contributes no root at all, so it is vacuously
independent of everything — including of itself. -/
theorem imported_from_contributes_no_root :
    supportProvenance.rootsOf 0 = ∅ := rfl

/-! ## §3 Quorum: headcount versus independent provenance -/

/-- The quorum a consumer demands. -/
def quorum : ℕ := 2

/-- **A headcount quorum is not a reliable-provenance quorum.**  Two visible
source-bearing rows clear the threshold; the independent reliable support does
not. -/
theorem headcount_quorum_is_not_reliable_quorum :
    quorum ≤ reliableCount ∧ ¬ quorum ≤ independentReliableCount := by
  refine ⟨by decide, ?_⟩
  intro h
  rw [counts_come_apart.2.2] at h
  exact absurd h (by decide)

/-! ## §4 The archive tiers on a real referenced knowledge base -/

/-- Douglas Adams, as a label. -/
def adams : Wikidata.Qid := .wd "Q42"
/-- human, as a label. -/
def human : Wikidata.Qid := .wd "Q5"
/-- person, as a label. -/
def person : Wikidata.Qid := .wd "Q215627"
/-- omnivore, as a label. -/
def omnivore : Wikidata.Qid := .wd "Q164509"

/-- A referenced knowledge base in which the class edge `human ⊑ person` has a
`stated in` reference, while `omnivore ⊑ person` rests only on an
`imported from` note. -/
def cohort : Wikidata.RKB where
  name := "reliable-source cohort"
  items := [adams, human, person, omnivore]
  levels := [(adams, 0), (human, 1), (person, 1), (omnivore, 1)]
  rsub :=
    [ ((human, person), [{ kind := .statedIn, source := .wd "Q36578" }]),
      ((omnivore, person), [{ kind := .importedFrom, source := .wd "Q328" }]) ]
  rinst :=
    [ ((adams, human), [{ kind := .referenceURL, url := "https://example.org/adams" }]),
      ((adams, omnivore), [{ kind := .importedFrom, source := .wd "Q328" }]) ]

/-- The fixture is a valid ontology, so the archive's tier lemmas apply. -/
theorem cohort_valid : cohort.full.valid = true := by decide

/-- **A pattern present in `full` and `sourced` disappears in `reliable`.**  The
derived fact "Adams is a person via omnivore" is asserted, is even
"verifiable" in the weak `sourced` sense, and is absent from the reliable
fragment, because an `imported from Wikimedia project` note is not a source. -/
theorem pattern_in_full_absent_in_reliable :
    cohort.full.isInstanceOf adams omnivore = true ∧
    cohort.sourced.isInstanceOf adams omnivore = true ∧
    cohort.reliable.isInstanceOf adams omnivore = false := by
  refine ⟨by decide, by decide, by decide⟩

/-- The tier inclusion, on the fixture: everything reliable is sourced and
everything sourced is asserted. -/
theorem reliable_le_sourced_le_full_on_fixture :
    (∀ x ∈ cohort.reliable.sub, x ∈ cohort.sourced.sub) ∧
    (∀ x ∈ cohort.sourced.sub, x ∈ cohort.full.sub) ∧
    (∀ x ∈ cohort.reliable.inst, x ∈ cohort.sourced.inst) ∧
    (∀ x ∈ cohort.sourced.inst, x ∈ cohort.full.inst) :=
  ⟨fun _ h => Wikidata.RKB.sub_of_mem_reliable_sub h,
   fun _ h => Wikidata.RKB.sub_of_mem_sourced_sub h,
   fun _ h => Wikidata.RKB.inst_of_mem_reliable_inst h,
   fun _ h => Wikidata.RKB.inst_of_mem_sourced_inst h⟩

/-! ## §5 Adequacy policies -/

/-- The provenance tier a consumer's adequacy policy demands. -/
inductive Tier where
  /-- Anything asserted counts. -/
  | full
  /-- A reference of any kind is required. -/
  | sourced
  /-- A reference that counts as a source is required. -/
  | reliable
deriving DecidableEq, Repr, Inhabited

/-- Whether the fixture's derived fact is adequate for a consumer at a tier. -/
def AdequateAt : Tier → Prop
  | .full => cohort.full.isInstanceOf adams omnivore = true
  | .sourced => cohort.sourced.isInstanceOf adams omnivore = true
  | .reliable => cohort.reliable.isInstanceOf adams omnivore = true

/-- **The same body of evidence is adequate for one consumer and not for
another.**  Adequacy is a property of the (evidence, policy) pair; it is not a
scalar attached to the evidence. -/
theorem adequacy_policy_separates :
    AdequateAt .full ∧ AdequateAt .sourced ∧ ¬ AdequateAt .reliable := by
  refine ⟨pattern_in_full_absent_in_reliable.1, pattern_in_full_absent_in_reliable.2.1, ?_⟩
  intro h
  rw [show AdequateAt .reliable = (cohort.reliable.isInstanceOf adams omnivore = true) from rfl]
    at h
  rw [pattern_in_full_absent_in_reliable.2.2] at h
  exact absurd h (by decide)

end Integration.Kernel.Aristotle.ReliableSourceConsumerAdequacy
