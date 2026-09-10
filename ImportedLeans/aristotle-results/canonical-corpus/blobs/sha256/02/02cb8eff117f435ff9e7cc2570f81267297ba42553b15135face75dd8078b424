import Integration.Kernel.PromotionTransport
import RequestProject.Provenance

/-!
# Aristotle instantiation: a pruned type module in the promotion transport chain

`Integration.Kernel.PromotionTransport` separates the four obligations of a
promotion — *an artefact exists*, *it corresponds to the statement*, *the
transport is sound*, *a term inhabits the target* — and proves that the first
three leave the fourth open.  This file instantiates that chain on a **pruned
Wikidata type module**: a knowledge base obtained from a larger one by dropping
edges, used to answer `instance of` / `subclass of` questions.

The point of the instantiation is the distinction the archive's engine makes
sharp and that a single "type module receipt" would flatten:

  a pruned module is **sound** for positive answers and **not complete**, so it
  can contribute subject typing and can never establish absence.

## What is proved

* `pruned_is_sound_for_instances` / `pruned_is_sound_for_subclasses` — **general
  soundness**, quantified over all `a c`, obtained from the archive's own
  monotonicity lemmas `KB.isInstanceOf_mono` / `KB.isSubclassOf_mono`; not a
  spot check.
* **`pruned_is_not_complete`** — an exact witness: a fact derivable in the full
  module and not in the pruned one.
* **`soundness_receipt_is_not_completeness_receipt`** — the two receipts as
  propositions: the soundness one is inhabited, the completeness one is not.
* **`absence_in_pruned_is_not_absence_in_full`** — the operational form: a
  negative answer from the pruned module is not a negative fact.
* `typeFrame`, `positive_answer_promotes` — the promotion chain instantiated: a
  positive answer of the pruned module is an artefact, corresponds to the typing
  statement, is transported soundly, and the target is inhabited, so a
  `PromotionTransport.Receipt` is assembled.
* **`negative_answer_does_not_promote`** — with the same frame and the negative
  reading of the same query, no receipt exists: the fourth obligation is not
  paid by soundness.

**Claim boundary.**  `fullModule` and `prunedModule` are finite knowledge bases
defined here.  The derivation engine, `wellFormed`, `isInstanceOf` and the
monotonicity lemmas are the archive's.  Nothing is claimed about the live
Wikidata class graph.
-/

namespace Integration.Kernel.Aristotle.PrunedGraphPromotionTransport

open Integration.Kernel

/-! ## §1 A full module and a pruned one -/

/-- Douglas Adams, as a label. -/
def adams : Wikidata.Qid := .wd "Q42"
/-- human, as a label. -/
def human : Wikidata.Qid := .wd "Q5"
/-- person, as a label. -/
def person : Wikidata.Qid := .wd "Q215627"
/-- agent, as a label. -/
def agent : Wikidata.Qid := .wd "Q24229398"

/-- The full type module: `human ⊑ person ⊑ agent`, with Adams an instance of
`human`. -/
def fullModule : Wikidata.KB where
  name := "full type module"
  items := [adams, human, person, agent]
  levels := [(adams, 0), (human, 1), (person, 1), (agent, 1)]
  sub := [(human, person), (person, agent)]
  inst := [(adams, human)]

/-- The pruned module: the `person ⊑ agent` edge has been dropped, for instance
by a bounded-adjacency routing policy. -/
def prunedModule : Wikidata.KB where
  name := "pruned type module"
  items := [adams, human, person, agent]
  levels := [(adams, 0), (human, 1), (person, 1), (agent, 1)]
  sub := [(human, person)]
  inst := [(adams, human)]

theorem fullModule_wellFormed : fullModule.wellFormed = true := by decide

theorem prunedModule_wellFormed : prunedModule.wellFormed = true := by decide

theorem pruned_sub_subset : ∀ x ∈ prunedModule.sub, x ∈ fullModule.sub := by decide

theorem pruned_inst_subset : ∀ x ∈ prunedModule.inst, x ∈ fullModule.inst := by decide

/-! ## §2 Soundness, in general -/

/-- **The pruned module is sound for subclass answers**, for *all* pairs: every
positive answer it gives is a positive answer of the full module.  This uses the
archive's monotonicity lemma, so it is not a finite check. -/
theorem pruned_is_sound_for_subclasses (a b : Wikidata.Qid)
    (h : prunedModule.isSubclassOf a b = true) : fullModule.isSubclassOf a b = true :=
  Wikidata.KB.isSubclassOf_mono fullModule_wellFormed prunedModule_wellFormed
    pruned_sub_subset h

/-- **The pruned module is sound for instance answers**, for all pairs. -/
theorem pruned_is_sound_for_instances (a c : Wikidata.Qid)
    (h : prunedModule.isInstanceOf a c = true) : fullModule.isInstanceOf a c = true :=
  Wikidata.KB.isInstanceOf_mono fullModule_wellFormed prunedModule_wellFormed
    pruned_sub_subset pruned_inst_subset h

/-! ## §3 …and the failure of completeness -/

/-- **The pruned module is not complete.**  Adams is an agent in the full module
and not in the pruned one. -/
theorem pruned_is_not_complete :
    fullModule.isInstanceOf adams agent = true ∧
    prunedModule.isInstanceOf adams agent = false := by
  refine ⟨by decide, by decide⟩

/-- The soundness obligation, as a proposition. -/
def SoundnessReceipt : Prop :=
  ∀ a c, prunedModule.isInstanceOf a c = true → fullModule.isInstanceOf a c = true

/-- The completeness obligation, as a proposition. -/
def CompletenessReceipt : Prop :=
  ∀ a c, fullModule.isInstanceOf a c = true → prunedModule.isInstanceOf a c = true

/-- **A soundness receipt is not a completeness receipt.**  The pruned module
pays the first obligation for every pair and fails the second. -/
theorem soundness_receipt_is_not_completeness_receipt :
    SoundnessReceipt ∧ ¬ CompletenessReceipt := by
  refine ⟨pruned_is_sound_for_instances, fun h => ?_⟩
  have := h adams agent pruned_is_not_complete.1
  rw [pruned_is_not_complete.2] at this
  exact absurd this (by decide)

/-- **A negative answer from the pruned module is not a negative fact.** -/
theorem absence_in_pruned_is_not_absence_in_full :
    prunedModule.isInstanceOf adams agent = false ∧
    fullModule.isInstanceOf adams agent ≠ false := by
  refine ⟨pruned_is_not_complete.2, ?_⟩
  rw [pruned_is_not_complete.1]
  decide

/-! ## §4 The promotion chain on the pruned module -/

/-- The promotion frame of the type module: an artefact is a *positive answer*
of the pruned module, the statement is the typing pair it asserts, the target is
that same typing claim about the full module, and a term is a proof that the
full module derives it. -/
def typeFrame : PromotionTransport.Frame where
  Artifact := { p : Wikidata.Qid × Wikidata.Qid // prunedModule.isInstanceOf p.1 p.2 = true }
  Statement := Wikidata.Qid × Wikidata.Qid
  Target := Wikidata.Qid × Wikidata.Qid
  Term := Unit
  claims a := a.1
  transport := id
  Holds g := fullModule.isInstanceOf g.1 g.2 = true
  Inhabits _ g := fullModule.isInstanceOf g.1 g.2 = true

/-- The precondition of the transport: the pruned module answers positively. -/
def PrunedAnswers (s : typeFrame.Statement) : Prop :=
  prunedModule.isInstanceOf s.1 s.2 = true

/-- The transport is sound exactly because §2 is a theorem about all pairs. -/
theorem typeFrame_transport_sound :
    PromotionTransport.TransportSound typeFrame PrunedAnswers := by
  intro s hs
  exact pruned_is_sound_for_instances s.1 s.2 hs

/-- Adams is an instance of `human` in the pruned module. -/
theorem adams_human_pruned : prunedModule.isInstanceOf adams human = true := by decide

/-- **A positive answer promotes.**  Artefact, correspondence, sound transport
and an inhabiting term: the full `PromotionTransport.Receipt` is assembled. -/
theorem positive_answer_promotes :
    Nonempty (PromotionTransport.Receipt typeFrame PrunedAnswers (adams, human)) :=
  PromotionTransport.receipt_exists_of_inhabitant
    (F := typeFrame) ⟨(adams, human), adams_human_pruned⟩ rfl adams_human_pruned
    typeFrame_transport_sound ()
    (show fullModule.isInstanceOf adams human = true by decide)

/-- The negative side of the same query, as a frame with no artefact and no
term: a pruned module that answers "no" offers nothing to promote. -/
def absenceFrame : PromotionTransport.Frame where
  Artifact := { p : Wikidata.Qid × Wikidata.Qid //
    prunedModule.isInstanceOf p.1 p.2 = false ∧ fullModule.isInstanceOf p.1 p.2 = false }
  Statement := Wikidata.Qid × Wikidata.Qid
  Target := Wikidata.Qid × Wikidata.Qid
  Term := Empty
  claims a := a.1
  transport := id
  Holds g := fullModule.isInstanceOf g.1 g.2 = false
  Inhabits _ g := fullModule.isInstanceOf g.1 g.2 = false

/-- **A negative answer does not promote.**  There is no receipt for the absence
claim about `(adams, agent)`: the pruned module's "no" is not evidence, and the
frame has no term to offer. -/
theorem negative_answer_does_not_promote :
    IsEmpty (PromotionTransport.Receipt absenceFrame
      (fun s => prunedModule.isInstanceOf s.1 s.2 = false) (adams, agent)) :=
  ⟨fun r => r.term.elim⟩

/-- The two halves side by side: soundness is paid for every pair, completeness
is not paid at all, and only the positive direction assembles a receipt. -/
theorem sound_positive_but_no_negative_completeness :
    SoundnessReceipt ∧ ¬ CompletenessReceipt ∧
    Nonempty (PromotionTransport.Receipt typeFrame PrunedAnswers (adams, human)) ∧
    IsEmpty (PromotionTransport.Receipt absenceFrame
      (fun s => prunedModule.isInstanceOf s.1 s.2 = false) (adams, agent)) :=
  ⟨soundness_receipt_is_not_completeness_receipt.1,
   soundness_receipt_is_not_completeness_receipt.2,
   positive_answer_promotes,
   negative_answer_does_not_promote⟩

end Integration.Kernel.Aristotle.PrunedGraphPromotionTransport
