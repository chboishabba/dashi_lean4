import Integration.Kernel.PromotionTransport
import RequestProject.Ranks
import RequestProject.Provenance

/-!
# Aristotle capstone: strand-indexed promotion over the two evidence planes

This is the capstone of the Aristotle reciprocal tranche.  It puts the two
evidence planes of the Wikidata architecture side by side —

* the **native plane**: statements with ranks, read through the archive's truthy
  semantics (`RequestProject.Ranks`);
* the **graph plane**: `instance of` / `subclass of` derivation through the
  archive's engine (`RequestProject.Engine`, via `RequestProject.Provenance`);

adds a **review** strand and a **policy** strand, and asks which of the four
promotion obligations of `Integration.Kernel.PromotionTransport` each strand can
pay.  Strand-local obligations compile into an ordinary promotion receipt, and
the receipt forgets which strand paid what.

## What is proved

Four firewalls, each with an exact witness:

* **`native_receipt_does_not_give_graph_completeness`** — a truthy native
  statement about the subject, and a typing question the graph plane cannot
  answer positively.
* **`graph_soundness_does_not_give_native_semantics`** — the graph derives a
  typing fact for which **no** truthy native statement exists (the only native
  statement asserting it is deprecated).
* **`peer_exact_does_not_give_policy_authority`** — a peer cohort assessment is
  inhabited while the migration-authority carrier of the same fixture is empty.
* **`full_receipt_does_not_determine_provenance_assignment`** — the strongest
  one: two *different* strand assignments discharge the same four obligations
  and compile to the same receipt, so **no** function from receipts to
  assignments is a left inverse of compilation.  A logical proof of promotion
  does not say who supplied each evidentiary strand.

And the positive direction:

* `strand_assignment_compiles_to_receipt` — four typed strand-local obligations
  assemble a `PromotionTransport.Receipt` for the typing statement.

**Claim boundary.**  `nativeClaims`, `graphModule`, `fullGraph`, the strand
table `canPay`, `PeerAssessment` and `PolicyAuthority` are finite fixtures
defined in this file; `PolicyAuthority` is *stipulated* empty (this fixture
grants no migration authority) and nothing here establishes any real
authority relation.  The truthy semantics and the derivation engine are the
archive's.
-/

namespace Integration.Kernel.Aristotle.WikibaseZelphBraidedPromotion

open Integration.Kernel

/-! ## §1 The two evidence planes -/

/-- Douglas Adams, as a label. -/
def adams : Wikidata.Qid := .wd "Q42"
/-- human, as a label. -/
def human : Wikidata.Qid := .wd "Q5"
/-- person, as a label. -/
def person : Wikidata.Qid := .wd "Q215627"
/-- agent, as a label. -/
def agent : Wikidata.Qid := .wd "Q24229398"
/-- `instance of`, as a label. -/
def p31 : Wikidata.Pid := .wd "P31"

/-- The native plane: one normal `instance of human` statement and one
*deprecated* `instance of person` statement for the same subject and property. -/
def nativeClaims : Wikidata.Claim.Set :=
  [ { subject := adams, pid := p31, value := .item human },
    { subject := adams, pid := p31, value := .item person, rank := .deprecated } ]

/-- The graph plane: `human ⊑ person`, Adams an instance of `human`; the edge
`person ⊑ agent` has been pruned away by the routing policy. -/
def graphModule : Wikidata.KB where
  name := "routed graph plane"
  items := [adams, human, person, agent]
  levels := [(adams, 0), (human, 1), (person, 1), (agent, 1)]
  sub := [(human, person)]
  inst := [(adams, human)]

/-- The unpruned graph, for comparison. -/
def fullGraph : Wikidata.KB where
  name := "unpruned graph plane"
  items := [adams, human, person, agent]
  levels := [(adams, 0), (human, 1), (person, 1), (agent, 1)]
  sub := [(human, person), (person, agent)]
  inst := [(adams, human)]

/-! ## §2 Firewall: native statement receipt ⇏ graph completeness -/

/-- The native `instance of human` statement is truthy. -/
theorem native_human_is_truthy :
    ({ subject := adams, pid := p31, value := .item human } : Wikidata.Claim)
      ∈ Wikidata.Claim.truthy nativeClaims := by decide

/-- **A native statement receipt does not give graph completeness.**  The native
plane carries a truthy typing statement about the subject while the graph plane
answers a further typing question negatively, although it holds unpruned. -/
theorem native_receipt_does_not_give_graph_completeness :
    ({ subject := adams, pid := p31, value := .item human } : Wikidata.Claim)
      ∈ Wikidata.Claim.truthy nativeClaims ∧
    graphModule.isInstanceOf adams agent = false ∧
    fullGraph.isInstanceOf adams agent = true :=
  ⟨native_human_is_truthy, by decide, by decide⟩

/-! ## §3 Firewall: graph soundness ⇏ native statement semantics -/

/-- **Graph soundness does not give native statement semantics.**  The graph
plane derives that Adams is a person, while no truthy native statement asserts
it: the only native statement that does is deprecated, so the native plane's
rank semantics is not readable off the graph plane. -/
theorem graph_soundness_does_not_give_native_semantics :
    graphModule.isInstanceOf adams person = true ∧
    ∀ c ∈ Wikidata.Claim.truthy nativeClaims,
      ¬ (c.subject = adams ∧ c.value = Wikidata.Value.item person) := by
  refine ⟨by decide, ?_⟩
  decide

/-! ## §4 Firewall: peer assessment ⇏ policy authority -/

/-- A peer cohort assessment token. -/
inductive PeerAssessment where
  /-- The cohort assessed the item as an exact peer match. -/
  | exactMatch
deriving DecidableEq, Repr, Inhabited

/-- The migration-authority carrier of this fixture, which grants nothing. -/
def PolicyAuthority : Type := Empty

/-- **A peer-exact assessment is not policy authority.**  The assessment carrier
is inhabited and the authority carrier of the same fixture is empty; nothing
maps the one into the other. -/
theorem peer_exact_does_not_give_policy_authority :
    Nonempty PeerAssessment ∧ IsEmpty PolicyAuthority :=
  ⟨⟨PeerAssessment.exactMatch⟩, inferInstanceAs (IsEmpty Empty)⟩

/-! ## §5 Strand-indexed promotion -/

/-- The four evidentiary strands of the braid. -/
inductive Strand where
  /-- Native statements: GUID, snak, rank, qualifiers, references. -/
  | native
  /-- The routed graph: `P31`/`P279`, bounded adjacency. -/
  | graph
  /-- Trusted-cohort review. -/
  | review
  /-- Migration / promotion policy. -/
  | policy
deriving DecidableEq, Repr, Inhabited

/-- The four promotion obligations. -/
inductive Obligation where
  /-- An artefact exists. -/
  | artifact
  /-- It corresponds to the statement. -/
  | correspondence
  /-- The transport is sound. -/
  | transport
  /-- The target is inhabited. -/
  | inhabitance
deriving DecidableEq, Repr, Inhabited

/-- Which strand is *able* to pay which obligation in this architecture.  Note
that the last obligation can be paid by either the review or the policy strand:
this is what makes the assignment underdetermined by the receipt. -/
def canPay : Strand → Obligation → Bool
  | .native, .artifact => true
  | .native, .correspondence => true
  | .graph, .transport => true
  | .review, .inhabitance => true
  | .policy, .inhabitance => true
  | _, _ => false

/-- An assignment of obligations to strands. -/
def Assignment : Type := Obligation → Strand

/-- An assignment discharges the braid when every obligation is given to a
strand that can pay it. -/
def Discharges (A : Assignment) : Prop := ∀ o, canPay (A o) o = true

/-- The assignment in which the review strand pays inhabitance. -/
def reviewAssignment : Assignment
  | .artifact => .native
  | .correspondence => .native
  | .transport => .graph
  | .inhabitance => .review

/-- The assignment in which the policy strand pays inhabitance instead. -/
def policyAssignment : Assignment
  | .artifact => .native
  | .correspondence => .native
  | .transport => .graph
  | .inhabitance => .policy

theorem reviewAssignment_discharges : Discharges reviewAssignment := by
  intro o; cases o <;> rfl

theorem policyAssignment_discharges : Discharges policyAssignment := by
  intro o; cases o <;> rfl

theorem assignments_differ : reviewAssignment ≠ policyAssignment := by
  intro h
  have := congrFun h Obligation.inhabitance
  exact absurd this (by decide)

/-! ## §6 Compilation into an ordinary receipt -/

/-- The promotion frame across the two planes: the artefact is a truthy native
statement, the statement it corresponds to is the typing pair it asserts, and
the target holds when the graph plane derives that pair. -/
def braidFrame : PromotionTransport.Frame where
  Artifact := { c : Wikidata.Claim // c ∈ Wikidata.Claim.truthy nativeClaims }
  Statement := Wikidata.Qid × Wikidata.Qid
  Target := Wikidata.Qid × Wikidata.Qid
  Term := Unit
  claims a :=
    (a.1.subject,
      match a.1.value with
      | .item q => q
      | _ => a.1.subject)
  transport := id
  Holds g := graphModule.isInstanceOf g.1 g.2 = true
  Inhabits _ g := graphModule.isInstanceOf g.1 g.2 = true

/-- The transport precondition: the graph plane answers the typing question. -/
def GraphAnswers (s : braidFrame.Statement) : Prop :=
  graphModule.isInstanceOf s.1 s.2 = true

theorem braidFrame_transport_sound :
    PromotionTransport.TransportSound braidFrame GraphAnswers := fun _ hs => hs

/-- **Four typed strand-local obligations compile to an ordinary promotion
receipt.**  The assignment is what licenses the four fields; the receipt itself
is an ordinary `PromotionTransport.Receipt`. -/
def compile (A : Assignment) (_ : Discharges A) :
    PromotionTransport.Receipt braidFrame GraphAnswers (adams, human) where
  artifact := ⟨{ subject := adams, pid := p31, value := .item human }, native_human_is_truthy⟩
  corresponds := rfl
  source := show graphModule.isInstanceOf adams human = true by decide
  sound := braidFrame_transport_sound
  term := ()
  inhabits := show graphModule.isInstanceOf adams human = true by decide

theorem strand_assignment_compiles_to_receipt :
    Nonempty (PromotionTransport.Receipt braidFrame GraphAnswers (adams, human)) :=
  ⟨compile reviewAssignment reviewAssignment_discharges⟩

/-- Compilation forgets the assignment: the two different discharging
assignments produce literally the same receipt. -/
theorem compile_forgets_assignment :
    compile reviewAssignment reviewAssignment_discharges
      = compile policyAssignment policyAssignment_discharges := rfl

/-- **A full promotion receipt does not determine the provenance assignment.**
No function from receipts to assignments recovers who paid which obligation:
two distinct discharging assignments compile to the same receipt. -/
theorem full_receipt_does_not_determine_provenance_assignment :
    ¬ ∃ f : PromotionTransport.Receipt braidFrame GraphAnswers (adams, human) → Assignment,
        ∀ A, ∀ h : Discharges A, f (compile A h) = A := by
  rintro ⟨f, hf⟩
  have h₁ := hf reviewAssignment reviewAssignment_discharges
  have h₂ := hf policyAssignment policyAssignment_discharges
  rw [compile_forgets_assignment] at h₁
  exact assignments_differ (h₁.symm.trans h₂)

/-- The capstone, assembled: the promotion goes through, and none of the four
collapses is available. -/
theorem braided_promotion_without_collapse :
    Nonempty (PromotionTransport.Receipt braidFrame GraphAnswers (adams, human)) ∧
    graphModule.isInstanceOf adams agent = false ∧
    (∀ c ∈ Wikidata.Claim.truthy nativeClaims,
      ¬ (c.subject = adams ∧ c.value = Wikidata.Value.item person)) ∧
    IsEmpty PolicyAuthority ∧
    ¬ ∃ f : PromotionTransport.Receipt braidFrame GraphAnswers (adams, human) → Assignment,
        ∀ A, ∀ h : Discharges A, f (compile A h) = A :=
  ⟨strand_assignment_compiles_to_receipt,
   native_receipt_does_not_give_graph_completeness.2.1,
   graph_soundness_does_not_give_native_semantics.2,
   peer_exact_does_not_give_policy_authority.2,
   full_receipt_does_not_determine_provenance_assignment⟩

end Integration.Kernel.Aristotle.WikibaseZelphBraidedPromotion
