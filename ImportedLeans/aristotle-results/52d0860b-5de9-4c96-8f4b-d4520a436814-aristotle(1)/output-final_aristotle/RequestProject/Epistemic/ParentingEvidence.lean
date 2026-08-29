import RequestProject.Wikidata.ParentingAuthority
import RequestProject.Epistemic.Trit

/-!
# Parenthood claims as evidence

The parent surfaces of `RequestProject.Wikidata.Parenting` join the evidence
discipline of the rest of the development: every importable parenthood claim
comes with an exact checker (`ParentClaim.check_iff`), so support is backed
(`ParentCertificate.holds_of_supported`) and import is fail-closed
(`ParentCertificate.state_ne_contradicted`) while a checker failure is still a
certified negative *about this knowledge base*.

Three boundaries are then proved rather than assumed:

* **recorded is not genetic** — a supported recorded-descent certificate sits
  happily beside a refuted genetic-descent claim
  (`recorded_support_does_not_license_genetic`);
* **the cap is not exact-two** — a supported genetic-cap certificate is
  compatible with a single recorded genetic parent (`cap_support_is_not_two`);
* **evidence is not a mandate** — full support for a parenthood claim coexists
  with there being no current delegated authority
  (`support_does_not_confer_authority`), and no evidence about the public slot
  can decide the authority route (`slot_evidence_cannot_route_authority`).
-/

namespace Epistemic

open Wikidata

/-- The parenthood claims the bridge can import. -/
inductive ParentClaim
  | recordedDescent (a b : Qid)
  | geneticDescent (a b : Qid)
  | geneticCap (x : Qid)
  deriving DecidableEq, Repr, Inhabited

namespace ParentClaim

/-- What a parenthood claim means, relative to a knowledge base. -/
def Holds (kb : KB) : ParentClaim → Prop
  | recordedDescent a b => DescendsFrom kb a b
  | geneticDescent a b => GeneticDescendsFrom kb a b
  | geneticCap x => SingleGeneticSlots kb x

/-- The executable checker for a parenthood claim. -/
def check (kb : KB) : ParentClaim → Bool
  | recordedDescent a b => descendsFrom kb a b
  | geneticDescent a b => geneticDescendsFrom kb a b
  | geneticCap x =>
      decide ((truthyValues kb x P22).length ≤ 1) && decide ((truthyValues kb x P25).length ≤ 1)

/-- **Checker exactness on the parent surfaces.** -/
theorem check_iff (kb : KB) (cl : ParentClaim) : cl.check kb = true ↔ cl.Holds kb := by
  cases cl with
  | recordedDescent a b => exact descendsFrom_iff kb a b
  | geneticDescent a b => exact geneticDescendsFrom_iff kb a b
  | geneticCap x =>
      simp only [check, Holds, SingleGeneticSlots, Bool.and_eq_true, decide_eq_true_eq]

theorem not_holds_of_check_false {kb : KB} {cl : ParentClaim} (h : cl.check kb = false) :
    ¬ cl.Holds kb := by
  intro hc
  rw [(check_iff kb cl).2 hc] at h
  exact Bool.noConfusion h

end ParentClaim

/-- An imported parenthood result. -/
structure ParentCertificate where
  /-- The knowledge base the claim is about. -/
  kb : KB
  /-- The claim. -/
  claim : ParentClaim
  /-- Did the pinned source snapshot match? -/
  sourceMatched : Bool
  /-- Source references. -/
  references : List String

namespace ParentCertificate

/-- Did the checker accept? -/
def accepted (cert : ParentCertificate) : Bool := cert.claim.check cert.kb

/-- Fail-closed evidence state. -/
def state (cert : ParentCertificate) : Trit := receiptState cert.sourceMatched cert.accepted

theorem state_eq_supported_iff (cert : ParentCertificate) :
    cert.state = Trit.supported ↔ cert.sourceMatched = true ∧ cert.claim.Holds cert.kb := by
  rw [state, receiptState_eq_supported_iff]
  exact and_congr_right fun _ => ParentClaim.check_iff cert.kb cert.claim

/-- **Supported parenthood evidence is really backed.** -/
theorem holds_of_supported {cert : ParentCertificate} (h : cert.state = Trit.supported) :
    cert.claim.Holds cert.kb :=
  ((state_eq_supported_iff cert).1 h).2

/-- **Fail-closed import** on the parent surfaces. -/
theorem state_ne_contradicted (cert : ParentCertificate) : cert.state ≠ Trit.contradicted :=
  receiptState_ne_contradicted _ _

/-- A checker failure is a certified negative about this knowledge base. -/
theorem not_holds_of_check_false {cert : ParentCertificate} (h : cert.accepted = false) :
    ¬ cert.claim.Holds cert.kb :=
  ParentClaim.not_holds_of_check_false h

end ParentCertificate

/-! ## Boundaries -/

/-- **Recorded parenthood is not genetic parenthood**: the recorded-descent claim
is supported for the donor-conception knowledge base while the genetic-descent
claim is refuted for it. -/
theorem recorded_support_does_not_license_genetic :
    (⟨donorKB, ParentClaim.recordedDescent ⟨100⟩ ⟨103⟩, true, ["registry"]⟩ :
        ParentCertificate).state = Trit.supported ∧
      ¬ (ParentClaim.geneticDescent ⟨100⟩ ⟨103⟩).Holds donorKB := by
  constructor
  · rw [ParentCertificate.state_eq_supported_iff]
    exact ⟨rfl, (descendsFrom_iff donorKB ⟨100⟩ ⟨103⟩).1 (by decide)⟩
  · exact ParentClaim.not_holds_of_check_false (by decide)

/-- **The cap is not exact-two**: the genetic-cap claim is supported for a
knowledge base with a single recorded genetic parent. -/
theorem cap_support_is_not_two :
    (⟨donorKB, ParentClaim.geneticCap ⟨101⟩, true, ["registry"]⟩ :
        ParentCertificate).state = Trit.supported ∧
      (geneticParentsF donorKB ⟨101⟩).length = 1 := by
  constructor
  · rw [ParentCertificate.state_eq_supported_iff]
    refine ⟨rfl, ?_⟩
    exact (ParentClaim.check_iff donorKB (ParentClaim.geneticCap ⟨101⟩)).1 (by decide)
  · decide

/-- **Evidence is not a mandate**: a fully supported parenthood claim is
compatible with there being no current delegated authority. -/
theorem support_does_not_confer_authority :
    (⟨donorKB, ParentClaim.recordedDescent ⟨100⟩ ⟨101⟩, true, ["registry"]⟩ :
        ParentCertificate).state = Trit.supported ∧
      Authority.currentAuthority Wikidata.Parenting.revokedHistory
        Wikidata.Parenting.parentMandate = false := by
  constructor
  · rw [ParentCertificate.state_eq_supported_iff]
    exact ⟨rfl, (descendsFrom_iff donorKB ⟨100⟩ ⟨101⟩).1 (by decide)⟩
  · decide

/-- **No evidence about the public slot can decide the authority route.**  The
route is a function of the fine carrier that provably does not factor through the
slot, so a slot-level certificate — however well supported — cannot determine
it. -/
theorem slot_evidence_cannot_route_authority :
    ¬ FactorsThrough ParentCarrier.projectSlot Wikidata.Parenting.routeAuthority :=
  Wikidata.Parenting.route_not_factorsThrough

end Epistemic
