import RequestProject.Wikidata.Rdf
import RequestProject.Wikidata.Identity
import RequestProject.Epistemic.Bridge

/-!
# Evidence over the constraint, RDF, parthood and identity surfaces

`RequestProject.Epistemic.Bridge` imports class facts as evidence.  The extra
surfaces extracted in `Constraints.lean`, `Rdf.lean` and `Identity.lean` need the
same discipline, and they get it here through one further claim family,
`SurfaceClaim`, each constructor of which is backed by an exact checker
(`SurfaceClaim.check_iff`).

The guarantees are the ones that matter for imported results:

* `SurfaceCertificate.holds_of_supported` — supported evidence provably entails
  the claim it reports, on any of the new surfaces;
* `SurfaceCertificate.state_ne_contradicted` — importing is fail-closed: a failed
  constraint check, an unmatched source or an unrun checker is `unresolved`, never
  a refutation;
* `SurfaceCertificate.not_holds_of_check_false` — but because the checkers are
  exact, a failure *is* a certified negative about this knowledge base.

`losslessness_always_holds` records the one claim in the family that holds of
every knowledge base: RDF reification loses nothing.  It is proved, not pinned to
an upstream receipt.
-/

namespace Epistemic

open Wikidata

/-- Claims on the constraint, RDF, parthood and identity surfaces. -/
inductive SurfaceClaim
  | constraint (con : Constraint)
  | rdfSubclassEntailment (a b : Qid)
  | rdfInstanceEntailment (x c : Qid)
  | rdfLossless
  | partOf (x y : Qid)
  | identifierBijection (p : Pid)
  deriving DecidableEq, Repr, Inhabited

namespace SurfaceClaim

/-- What a surface claim means, relative to a knowledge base. -/
def Holds (kb : KB) : SurfaceClaim → Prop
  | constraint con => con.Holds kb
  | rdfSubclassEntailment a b =>
      Rdf.Entails (Rdf.directTriples kb) ⟨Rdf.Term.item a, Rdf.Term.prop P279, Rdf.Term.item b⟩
  | rdfInstanceEntailment x c =>
      Rdf.Entails (Rdf.directTriples kb) ⟨Rdf.Term.item x, Rdf.Term.prop P31, Rdf.Term.item c⟩
  | rdfLossless => Rdf.dereify (Rdf.reify kb) = kb.statements
  | partOf x y => PartOf kb x y
  | identifierBijection p => SingleValue kb p ∧ DistinctValue kb p

/-- The executable checker for a surface claim. -/
def check (kb : KB) : SurfaceClaim → Bool
  | constraint con => con.check kb
  | rdfSubclassEntailment a b => Rdf.entailsSubclassOk kb a b
  | rdfInstanceEntailment x c => Rdf.entailsInstanceOk kb x c
  | rdfLossless => Rdf.dereify (Rdf.reify kb) = kb.statements
  | partOf x y => isPartOf kb x y
  | identifierBijection p => singleValueOk kb p && distinctValueOk kb p

/-- **Checker exactness on every new surface.** -/
theorem check_iff (kb : KB) (cl : SurfaceClaim) : cl.check kb = true ↔ cl.Holds kb := by
  cases cl with
  | constraint con => exact Constraint.check_iff kb con
  | rdfSubclassEntailment a b => exact Rdf.entailsSubclassOk_iff kb a b
  | rdfInstanceEntailment x c => exact Rdf.entailsInstanceOk_iff kb x c
  | rdfLossless => exact decide_eq_true_iff
  | partOf x y => exact isPartOf_iff kb x y
  | identifierBijection p =>
      simp only [check, Holds, Bool.and_eq_true, singleValueOk_iff, distinctValueOk_iff]

theorem not_holds_of_check_false {kb : KB} {cl : SurfaceClaim} (h : cl.check kb = false) :
    ¬ cl.Holds kb := by
  intro hc
  rw [(check_iff kb cl).2 hc] at h
  exact Bool.noConfusion h

/-- Reification is lossless for every knowledge base, so this claim never needs
importing on trust. -/
theorem losslessness_always_holds (kb : KB) : (rdfLossless).Holds kb := Rdf.dereify_reify kb

/-- Which ontology surface a claim belongs to. -/
def surface : SurfaceClaim → SurfaceKind
  | constraint _ => SurfaceKind.constraintFact
  | rdfSubclassEntailment _ _ => SurfaceKind.rdfFact
  | rdfInstanceEntailment _ _ => SurfaceKind.rdfFact
  | rdfLossless => SurfaceKind.rdfFact
  | partOf _ _ => SurfaceKind.statementFact
  | identifierBijection _ => SurfaceKind.identityFact

end SurfaceClaim

/-! ## Certificates on the new surfaces -/

/-- An imported result on one of the new surfaces. -/
structure SurfaceCertificate where
  kb : KB
  claim : SurfaceClaim
  sourceMatched : Bool
  references : List String

namespace SurfaceCertificate

/-- Did the checker accept? -/
def accepted (cert : SurfaceCertificate) : Bool := cert.claim.check cert.kb

/-- Fail-closed evidence state. -/
def state (cert : SurfaceCertificate) : Trit := receiptState cert.sourceMatched cert.accepted

theorem state_eq_supported_iff (cert : SurfaceCertificate) :
    cert.state = Trit.supported ↔ cert.sourceMatched = true ∧ cert.claim.Holds cert.kb := by
  rw [state, receiptState_eq_supported_iff]
  exact and_congr_right fun _ => SurfaceClaim.check_iff cert.kb cert.claim

/-- **Supported evidence is really backed** on the new surfaces too. -/
theorem holds_of_supported {cert : SurfaceCertificate} (h : cert.state = Trit.supported) :
    cert.claim.Holds cert.kb :=
  ((state_eq_supported_iff cert).1 h).2

/-- A failing constraint or entailment check is `unresolved`, not a refutation. -/
theorem state_of_checker_failure {cert : SurfaceCertificate} (h : cert.accepted = false) :
    cert.state = Trit.unresolved := by
  rw [state, h, receiptState_of_checker_failure]

theorem state_of_source_mismatch {cert : SurfaceCertificate} (h : cert.sourceMatched = false) :
    cert.state = Trit.unresolved := by
  rw [state, h, receiptState_of_source_mismatch]

/-- **Fail-closed import** on the new surfaces. -/
theorem state_ne_contradicted (cert : SurfaceCertificate) : cert.state ≠ Trit.contradicted :=
  receiptState_ne_contradicted _ _

/-- A checker failure is a certified negative *about this knowledge base*. -/
theorem not_holds_of_check_false {cert : SurfaceCertificate} (h : cert.accepted = false) :
    ¬ cert.claim.Holds cert.kb :=
  SurfaceClaim.not_holds_of_check_false h

/-- The provenance-bearing scoped claim generated by a surface certificate. -/
def scopedClaim (cert : SurfaceCertificate) : ScopedClaim SurfaceKind :=
  scopedOfReceipt cert.sourceMatched cert.accepted cert.references

@[simp] theorem scopedClaim_references (cert : SurfaceCertificate) :
    cert.scopedClaim.references = cert.references := rfl

@[simp] theorem scopedClaim_stateAt (cert : SurfaceCertificate) (k : SurfaceKind) :
    cert.scopedClaim.stateAt k = cert.state := rfl

/-- A lossless-reification certificate with a matched source is always
supported: the claim is a theorem, not a receipt. -/
theorem lossless_supported {kb : KB} {refs : List String} :
    (⟨kb, SurfaceClaim.rdfLossless, true, refs⟩ : SurfaceCertificate).state
      = Trit.supported := by
  rw [state_eq_supported_iff]
  exact ⟨rfl, SurfaceClaim.losslessness_always_holds kb⟩

end SurfaceCertificate

/-! ## Identity evidence carries no class authority -/

/-- An identifier bijection is evidence about identity only.  Even a fully
supported `identifierBijection` certificate leaves the class facts of the
knowledge base untouched: here it holds while no instance fact is derivable. -/
theorem identifier_evidence_grants_no_class_fact :
    ∃ cert : SurfaceCertificate,
      cert.state = Trit.supported ∧ ∀ x c : Qid, ¬ InstanceOf cert.kb x c := by
  refine ⟨⟨⟨[⟨1⟩], []⟩, SurfaceClaim.identifierBijection ⟨214⟩, true, ["identity source"]⟩,
    ?_, ?_⟩
  · rw [SurfaceCertificate.state_eq_supported_iff]
    refine ⟨rfl, ?_⟩
    constructor <;>
      · intro st₁ h₁
        simp [truthyStatementsFor] at h₁
  · rintro x c ⟨c₀, hc₀, -⟩
    simp [instanceEdges] at hc₀

end Epistemic
