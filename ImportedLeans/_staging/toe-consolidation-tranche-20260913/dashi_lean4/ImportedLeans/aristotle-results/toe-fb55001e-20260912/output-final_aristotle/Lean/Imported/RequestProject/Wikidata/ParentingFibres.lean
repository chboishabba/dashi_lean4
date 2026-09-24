import RequestProject.Wikidata.Parenting
import RequestProject.Epistemic.Quotient

/-!
# The parent slot as a projection: observers, hidden motion, residuals

The Wikidata parent slot is a projection of the relationship carrier of
`RequestProject.Wikidata.Parenting`.  This module runs the generic machinery of
`RequestProject.Epistemic.Observer` and `RequestProject.Epistemic.Quotient` on it
and reads off what the slot can and cannot carry.

* **Observers.**  The slot alone is not separating (`slotObserver_not_separating`);
  adding the genetic coordinate strictly refines it
  (`slot_genetic_strictlyRefines`) and is still not separating
  (`geneticObserver_not_separating`).
* **Hidden dynamics.**  Legal finalisation and identity disclosure both change
  the fine state while leaving the slot fixed
  (`finalizeLegal_hidden_transition`, `disclose_hidden_transition`), which is
  itself a proof that the slot projection is not injective.
* **Exact reopening.**  Slot plus relation vector reconstructs the carrier on the
  nose (`parentReopening`), so surface and residual together are separating and
  every hidden transition must move the residual
  (`legal_finalization_moves_residual`, `disclosure_moves_residual`).
* **Descent of predicates.**  A predicate of the slot pulls back to a
  fibre-constant predicate of the carrier; the genetic, genealogical and
  progenitor coordinates provably do not descend
  (`genetic_not_fibreConstant` and friends).
* **Authority routing.**  Strongest of the group: an authority route that reads
  the legal-parent coordinate cannot be reproduced by *any* interpretation of the
  slot (`route_not_factorsThrough`).  The erased distinction is action-bearing,
  not merely descriptive.
* **Progressive residuals.**  Factoring carrier → semantic surface → slot makes
  the total residual the product of the two stage residuals, so a refinement
  tower needs no ever-widening public record.
-/

namespace Wikidata.Parenting

open Epistemic

/-! ## Observers on the carrier -/

/-- The public observer: the Wikidata slot. -/
def slotObserver : Observer ParentCarrier Pid := ParentCarrier.projectSlot

/-- The genetic-contribution observer. -/
def geneticObserver : Observer ParentCarrier Bool := fun c => c.relation.genetic

/-- The genealogical-parent observer. -/
def genealogicalObserver : Observer ParentCarrier Bool := fun c => c.relation.genealogical

/-- The legal-parent observer. -/
def legalObserver : Observer ParentCarrier Bool := fun c => c.relation.legal

/-- The disclosure observer. -/
def disclosureObserver : Observer ParentCarrier Bool := fun c => c.relation.identityDisclosable

/-- **The parent slot is not a separating observer.** -/
theorem slotObserver_not_separating : ¬ Separating slotObserver := by
  refine not_separating_of_collision ⟨anonymousDonorCarrier, adoptiveCarrier, rfl, ?_⟩
  decide

/-- **Adding the genetic coordinate strictly refines the slot.** -/
theorem slot_genetic_strictlyRefines :
    StrictlyRefines slotObserver (pairObserver slotObserver geneticObserver) :=
  strictlyRefines_pair (x := anonymousDonorCarrier) (y := adoptiveCarrier) rfl (by decide)

/-- **The genetic coordinate alone is still not separating**: an anonymous donor
and a genetic, gestational, legal parent look the same to it. -/
theorem geneticObserver_not_separating : ¬ Separating geneticObserver := by
  refine not_separating_of_collision
    ⟨anonymousDonorCarrier, ⟨NodeLevel.individual, RelationVector.geneticGestationalParent⟩,
      rfl, ?_⟩
  decide

/-- Neither is the pair of slot and genetic coordinate. -/
theorem slot_genetic_pair_not_separating :
    ¬ Separating (pairObserver slotObserver geneticObserver) := by
  refine not_separating_of_collision
    ⟨anonymousDonorCarrier, ⟨NodeLevel.individual, RelationVector.disclosableDonor⟩, rfl, ?_⟩
  decide

/-! ## Dynamics hidden inside a slot fibre -/

/-- Legal finalisation: the legal-parent coordinate is switched on. -/
def finalizeLegal (c : ParentCarrier) : ParentCarrier :=
  { c with relation := { c.relation with legal := true } }

/-- Disclosure: the identity becomes known and disclosable. -/
def discloseIdentity (c : ParentCarrier) : ParentCarrier :=
  { c with relation := { c.relation with identityKnown := true, identityDisclosable := true } }

theorem finalizeLegal_surfaceInvariant :
    SurfaceInvariant ParentCarrier.projectSlot finalizeLegal := fun _ => rfl

theorem discloseIdentity_surfaceInvariant :
    SurfaceInvariant ParentCarrier.projectSlot discloseIdentity := fun _ => rfl

/-- **Legal finalisation is a hidden transition**: the fine state moves, the
public slot does not. -/
theorem finalizeLegal_hidden_transition :
    HiddenTransition ParentCarrier.projectSlot finalizeLegal preFinalizationCarrier :=
  hiddenTransition_of_surfaceInvariant finalizeLegal_surfaceInvariant (by decide)

/-- **Disclosure is a hidden transition** too. -/
theorem disclose_hidden_transition :
    HiddenTransition ParentCarrier.projectSlot discloseIdentity anonymousDonorCarrier :=
  hiddenTransition_of_surfaceInvariant discloseIdentity_surfaceInvariant (by decide)

/-- Consequently the slot projection is not injective. -/
theorem projectSlot_not_injective : ¬ Function.Injective ParentCarrier.projectSlot :=
  not_injective_of_hiddenTransition finalizeLegal_hidden_transition

/-- Disclosure varies inside one `P8810` fibre. -/
theorem disclosure_varies_inside_fibre :
    anonymousDonorCarrier.projectSlot = disclosableDonorCarrier.projectSlot ∧
      disclosureObserver anonymousDonorCarrier = false ∧
      disclosureObserver disclosableDonorCarrier = true := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-! ## Exact reopening -/

/-- The level a slot commits to. -/
def levelFromSlot (p : Pid) : NodeLevel :=
  if p = P1531 then NodeLevel.lineage else NodeLevel.individual

theorem levelFromSlot_recommendedSlot (l : NodeLevel) : levelFromSlot (recommendedSlot l) = l := by
  cases l <;> decide

/-- **Slot plus relation vector reopens the carrier exactly.** -/
def parentReopening : ExactRecoverable ParentCarrier Pid where
  Residual := RelationVector
  project := ParentCarrier.projectSlot
  residual := ParentCarrier.relation
  reopen := fun p r => ⟨levelFromSlot p, r⟩
  reopen_exact := by
    rintro ⟨l, r⟩
    simp only [ParentCarrier.projectSlot, ParentCarrier.mk.injEq, and_true]
    exact levelFromSlot_recommendedSlot l

/-- Same slot and same residual: the same carrier. -/
theorem eq_of_slot_and_relation {c d : ParentCarrier} (hslot : c.projectSlot = d.projectSlot)
    (hrel : c.relation = d.relation) : c = d :=
  parentReopening.eq_of_project_eq_of_residual_eq hslot hrel

/-- **Legal finalisation must move the residual.** -/
theorem legal_finalization_moves_residual :
    (finalizeLegal preFinalizationCarrier).relation ≠ preFinalizationCarrier.relation :=
  parentReopening.residual_ne_of_hiddenTransition finalizeLegal_hidden_transition

/-- **Disclosure must move the residual.** -/
theorem disclosure_moves_residual :
    (discloseIdentity anonymousDonorCarrier).relation ≠ anonymousDonorCarrier.relation :=
  parentReopening.residual_ne_of_hiddenTransition disclose_hidden_transition

/-! ## Which predicates descend through the slot -/

/-- Is this the generic `P8810` parent slot? -/
def isP8810 : Predicate Pid := fun p => p = P8810

/-- The `P8810` predicate read on carriers. -/
def p8810Predicate : Predicate ParentCarrier := pullbackPred ParentCarrier.projectSlot isP8810

/-- **A slot predicate descends by construction.** -/
theorem p8810Predicate_fibreConstant :
    FibreConstantPred ParentCarrier.projectSlot p8810Predicate :=
  fibreConstantPred_pullback _ _

/-- The genetic coordinate as a predicate. -/
def geneticPred : Predicate ParentCarrier := fun c => c.relation.genetic

/-- The genealogical-parent coordinate as a predicate. -/
def genealogicalPred : Predicate ParentCarrier := fun c => c.relation.genealogical

/-- The progenitor coordinate as a predicate. -/
def progenitorPred : Predicate ParentCarrier := fun c => c.relation.progenitor

/-- **The genetic coordinate does not descend through the slot.** -/
theorem genetic_not_fibreConstant :
    ¬ FibreConstantPred ParentCarrier.projectSlot geneticPred := by
  intro h
  have := h anonymousDonorCarrier adoptiveCarrier rfl
  simp [geneticPred, anonymousDonorCarrier, adoptiveCarrier, RelationVector.anonymousDonor,
    RelationVector.adoptiveParent, RelationVector.none] at this

/-- **Neither does genealogical parenthood.** -/
theorem genealogical_not_fibreConstant :
    ¬ FibreConstantPred ParentCarrier.projectSlot genealogicalPred := by
  intro h
  have := h anonymousDonorCarrier adoptiveCarrier rfl
  simp [genealogicalPred, anonymousDonorCarrier, adoptiveCarrier, RelationVector.anonymousDonor,
    RelationVector.adoptiveParent, RelationVector.none] at this

/-- **Nor progeniture.** -/
theorem progenitor_not_fibreConstant :
    ¬ FibreConstantPred ParentCarrier.projectSlot progenitorPred := by
  intro h
  have := h anonymousDonorCarrier adoptiveCarrier rfl
  simp [progenitorPred, anonymousDonorCarrier, adoptiveCarrier, RelationVector.anonymousDonor,
    RelationVector.adoptiveParent, RelationVector.none] at this

/-! ## Authority routing is not a function of the slot -/

/-- Where a decision about parental authority is routed. -/
inductive AuthorityRoute
  | noParentalAuthority
  | legalParentDecision
  deriving DecidableEq, Repr, Inhabited

/-- The fine router: only a legal parent gets the legal-parent decision route. -/
def routeAuthority (c : ParentCarrier) : AuthorityRoute :=
  if c.relation.legal then AuthorityRoute.legalParentDecision else AuthorityRoute.noParentalAuthority

theorem route_anonymousDonor :
    routeAuthority anonymousDonorCarrier = AuthorityRoute.noParentalAuthority := by decide

theorem route_adoptive :
    routeAuthority adoptiveCarrier = AuthorityRoute.legalParentDecision := by decide

/-- **No interpretation of the parent slot reproduces the authority route.**  The
distinction the slot erases is action-bearing. -/
theorem route_not_factorsThrough :
    ¬ FactorsThrough ParentCarrier.projectSlot routeAuthority :=
  not_factorsThrough (x := anonymousDonorCarrier) (y := adoptiveCarrier) rfl (by decide)

/-! ## Progressive residual factorisation

Rather than one flat receipt, factor the projection through a semantic surface
that keeps the public-facing progenitor/genetic/genealogical coordinates. -/

/-- The intermediate semantic surface. -/
structure SemanticSurface where
  /-- The Wikidata slot. -/
  slot : Pid
  /-- Progeniture. -/
  progenitor : Bool
  /-- Genetic contribution. -/
  genetic : Bool
  /-- Genealogical parenthood. -/
  genealogical : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What the semantic surface leaves behind. -/
structure PrivateResidual where
  /-- Gamete contribution. -/
  gamete : Bool
  /-- Mitochondrial contribution. -/
  mitochondrial : Bool
  /-- Gestation. -/
  gestational : Bool
  /-- Intended parenthood. -/
  intended : Bool
  /-- Legal parenthood. -/
  legal : Bool
  /-- Social parenthood. -/
  social : Bool
  /-- Caregiving. -/
  caregiver : Bool
  /-- The identity is known. -/
  identityKnown : Bool
  /-- The identity may be disclosed. -/
  identityDisclosable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What the slot leaves behind of the semantic surface. -/
structure SemanticResidual where
  /-- Progeniture. -/
  progenitor : Bool
  /-- Genetic contribution. -/
  genetic : Bool
  /-- Genealogical parenthood. -/
  genealogical : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Stage one: carrier to semantic surface, with the private coordinates as
residual. -/
def semanticStage : ExactRecoverable ParentCarrier SemanticSurface where
  Residual := PrivateResidual
  project := fun c =>
    ⟨c.projectSlot, c.relation.progenitor, c.relation.genetic, c.relation.genealogical⟩
  residual := fun c =>
    ⟨c.relation.gamete, c.relation.mitochondrial, c.relation.gestational, c.relation.intended,
      c.relation.legal, c.relation.social, c.relation.caregiver, c.relation.identityKnown,
      c.relation.identityDisclosable⟩
  reopen := fun s r =>
    ⟨levelFromSlot s.slot,
      ⟨s.progenitor, s.genetic, r.gamete, r.mitochondrial, r.gestational, s.genealogical,
        r.intended, r.legal, r.social, r.caregiver, r.identityKnown, r.identityDisclosable⟩⟩
  reopen_exact := by
    rintro ⟨l, ⟨a, b, c, d, e, f, g, h, i, j, k, m⟩⟩
    simp only [ParentCarrier.projectSlot, ParentCarrier.mk.injEq, and_true]
    exact levelFromSlot_recommendedSlot l

/-- Stage two: semantic surface to slot, with the semantic coordinates as
residual. -/
def slotStage : ExactRecoverable SemanticSurface Pid where
  Residual := SemanticResidual
  project := SemanticSurface.slot
  residual := fun s => ⟨s.progenitor, s.genetic, s.genealogical⟩
  reopen := fun p r => ⟨p, r.progenitor, r.genetic, r.genealogical⟩
  reopen_exact := by rintro ⟨p, a, b, c⟩; rfl

/-- The composite of the two stages. -/
def progressiveReopening : ExactRecoverable ParentCarrier Pid :=
  ExactRecoverable.comp semanticStage slotStage

/-- The composite really is the slot projection. -/
theorem progressiveReopening_project :
    progressiveReopening.project = ParentCarrier.projectSlot := rfl

/-- **The composite residual is the product of the two stage residuals.** -/
theorem progressiveReopening_residual :
    progressiveReopening.Residual = (PrivateResidual × SemanticResidual) := rfl

/-- Reopening through the tower is still exact. -/
theorem progressiveReopening_exact (c : ParentCarrier) :
    progressiveReopening.reopen (progressiveReopening.project c)
      (progressiveReopening.residual c) = c :=
  progressiveReopening.reopen_exact c

end Wikidata.Parenting
