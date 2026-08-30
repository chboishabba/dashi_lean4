import RequestProject.Wikidata.Rdf
import RequestProject.Epistemic.Lens

/-!
# The Wikidata layers as a view family

The layer tower of `Layers.lean` and `Rdf.lean` — full statements, the truthy
query layer, the reified RDF layer, the direct RDF layer — is exactly a family of
projections of one latent object, the knowledge base.  Reading it as a
`ViewFamily` turns two informal claims about the tower into theorems.

* **The class-fact view is layer-invariant.**  Projecting a knowledge base onto
  its subclass edges gives literally the same list at the full and truthy layers,
  so there is an invertible lens transition between them, and it is the identity
  (`classTransition_full_truthy`).  Nothing about class facts is gained or lost
  by moving between those two layers.

* **The RDF tower is strictly ordered.**  The reified layer determines the direct
  layer (`determines_reified_direct`), the converse fails
  (`not_determines_direct_reified`), and consequently *no* lens transition
  between them exists (`no_transition_direct_reified`).  Rank is the information
  that is destroyed, and no transport can restore it.

Together these say: layer changes are safe exactly where a two-sided transport
can be produced, which is a property to be checked per pair of layers, not a
blanket assumption about the tower.
-/

namespace Wikidata

open Epistemic

/-! ## The class-fact view -/

/-- The knowledge base seen as its subclass graph, at a chosen statement layer. -/
def classView : ViewFamily KB StatementLayer (List (Qid × Qid)) where
  project l kb := subclassEdges (atLayer kb l)

@[simp] theorem classView_full (kb : KB) :
    classView.project StatementLayer.full kb = subclassEdges kb := rfl

@[simp] theorem classView_truthy (kb : KB) :
    classView.project StatementLayer.truthy kb = subclassEdges (truthyLayer kb) := rfl

/-- The class-fact view does not depend on the statement layer. -/
theorem classView_project_eq (l l' : StatementLayer) (kb : KB) :
    classView.project l kb = classView.project l' kb := by
  cases l <;> cases l' <;>
    simp [classView, atLayer, subclassEdges_truthyLayer]

/-- **The truthy layer is a lossless lens for class facts**, and the transport
between the two layers is the identity. -/
def classTransition_full_truthy :
    ViewFamily.Transition classView StatementLayer.full StatementLayer.truthy where
  forward := id
  backward := id
  forwardProjects := fun kb => (classView_project_eq _ _ kb)
  backwardProjects := fun kb => (classView_project_eq _ _ kb)
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl

/-- Every reading of the class-fact view is layer-independent. -/
theorem classView_observe_eq (q : List (Qid × Qid) → Trit) (l l' : StatementLayer) (kb : KB) :
    classView.observe q l kb = classView.observe q l' kb := by
  simp [ViewFamily.observe, classView_project_eq l l' kb]

/-! ## The RDF view -/

/-- The two RDF surfaces. -/
inductive RdfLayer
  | reified
  | direct
  deriving DecidableEq, Repr, Inhabited

/-- The knowledge base seen as RDF triples, at a chosen RDF layer. -/
def rdfView : ViewFamily KB RdfLayer (List Rdf.Triple) where
  project
    | RdfLayer.reified, kb => Rdf.reify kb
    | RdfLayer.direct, kb => Rdf.directTriples kb

@[simp] theorem rdfView_reified (kb : KB) :
    rdfView.project RdfLayer.reified kb = Rdf.reify kb := rfl

@[simp] theorem rdfView_direct (kb : KB) :
    rdfView.project RdfLayer.direct kb = Rdf.directTriples kb := rfl

/-- The truthy projection depends on the statement list alone. -/
theorem isTruthy_congr {kb₁ kb₂ : KB} (h : kb₁.statements = kb₂.statements) :
    IsTruthy kb₁ = IsTruthy kb₂ := by
  funext st
  simp [IsTruthy, hasPreferred, statementsFor, h]

/-- Hence so does the direct layer. -/
theorem directTriples_congr {kb₁ kb₂ : KB} (h : kb₁.statements = kb₂.statements) :
    Rdf.directTriples kb₁ = Rdf.directTriples kb₂ := by
  simp [Rdf.directTriples, isTruthy_congr h, h]

/-- **The reified layer determines the direct layer.**  It is lossless, so
anything computed from the direct layer is already fixed by it. -/
theorem determines_reified_direct : rdfView.Determines RdfLayer.reified RdfLayer.direct := by
  intro kb₁ kb₂ h
  exact directTriples_congr (Rdf.reify_injective h)

/-- **The direct layer does not determine the reified layer**: it forgets rank. -/
theorem not_determines_direct_reified : ¬ rdfView.Determines RdfLayer.direct RdfLayer.reified := by
  intro h
  obtain ⟨kb₁, kb₂, hdir, hre⟩ := Rdf.direct_layer_forgets_rank
  exact hre (h kb₁ kb₂ hdir)

/-- **No lens transition from the direct layer back to the reified layer.**
Rank cannot be transported back, so there is no two-sided transport at all. -/
theorem no_transition_direct_reified :
    IsEmpty (ViewFamily.Transition rdfView RdfLayer.direct RdfLayer.reified) :=
  ViewFamily.isEmpty_transition_of_not_determines not_determines_direct_reified

/-- A transition is symmetric, so there is no transition in the other direction
either: the reified and direct layers are not interchangeable views, even though
one determines the other. -/
theorem no_transition_reified_direct :
    IsEmpty (ViewFamily.Transition rdfView RdfLayer.reified RdfLayer.direct) :=
  ⟨fun T => no_transition_direct_reified.elim T.symm⟩

/-- **The RDF tower is strictly ordered by information.** -/
theorem rdf_tower_strict :
    rdfView.Determines RdfLayer.reified RdfLayer.direct ∧
      ¬ rdfView.Determines RdfLayer.direct RdfLayer.reified :=
  ⟨determines_reified_direct, not_determines_direct_reified⟩

end Wikidata
