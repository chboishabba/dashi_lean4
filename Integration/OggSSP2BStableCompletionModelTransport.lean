import Integration.OggSSP2BActualStableCompletionSubquotient

/-!
# Transport a concrete stable Completion10 model onto the actual 2B Tate carrier

A bare 276-dimensional linear equivalence is not enough for the scientific
same-object claim: it can transport *some* conjugate operator, but it does not
prove that operator is the sourced actual M22:2 outer action on Tate.

This file therefore keeps the earlier coordinate-transport compiler for
compatibility and adds the preferred equivariant weld:

  e : ActualTate276 ≃ M,
  g_Tate : ActualTate276 -> ActualTate276,
  e (g_Tate x) = g_model (e x).

With this square, the pulled-back stable quotient is preserved by the actual
Tate operator itself, and the descended action is the already-verified
Completion10 J2^5 action on the same quotient.
-/

namespace Integration.OggSSP2BStableCompletionModelTransport

namespace A := Integration.OggSSP2BActualStableCompletionSubquotient
namespace R := Integration.OggSSP2BRevisedCompletionRecognition

abbrev Scalar := A.Scalar
abbrev ActualTate276 := A.ActualTate276

structure ModelStableCompletionReceipt
    (M Q : Type*) [AddCommGroup M] [Module Scalar M]
    [AddCommGroup Q] [Module Scalar Q] where
  sourceSubmodule : Submodule Scalar M
  quotient : sourceSubmodule →ₗ[Scalar] Q
  quotient_surjective : Function.Surjective quotient
  target_finrank : Module.finrank Scalar Q = 10
  atlasKind : Integration.OggSSP2BM22CompletionTenCandidate.M22TenModuleKind

  outerOperator : M →ₗ[Scalar] M
  source_preserved : ∀ x : sourceSubmodule, outerOperator x.1 ∈ sourceSubmodule

  quotientOuterOperator : Q →ₗ[Scalar] Q
  quotient_natural : ∀ x : sourceSubmodule,
    quotient ⟨outerOperator x.1, source_preserved x⟩
      = quotientOuterOperator (quotient x)

  completionChart : Q ≃ₗ[Scalar] R.CompletionModule
  quotientOuterOperator_involutive :
    quotientOuterOperator.comp quotientOuterOperator = LinearMap.id
  completion_intertwining : ∀ q,
    completionChart (quotientOuterOperator q)
      = R.completionFlipLinear (completionChart q)

  sourcedFromM22d2OuterClass : Bool
  modelProvenance : String

/-- Preferred same-object weld: the model equivalence must intertwine the
actual sourced Tate outer operator with the model outer operator. -/
structure EquivariantModelWeldReceipt
    (M : Type*) [AddCommGroup M] [Module Scalar M]
    (modelOuter : M →ₗ[Scalar] M) where
  equivalence : ActualTate276 ≃ₗ[Scalar] M
  actualOuterOperator : ActualTate276 →ₗ[Scalar] ActualTate276
  outer_intertwining : ∀ x,
    equivalence (actualOuterOperator x) = modelOuter (equivalence x)
  actualOuterOperatorSourced : Bool
  sourceProvenance : String

namespace ModelStableCompletionReceipt

variable {M Q : Type*} [AddCommGroup M] [Module Scalar M]
variable [AddCommGroup Q] [Module Scalar Q]

/-- Pullback of the model's selected source submodule. -/
def pulledSource
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M) :
    Submodule Scalar ActualTate276 :=
  r.sourceSubmodule.comap e.toLinearMap

/-- Canonical map from an element of the pulled-back source into the concrete
model source. -/
def toModelSource
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (x : r.pulledSource e) : r.sourceSubmodule :=
  ⟨e x.1, x.2⟩

@[simp] theorem toModelSource_val
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (x : r.pulledSource e) :
    (r.toModelSource e x : M) = e x.1 := rfl

/-- Compatibility path: transport by conjugating the model operator.  This is
useful algebraically but is not, by itself, the preferred sourced-action weld. -/
def transportToActualTate
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (sameObjectProvenance : String) :
    A.StableCompletionSubquotientReceipt Q where
  sourceSubmodule := r.pulledSource e
  quotient :=
    { toFun := fun x => r.quotient (r.toModelSource e x)
      map_add' := by
        intro x y
        simp [toModelSource]
      map_smul' := by
        intro c x
        simp [toModelSource] }
  quotient_surjective := by
    intro q
    obtain ⟨y, hy⟩ := r.quotient_surjective q
    let x0 : ActualTate276 := e.symm y.1
    have hx0 : x0 ∈ r.pulledSource e := by
      change e x0 ∈ r.sourceSubmodule
      simpa [x0] using y.2
    let x : r.pulledSource e := ⟨x0, hx0⟩
    refine ⟨x, ?_⟩
    change r.quotient (r.toModelSource e x) = q
    simpa [x, x0, toModelSource] using hy
  target_finrank := r.target_finrank
  atlasKind := r.atlasKind
  ambientOuterOperator :=
    e.symm.toLinearMap.comp (r.outerOperator.comp e.toLinearMap)
  source_preserved := by
    intro x
    change e (e.symm (r.outerOperator (e x.1))) ∈ r.sourceSubmodule
    simpa using r.source_preserved (r.toModelSource e x)
  quotientOuterOperator := r.quotientOuterOperator
  quotient_natural := by
    intro x
    change r.quotient
        (r.toModelSource e
          ⟨e.symm (r.outerOperator (e x.1)), by
            change e (e.symm (r.outerOperator (e x.1))) ∈ r.sourceSubmodule
            simpa using r.source_preserved (r.toModelSource e x)⟩)
      = r.quotientOuterOperator (r.quotient (r.toModelSource e x))
    simpa [toModelSource] using r.quotient_natural (r.toModelSource e x)
  completionChart := r.completionChart
  quotientOuterOperator_involutive := r.quotientOuterOperator_involutive
  completion_intertwining := r.completion_intertwining
  sourcedFromM22d2OuterClass := r.sourcedFromM22d2OuterClass
  sourceProvenance := sameObjectProvenance

/-- Preferred transport: use the actual Tate outer operator and an explicit
intertwining square with the concrete model. -/
def transportEquivariantlyToActualTate
    (r : ModelStableCompletionReceipt M Q)
    (w : EquivariantModelWeldReceipt M r.outerOperator) :
    A.StableCompletionSubquotientReceipt Q where
  sourceSubmodule := r.pulledSource w.equivalence
  quotient :=
    { toFun := fun x => r.quotient (r.toModelSource w.equivalence x)
      map_add' := by intro x y; simp [toModelSource]
      map_smul' := by intro c x; simp [toModelSource] }
  quotient_surjective := by
    intro q
    obtain ⟨y, hy⟩ := r.quotient_surjective q
    let x0 : ActualTate276 := w.equivalence.symm y.1
    have hx0 : x0 ∈ r.pulledSource w.equivalence := by
      change w.equivalence x0 ∈ r.sourceSubmodule
      simpa [x0] using y.2
    refine ⟨⟨x0, hx0⟩, ?_⟩
    change r.quotient ⟨w.equivalence x0, hx0⟩ = q
    simpa [x0] using hy
  target_finrank := r.target_finrank
  atlasKind := r.atlasKind
  ambientOuterOperator := w.actualOuterOperator
  source_preserved := by
    intro x
    change w.equivalence (w.actualOuterOperator x.1) ∈ r.sourceSubmodule
    rw [w.outer_intertwining]
    exact r.source_preserved (r.toModelSource w.equivalence x)
  quotientOuterOperator := r.quotientOuterOperator
  quotient_natural := by
    intro x
    change r.quotient
        ⟨w.equivalence (w.actualOuterOperator x.1), by
          rw [w.outer_intertwining]
          exact r.source_preserved (r.toModelSource w.equivalence x)⟩
      = r.quotientOuterOperator (r.quotient (r.toModelSource w.equivalence x))
    rw [w.outer_intertwining]
    simpa [toModelSource] using r.quotient_natural (r.toModelSource w.equivalence x)
  completionChart := r.completionChart
  quotientOuterOperator_involutive := r.quotientOuterOperator_involutive
  completion_intertwining := r.completion_intertwining
  sourcedFromM22d2OuterClass := w.actualOuterOperatorSourced && r.sourcedFromM22d2OuterClass
  sourceProvenance := w.sourceProvenance ++ "; " ++ r.modelProvenance

 theorem transported_finrank_ten
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (p : String) :
    Module.finrank Scalar Q = 10 :=
  (r.transportToActualTate e p).target_finrank

 theorem equivariantly_transported_finrank_ten
    (r : ModelStableCompletionReceipt M Q)
    (w : EquivariantModelWeldReceipt M r.outerOperator) :
    Module.finrank Scalar Q = 10 :=
  (r.transportEquivariantlyToActualTate w).target_finrank

 theorem equivariantly_transported_completion_intertwines
    (r : ModelStableCompletionReceipt M Q)
    (w : EquivariantModelWeldReceipt M r.outerOperator)
    (q : Q) :
    let tr := r.transportEquivariantlyToActualTate w
    tr.completionChart (tr.quotientOuterOperator q)
      = R.completionFlipLinear (tr.completionChart q) := by
  simpa using r.completion_intertwining q

end ModelStableCompletionReceipt

end Integration.OggSSP2BStableCompletionModelTransport
