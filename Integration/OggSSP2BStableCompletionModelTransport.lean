import Integration.OggSSP2BActualStableCompletionSubquotient

/-!
# Transport a concrete stable Completion10 model onto the actual 2B Tate carrier

Once a literal same-object equivalence between `ActualTate276` and a concrete
276-dimensional model (duad, Co1 exterior square, or another sourced model) is
available, we should not reconstruct N<=S and the quotient action manually.

This file packages the stable quotient on an arbitrary model `M` and pulls the
entire structure back through a linear equivalence

    ActualTate276 ≃ₗ M.

Thus the only remaining vertical weld is the equivalence itself; the finite
stable quotient, outer operator, quotient action and Completion10 chart transport
automatically.
-/

namespace Integration.OggSSP2BStableCompletionModelTransport

namespace A := Integration.OggSSP2BActualStableCompletionSubquotient
namespace R := Integration.OggSSP2BRevisedCompletionRecognition

abbrev Scalar := A.Scalar
abbrev ActualTate276 := A.ActualTate276

/-- Stable Completion10 data on an arbitrary concrete 276-dimensional model. -/
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

namespace ModelStableCompletionReceipt

variable {M Q : Type*} [AddCommGroup M] [Module Scalar M]
variable [AddCommGroup Q] [Module Scalar Q]

/-- Pull a concrete-model stable quotient back to the actual Tate carrier. -/
def transportToActualTate
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (sameObjectProvenance : String) :
    A.StableCompletionSubquotientReceipt Q where
  sourceSubmodule := r.sourceSubmodule.comap e.toLinearMap
  quotient :=
    { toFun := fun x => r.quotient ⟨e x.1, x.2⟩
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  quotient_surjective := by
    intro q
    obtain ⟨y, hy⟩ := r.quotient_surjective q
    let x0 : ActualTate276 := e.symm y.1
    have hx0 : x0 ∈ r.sourceSubmodule.comap e.toLinearMap := by
      change e x0 ∈ r.sourceSubmodule
      simpa [x0] using y.2
    refine ⟨⟨x0, hx0⟩, ?_⟩
    change r.quotient ⟨e x0, hx0⟩ = q
    simpa [x0] using hy
  target_finrank := r.target_finrank
  atlasKind := r.atlasKind
  ambientOuterOperator :=
    e.symm.toLinearMap.comp (r.outerOperator.comp e.toLinearMap)
  source_preserved := by
    intro x
    change e (e.symm (r.outerOperator (e x.1))) ∈ r.sourceSubmodule
    simpa using r.source_preserved ⟨e x.1, x.2⟩
  quotientOuterOperator := r.quotientOuterOperator
  quotient_natural := by
    intro x
    simpa using r.quotient_natural ⟨e x.1, x.2⟩
  completionChart := r.completionChart
  quotientOuterOperator_involutive := r.quotientOuterOperator_involutive
  completion_intertwining := r.completion_intertwining
  sourcedFromM22d2OuterClass := r.sourcedFromM22d2OuterClass
  sourceProvenance := sameObjectProvenance

/-- Once the model equivalence is supplied, the transported quotient has the
    exact target dimension automatically. -/
theorem transported_finrank_ten
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (p : String) :
    Module.finrank Scalar Q = 10 :=
  (r.transportToActualTate e p).target_finrank

/-- The finite model's Completion10 intertwiner survives the same-object weld. -/
theorem transported_completion_intertwines
    (r : ModelStableCompletionReceipt M Q)
    (e : ActualTate276 ≃ₗ[Scalar] M)
    (p : String) (q : Q) :
    let tr := r.transportToActualTate e p
    tr.completionChart (tr.quotientOuterOperator q)
      = R.completionFlipLinear (tr.completionChart q) := by
  simpa using r.completion_intertwining q

end ModelStableCompletionReceipt

end Integration.OggSSP2BStableCompletionModelTransport
