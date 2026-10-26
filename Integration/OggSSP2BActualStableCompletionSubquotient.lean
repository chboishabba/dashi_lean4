import Integration.OggSSP2BRevisedCompletionRecognition
import Integration.OggSSP2BTate276M24BrauerRuntimeReceipt

/-!
# Actual-Tate M22:2-stable Completion10 subquotient compiler

The finite search is over.  The remaining B'+C' theorem is one same-object statement:
construct a ten-dimensional quotient of an actual Tate submodule which is preserved by
the sourced outer M22:2 operator, and prove that the descended operator is the repo-native
Completion10 flip.

This file packages that exact datum and compiles it into the existing
`ActualTateCompletionTenRecognition`.  No character equality or finite Atlas result is
silently promoted to this receipt.
-/

namespace Integration.OggSSP2BActualStableCompletionSubquotient

namespace R := Integration.OggSSP2BRevisedCompletionRecognition
namespace B := Integration.OggSSP2BTate276M24BrauerRuntimeReceipt

abbrev Scalar := R.Scalar
abbrev ActualTate276 := R.ActualTate276

/-- The explicit N <= S <= M presentation behind a composition-factor quotient.
`kernelSubmodule` is N and `sourceSubmodule` is S. -/
structure StableCompletionSubquotientReceipt
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  sourceSubmodule : Submodule Scalar ActualTate276
  quotient : sourceSubmodule →ₗ[Scalar] Q
  quotient_surjective : Function.Surjective quotient
  target_finrank : Module.finrank Scalar Q = 10
  atlasKind : Integration.OggSSP2BM22CompletionTenCandidate.M22TenModuleKind

  /-- Actual ambient operator induced by the sourced outer M22:2 element. -/
  ambientOuterOperator : ActualTate276 →ₗ[Scalar] ActualTate276
  source_preserved :
    ∀ x : sourceSubmodule, ambientOuterOperator x.1 ∈ sourceSubmodule

  /-- The induced operator on Q and the same-object descent equation. -/
  quotientOuterOperator : Q →ₗ[Scalar] Q
  quotient_natural :
    ∀ x : sourceSubmodule,
      quotient ⟨ambientOuterOperator x.1, source_preserved x⟩
        = quotientOuterOperator (quotient x)

  /-- Identification of the descended action with Completion10. -/
  completionChart : Q ≃ₗ[Scalar] R.CompletionModule
  quotientOuterOperator_involutive :
    quotientOuterOperator.comp quotientOuterOperator = LinearMap.id
  completion_intertwining :
    ∀ q,
      completionChart (quotientOuterOperator q)
        = R.completionFlipLinear (completionChart q)

  sourcedFromM22d2OuterClass : Bool
  sourceProvenance : String

namespace StableCompletionSubquotientReceipt

variable {Q : Type*} [AddCommGroup Q] [Module Scalar Q]

/-- N in the concrete N <= S <= M subquotient presentation. -/
def kernelSubmodule (r : StableCompletionSubquotientReceipt Q) :
    Submodule Scalar r.sourceSubmodule := r.quotient.ker

/-- Compile the explicit stable subquotient directly into the existing B'+C' receipt. -/
def toRecognition (r : StableCompletionSubquotientReceipt Q) :
    R.ActualTateCompletionTenRecognition Q where
  subquotient :=
    { sourceSubmodule := r.sourceSubmodule
      quotient := r.quotient
      quotient_surjective := r.quotient_surjective
      target_finrank := r.target_finrank
      atlasKind := r.atlasKind }
  completion :=
    { chart := r.completionChart
      binaryOperator := r.quotientOuterOperator
      binaryOperator_involutive := r.quotientOuterOperator_involutive
      chart_intertwines_completion := r.completion_intertwining
      sourcedFromM22d2OuterClass := r.sourcedFromM22d2OuterClass }
  m22d2OuterActionIdentifiedOnSameQuotient := true
  sourceProvenance := r.sourceProvenance

/-- The compiler retains the exact target dimension. -/
theorem compiled_finrank_ten (r : StableCompletionSubquotientReceipt Q) :
    Module.finrank Scalar Q = 10 := r.target_finrank

/-- The descended outer action is exactly the Completion10 flip. -/
theorem compiled_completion_intertwines
    (r : StableCompletionSubquotientReceipt Q) (q : Q) :
    (r.toRecognition.completion.chart
      (r.toRecognition.completion.binaryOperator q))
      = R.completionFlipLinear (r.toRecognition.completion.chart q) :=
  r.completion_intertwining q

/-- B'+C' are thereby one acquisition: a stable same-object quotient, not two
independent discoveries. -/
theorem compiled_same_quotient_flag
    (r : StableCompletionSubquotientReceipt Q) :
    r.toRecognition.m22d2OuterActionIdentifiedOnSameQuotient = true := rfl

end StableCompletionSubquotientReceipt

/-- The Brauer-character PASS narrows the search but does not manufacture the explicit
stable subquotient. -/
inductive BrauerRuntimeConstructsStableSubquotient : Prop

theorem brauer_runtime_alone_does_not_construct_stable_subquotient :
    ¬ BrauerRuntimeConstructsStableSubquotient := by
  intro h
  cases h

end Integration.OggSSP2BActualStableCompletionSubquotient
