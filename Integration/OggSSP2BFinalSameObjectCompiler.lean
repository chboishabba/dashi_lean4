import Integration.OggSSP2BRevisedCompletionRecognition
import Integration.ThreeC2TateFibreCycle

/-!
# Final same-object compiler for the 2B Completion10 programme

After the finite max-cut, discovery is no longer the issue:
* M24-duad restriction has 10a^5 and 10b^5;
* bare M22 is ruled out as the Completion10 involution source;
* M22:2 supplies an outer J2^5 five-pair action on both actual 10-dimensional
  modules;
* the binary-tetrahedral defect invariant is independently sourced.

This file packages exactly the remaining same-object data needed to finish the
original 2B programme:

A'  actual three-fibre Tate transport on the source 276-dimensional Tate
    carrier;
B'  an actual 10-dimensional Tate subquotient;
C'  the sourced M22:2 outer Completion10 action on that SAME quotient;
D   a sourced Mode5 -> binary-tetrahedral order-stratum recognition;
plus natural transport of the selected quotient through all three Tate fibres.

No source receipt is fabricated here.  The point of this compiler is that once
these concrete maps are supplied there is no remaining architectural theorem
between them and the finished core recognition.
-/

namespace Integration.OggSSP2BFinalSameObjectCompiler

namespace R := Integration.OggSSP2BRevisedCompletionRecognition
namespace T := Integration.ThreeC2TateFibreCycle
namespace D := Integration.OggSSP2BBinaryTetrahedralDefectSource

abbrev Scalar := R.Scalar
abbrev ActualTate276 := R.ActualTate276

/-- A': the actual three Tate fibres, with their C3 transport, represented on
one source-compatible 276-dimensional carrier. -/
structure ActualThreeFibreTateTransportReceipt where
  cycle : T.ThreeFibreCycleData
    (M0 := ActualTate276)
    (M1 := ActualTate276)
    (M2 := ActualTate276)
  sourceProvenance : String

/-- Transport of the selected B' quotient itself.  The source submodule in the
first fibre is exactly the one already used by the B'+C' recognition receipt;
the other two are its source-native transported companions. -/
structure SelectedQ10TransportReceipt
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q]
    (recognition : R.ActualTateCompletionTenRecognition Q)
    (transport : ActualThreeFibreTateTransportReceipt) where

  source1 : Submodule Scalar ActualTate276
  source2 : Submodule Scalar ActualTate276

  quotient1 : source1 →ₗ[Scalar] Q
  quotient2 : source2 →ₗ[Scalar] Q
  quotient1_surjective : Function.Surjective quotient1
  quotient2_surjective : Function.Surjective quotient2

  source0_to1 :
    ∀ x : recognition.subquotient.sourceSubmodule,
      transport.cycle.phi01 x.1 ∈ source1
  source1_to2 :
    ∀ x : source1,
      transport.cycle.phi12 x.1 ∈ source2
  source2_to0 :
    ∀ x : source2,
      transport.cycle.phi20 x.1 ∈ recognition.subquotient.sourceSubmodule

  qPhi01 : Q ≃ₗ[Scalar] Q
  qPhi12 : Q ≃ₗ[Scalar] Q
  qPhi20 : Q ≃ₗ[Scalar] Q

  quotient_natural_01 :
    ∀ x : recognition.subquotient.sourceSubmodule,
      qPhi01 (recognition.subquotient.quotient x)
        = quotient1 ⟨transport.cycle.phi01 x.1, source0_to1 x⟩

  quotient_natural_12 :
    ∀ x : source1,
      qPhi12 (quotient1 x)
        = quotient2 ⟨transport.cycle.phi12 x.1, source1_to2 x⟩

  quotient_natural_20 :
    ∀ x : source2,
      qPhi20 (quotient2 x)
        = recognition.subquotient.quotient
            ⟨transport.cycle.phi20 x.1, source2_to0 x⟩

  quotient_cycle_coherent :
    ∀ q : Q, qPhi20 (qPhi12 (qPhi01 q)) = q

/-- Final core receipt.  Its `completion` field is already the same-object B'+C'
receipt, so the outer M22:2 operator is required to act on the very quotient
selected from the actual Tate fibre. -/
structure Final2BCoreRecognition
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  completion : R.ActualTateCompletionTenRecognition Q
  fullTateTransport : ActualThreeFibreTateTransportReceipt
  selectedTransport : SelectedQ10TransportReceipt Q completion fullTateTransport
  defectRecognition : R.ActualModeDefectRecognition
  sourceProvenance : String

namespace Final2BCoreRecognition

variable {Q : Type*} [AddCommGroup Q] [Module Scalar Q]

/-- B': the selected actual Tate quotient has the intended dimension. -/
theorem selected_Q10_has_finrank_ten
    (r : Final2BCoreRecognition Q) :
    Module.finrank Scalar Q = 10 :=
  r.completion.subquotient.target_finrank

/-- C': the action on the same quotient is exactly conjugate to the repo-native
Completion10 binary flip. -/
theorem completion_action_intertwines
    (r : Final2BCoreRecognition Q) (q : Q) :
    r.completion.completion.chart (r.completion.completion.binaryOperator q)
      = R.completionFlipLinear (r.completion.completion.chart q) :=
  r.completion.completion.chart_intertwines_completion q

/-- A': selected Q10 transport closes after the full three-fibre cycle. -/
theorem selected_transport_returns
    (r : Final2BCoreRecognition Q) (q : Q) :
    r.selectedTransport.qPhi20
      (r.selectedTransport.qPhi12 (r.selectedTransport.qPhi01 q)) = q :=
  r.selectedTransport.quotient_cycle_coherent q

/-- D: the recognized mode defect is the independently sourced binary-
tetrahedral centralizer 2-adic exponent. -/
theorem recognized_mode_defect
    (r : Final2BCoreRecognition Q)
    (m : Integration.OggSSP2BFiveByTwoDefectArchitecture.Mode5) :
    Integration.OggSSP2BFiveByTwoDefectArchitecture.defectDepth m
      = D.centralizerTwoAdicExponent
          (r.defectRecognition.modeToOrderStratum m) :=
  r.defectRecognition.defectIntertwines m

end Final2BCoreRecognition

/-- The finite runtime discoveries alone do not inhabit the final source
receipt.  This keeps the same-object boundary explicit. -/
inductive FiniteRuntimeConstructsFinal2BCoreRecognition : Prop

theorem finite_runtime_does_not_construct_final_same_object_receipt :
    ¬ FiniteRuntimeConstructsFinal2BCoreRecognition := by
  intro h
  cases h

end Integration.OggSSP2BFinalSameObjectCompiler
