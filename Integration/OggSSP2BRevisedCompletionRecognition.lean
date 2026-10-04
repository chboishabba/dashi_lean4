import Integration.OggSSP2BM22RuntimeReceipt
import Integration.OggSSP2BM22d2Completion10RuntimeReceipt
import Integration.OggSSP2BM24xS3DuadPhaseNoGo
import Integration.OggSSP2BBinaryTetrahedralDefectSource
import Integration.ThreeC2TateFibreFromGroupConjugacy

/-!
# Revised 2B Completion10 recognition after the runtime max-cut

The finite runtime now says three distinct things:

* positive B-side evidence: the M24 duad module restricted to M22 contains
  actual 10a and 10b composition factors (five copies of each);
* negative old-C result: the unique bare M22 involution acts on both
  ten-dimensional modules with rank(g-I)=4 and fixed dimension 6, so it is not
  the old five-pair Completion10 involution;
* positive revised-C source: in both actual ten-dimensional M22:2 modules, an
  OUTER involution class has rank(g-I)=5, fixed dimension 5 and a verified
  five-swapped-pair spanning basis.  Thus the finite Completion10 phase source
  is found one layer above bare M22.

The remaining C' theorem is no longer discovery of an action.  It is the
same-object statement that this sourced M22:2 outer action is the action on the
same actual 2B Tate subquotient supplied by B'.

The binary-tetrahedral defect meaning is independently sourced as the 2-adic
centralizer exponent profile (3,3,2,1,1).  D still requires a sourced
identification of the recognized five Completion10 modes with those five
order strata.
-/

namespace Integration.OggSSP2BRevisedCompletionRecognition

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture
namespace R := Integration.OggSSP2BM22RuntimeReceipt
namespace CPrime := Integration.OggSSP2BM22d2Completion10RuntimeReceipt
namespace D := Integration.OggSSP2BBinaryTetrahedralDefectSource

abbrev Scalar := ZMod 2
abbrev ActualTate276 := Fin 276 → Scalar
abbrev CompletionModule := F.TenState → Scalar

/-- Linear permutation operator induced by the existing Completion10
complement involution. -/
def completionFlipLinear : CompletionModule →ₗ[Scalar] CompletionModule where
  toFun v := fun s => v (F.complement s)
  map_add' f g := by
    funext s
    rfl
  map_smul' c f := by
    funext s
    rfl

theorem completionFlipLinear_sq :
    completionFlipLinear.comp completionFlipLinear = LinearMap.id := by
  ext v s
  simp [completionFlipLinear, F.complement_involutive]

/-- B': a genuine ten-dimensional subquotient of the actual Tate module is a
surjective quotient of some actual Tate submodule.  This is the right target
for a composition factor; we do not incorrectly require it to be a literal
coordinate subspace. -/
structure ActualTateTenSubquotientReceipt
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  sourceSubmodule : Submodule Scalar ActualTate276
  quotient : sourceSubmodule →ₗ[Scalar] Q
  quotient_surjective : Function.Surjective quotient
  target_finrank : Module.finrank Scalar Q = 10
  atlasKind : Integration.OggSSP2BM22CompletionTenCandidate.M22TenModuleKind

/-- C': the sourced outer M22:2 operator must act on the SAME quotient from B'
and be conjugate to the repo-native Completion10 complement action. -/
structure LargerCompletionActionReceipt
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  chart : Q ≃ₗ[Scalar] CompletionModule
  binaryOperator : Q →ₗ[Scalar] Q
  binaryOperator_involutive :
    binaryOperator.comp binaryOperator = LinearMap.id
  chart_intertwines_completion :
    ∀ q,
      chart (binaryOperator q) = completionFlipLinear (chart q)
  sourcedFromM22d2OuterClass : Bool

/-- Combined B'+C' same-object target. -/
structure ActualTateCompletionTenRecognition
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  subquotient : ActualTateTenSubquotientReceipt Q
  completion : LargerCompletionActionReceipt Q
  m22d2OuterActionIdentifiedOnSameQuotient : Bool
  sourceProvenance : String

/-- D: once Completion10 is recognized on the actual Q10, its five modes must
be identified with the independently sourced binary-tetrahedral order strata. -/
abbrev ActualModeDefectRecognition := D.FiveModeDefectRecognition

/-- The runtime bare-M22 involution does not meet the old five-pair fingerprint
and therefore cannot by itself inhabit C'. -/
theorem bare_m22_involution_route_is_killed :
    ¬ (R.runtimeBareM22InvolutionRank = R.completionTenFivePairTargetRank
       ∧ R.runtimeBareM22FixedDimension =
          R.completionTenFivePairTargetFixedDimension) :=
  R.bare_m22_involution_cannot_meet_old_five_pair_fingerprint

/-- Revised C' finite discovery is paid: exactly two M22:2 ten-module/class
matches have the J2^5 fingerprint. -/
theorem finite_m22d2_completion_source_is_found :
    CPrime.outerJ2x5MatchCount = 2 :=
  CPrime.outerJ2x5MatchCount_is_two

theorem finite_m22d2_five_pair_basis_is_verified :
    CPrime.tenAOuterCompletionCandidate.fiveSwapPairsVerified = true ∧
    CPrime.tenBOuterCompletionCandidate.fiveSwapPairsVerified = true :=
  CPrime.both_runtime_candidates_have_literal_five_pair_basis

/-- The positive runtime result is still useful: ten-dimensional factor kinds
exist in the finite duad restriction, so B' is now a same-object/source ingress
problem rather than a dimension-existence problem. -/
theorem finite_duad_model_has_ten_factor_multiplicity :
    R.factorMultiplicity .tenA + R.factorMultiplicity .tenB = 10 :=
  R.total_ten_dimensional_factor_multiplicity

/-- The defect profile itself is independently sourced. -/
theorem sourced_defect_profile_paid :
    (D.centralizerTwoAdicExponent .identity,
     D.centralizerTwoAdicExponent .centralMinusOne,
     D.centralizerTwoAdicExponent .orderFour,
     D.centralizerTwoAdicExponent .orderThree,
     D.centralizerTwoAdicExponent .orderSix)
      = (3,3,2,1,1) :=
  D.sourced_defect_profile

/-- Status boundary after the C' max-cut. -/
structure RevisedFrontier where
  finiteTenFactorsObserved : Bool
  tenAAndTenBIdentified : Bool
  bareM22CompletionKilled : Bool
  finiteM22d2CompletionSourceObserved : Bool
  finiteM22d2FivePairBasisVerified : Bool
  actualTateTenSubquotientPaid : Bool
  actualTateCompletionActionPaid : Bool
  sourceDefectInvariantPaid : Bool
  actualModeToDefectStratumRecognitionPaid : Bool
  downstreamThirtyTraceSplitAvailable : Bool
  downstreamP31And279PromotedSameObject : Bool

/-- Only the genuine same-object welds remain false. -/
def canonicalRevisedFrontier : RevisedFrontier where
  finiteTenFactorsObserved := true
  tenAAndTenBIdentified := true
  bareM22CompletionKilled := true
  finiteM22d2CompletionSourceObserved := true
  finiteM22d2FivePairBasisVerified := true
  actualTateTenSubquotientPaid := false
  actualTateCompletionActionPaid := false
  sourceDefectInvariantPaid := true
  actualModeToDefectStratumRecognitionPaid := false
  downstreamThirtyTraceSplitAvailable := true
  downstreamP31And279PromotedSameObject := false

end Integration.OggSSP2BRevisedCompletionRecognition
