import Integration.RationalOctonionDivisionNorm
import Integration.RationalAlbertF4SplitRootDatumReceipt
import Integration.RationalAlbertF4RealPlaceCompactnessReceipt

/-!
# Rational Albert / F4 scalar-extension and local-form boundary

The current exceptional programme contains three logically different pieces of
form information which must not be collapsed:

1. on the native `ℚ` octonion carrier, the positive eight-square composition
   norm is anisotropic and there are no zero divisors;
2. after passing to the companion splitting chart `ℚ(i)`, the Albert derivation
   representation has the exact `4 + 48` F4 root-space grading;
3. at the real place, an exact rational trace-form computation is positive
   definite on the represented 52-dimensional derivation algebra.

The second item is a scalar-extension/splitting statement.  It does **not** say
that the original `ℚ`-form is split.  The third item is a real-place diagnostic
and does **not** determine the global rational form.  A genuine original-Q-form
classification must identify the relevant algebraic group/form on the same
native object, with whatever finite-place/global classification input the
chosen theorem requires.
-/

namespace Integration.RationalAlbertF4ScalarExtensionFormBoundary

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalCayleyDicksonOctonion.RationalOctonion
open Integration.RationalAlbertF4SplitRootDatumReceipt
open Integration.RationalAlbertF4RealPlaceCompactnessReceipt

/-- The strongest theorem-bearing native-Q invariant currently available: the
literal octonion norm vanishes exactly at zero. -/
theorem native_q_octonion_norm_anisotropic (x : RationalOctonion) :
    normSq x = 0 ↔ x = 0 :=
  normSq_eq_zero_iff x

/-- The companion exact root-space producer is explicitly a `Q(i)` chart. -/
theorem companion_root_chart_is_qi : companionExactQI.splittingField = "Q(i)" := rfl

structure Boundary where
  nativeQOctonionNormAnisotropic : Bool
  nativeQOctonionNoZeroDivisors : Bool
  qiRootDecompositionPaid : Bool
  qiRootDecompositionIsScalarExtensionData : Bool
  qiRootDecompositionClassifiesOriginalQForm : Bool
  realPlacePositiveTraceDiagnosticPaid : Bool
  realPlaceDiagnosticClassifiesOriginalQForm : Bool
  allFinitePlacesClassified : Bool
  allLocalPlacesClassified : Bool
  originalQFormClassificationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  nativeQOctonionNormAnisotropic := true
  nativeQOctonionNoZeroDivisors := true
  qiRootDecompositionPaid := true
  qiRootDecompositionIsScalarExtensionData := true
  qiRootDecompositionClassifiesOriginalQForm := false
  realPlacePositiveTraceDiagnosticPaid := true
  realPlaceDiagnosticClassifiesOriginalQForm := false
  allFinitePlacesClassified := false
  allLocalPlacesClassified := false
  originalQFormClassificationPaid := false

inductive QISplittingCreatesOriginalQFormClassification : Prop
inductive RealPlaceCreatesOriginalQFormClassification : Prop

/-- A root decomposition visible only after the declared splitting-field
extension cannot be promoted, by itself, to a classification of the original
rational form. -/
theorem qi_splitting_does_not_create_original_q_form_classification :
    ¬ QISplittingCreatesOriginalQFormClassification := by
  intro h
  cases h

/-- One archimedean-place diagnostic does not by itself classify the global
rational form. -/
theorem real_place_does_not_create_original_q_form_classification :
    ¬ RealPlaceCreatesOriginalQFormClassification := by
  intro h
  cases h

end Integration.RationalAlbertF4ScalarExtensionFormBoundary
