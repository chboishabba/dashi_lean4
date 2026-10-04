import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleWeight
import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalization

/-!
# Uniform high-t pole localization: paid equicontinuity, fail-closed determinant cut

The genuine new analytic input is now source-written in
`RiemannProjectiveQuarticFourWindowUniformPoleWeight`:

  |w_{t,c}(u)-w_{t,c}(v)|
    <= 19*cosh(1)*|u-v|

uniformly for t>=200, |c|<=2 and u,v in [-6,6].  This is exactly the
`t`-uniform equicontinuity estimate missing from the older pointwise continuity
proof.

The remaining step is finite-dimensional bookkeeping through the normalized
four-window bump pairings and determinant perturbation bound.  We deliberately
keep that last compiler fail-closed here until kernel replay is available,
rather than importing a private fixed-t helper or claiming a quantifier swap
without a checked proof.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real

/-- Source-written fact: the t-dependent pole weights now have a common
high-t modulus of continuity on the fixed window containing every bump centre. -/
def UniformQuarticFourPoleWeightEquicontinuityPaid : Prop :=
  ∀ t c u v : ℝ,
    200 <= t ->
    |c| <= 2 ->
    u ∈ Set.Icc (-6 : ℝ) 6 ->
    v ∈ Set.Icc (-6 : ℝ) 6 ->
    |quarticFourNormalizedPoleWeight t c u
      - quarticFourNormalizedPoleWeight t c v|
      <= quarticFourUniformPoleLipschitzConstant * |u-v|

theorem uniformQuarticFourPoleWeightEquicontinuity_paid :
    UniformQuarticFourPoleWeightEquicontinuityPaid := by
  intro t c u v ht hc hu hv
  exact quarticFourNormalizedPoleWeight_sub_abs_le_uniform ht hc hu hv

/-- Exact remaining finite compiler target.  Once inhabited, the already-owned
`exists_uniformQuarticFourSignedPoleCore_of_uniformPoleLocalization` produces
one fixed smooth witness width for every t>=200. -/
def UniformQuarticFourPoleDeterminantCompilerTarget : Prop :=
  UniformQuarticFourSmoothPoleLocalization
    quarticFourUniformPoleLocalizationTolerance

/-- The witness-width consequence is already compiled; only the determinant
localization target above remains to be inhabited. -/
theorem fixedWidthCore_of_uniformPoleDeterminantCompilerTarget
    (h : UniformQuarticFourPoleDeterminantCompilerTarget) :
    Nonempty UniformQuarticFourSignedPoleCore :=
  exists_uniformQuarticFourSignedPoleCore_of_uniformPoleLocalization h

end Synthesis
