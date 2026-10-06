import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Teleodynamic normalized cross-correlation

This is the quantitative backend for the Principia-II C-tensor entry shape.
For centered observable and centered rate vectors in a real inner-product space,
the normalized inner product has absolute value at most one by Mathlib's
Cauchy-Schwarz theorem.

The algebraic normalized expression is total in Lean, including zero norms.
The source statistical interpretation as a normalized covariance is therefore
kept behind an explicit nonzero-variance/nonzero-norm input record.
-/

namespace Integration.TeleodynamicsCorrelation

open scoped InnerProductSpace

universe u

variable {F : Type u} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def normalizedCorrelation (x y : F) : ℝ :=
  ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)

theorem normalizedCorrelation_abs_le_one (x y : F) :
    |normalizedCorrelation x y| ≤ 1 := by
  simpa [normalizedCorrelation] using
    abs_real_inner_div_norm_mul_norm_le_one x y

/-- Statistical-validity gate for the source normalized-covariance reading. -/
structure NondegenerateCorrelationInput (F : Type u)
    [SeminormedAddCommGroup F] [InnerProductSpace ℝ F] where
  centeredObservable : F
  centeredRate : F
  observableNonzero : centeredObservable ≠ 0
  rateNonzero : centeredRate ≠ 0

noncomputable def cTensorEntry (input : NondegenerateCorrelationInput F) : ℝ :=
  normalizedCorrelation input.centeredObservable input.centeredRate

theorem cTensorEntry_abs_le_one (input : NondegenerateCorrelationInput F) :
    |cTensorEntry input| ≤ 1 := by
  exact normalizedCorrelation_abs_le_one _ _

theorem cTensorEntry_mem_Icc (input : NondegenerateCorrelationInput F) :
    cTensorEntry input ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨neg_le_of_abs_le (cTensorEntry_abs_le_one input),
    le_of_abs_le (cTensorEntry_abs_le_one input)⟩

structure Boundary where
  normalizedInnerProductTyped : Bool
  statisticalCorrelationRequiresNonzeroVariance : Bool
  boundDerivedFromCauchySchwarz : Bool
  boundEstablishesConsciousnessMeasure : Bool
  boundEstablishesPhysicalCoupling : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  normalizedInnerProductTyped := true
  statisticalCorrelationRequiresNonzeroVariance := true
  boundDerivedFromCauchySchwarz := true
  boundEstablishesConsciousnessMeasure := false
  boundEstablishesPhysicalCoupling := false

end Integration.TeleodynamicsCorrelation
