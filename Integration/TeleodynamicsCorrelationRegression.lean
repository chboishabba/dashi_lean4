import Integration.TeleodynamicsCorrelation

namespace Integration.TeleodynamicsCorrelationRegression

open Integration.TeleodynamicsCorrelation

example {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x y : F) : |normalizedCorrelation x y| ≤ 1 :=
  normalizedCorrelation_abs_le_one x y

example {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (input : NondegenerateCorrelationInput F) : |cTensorEntry input| ≤ 1 :=
  cTensorEntry_abs_le_one input

example : canonicalBoundary.statisticalCorrelationRequiresNonzeroVariance = true := rfl
example : canonicalBoundary.boundDerivedFromCauchySchwarz = true := rfl
example : canonicalBoundary.boundEstablishesConsciousnessMeasure = false := rfl

end Integration.TeleodynamicsCorrelationRegression
