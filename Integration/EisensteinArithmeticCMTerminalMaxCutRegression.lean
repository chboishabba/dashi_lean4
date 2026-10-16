import Integration.EisensteinArithmeticCMTerminalMaxCutExact

/-!
RED-first terminal regression for the original Eisenstein thread.

It pins what is now genuinely paid and, equally importantly, the first
unpaid geometric and split-character promotions.  The obsolete Cantor-series
equality is not allowed to re-enter as a substitute for the same-object CM chain.
-/

namespace Integration.EisensteinArithmeticCMTerminalMaxCutRegression

open Integration.EisensteinArithmeticCMTerminalMaxCutExact

example : universalNormShellFormulaPaid terminalStatus = true := rfl
example : arithmeticDirichletFactorizationPaid terminalStatus = true := rfl
example : nativeJZeroPointGroupPaid terminalStatus = true := rfl
example : eisensteinQuadraticEndomorphismRelationPaid terminalStatus = true := rfl
example : sameIntegralCarrierOrderActionPaid terminalStatus = true := rfl
example : inertPrimeSamePrimeWeldPaid terminalStatus = true := rfl
example : inertPrimeTraceZeroPaid terminalStatus = true := rfl
example : inertPrimeLocalEulerShapePaid terminalStatus = true := rfl
example : genericCubicJacobiTraceCompilerPaid terminalStatus = true := rfl
example : orderThreeMulCharExistenceAvailableInMathlib terminalStatus = true := rfl

example : cantorScaleSeriesIdentifiedWithNormShellSeries terminalStatus = false := rfl
example : faithfulGeometricCMEmbeddingPaid terminalStatus = false := rfl
example : endomorphismDegreeEqualsNormPaid terminalStatus = false := rfl
example : canonicalCubeFibreCharacterCertificatePaid terminalStatus = false := rfl
example : jacobiSumEvaluatedAsEisensteinPrimePaid terminalStatus = false := rfl
example : splitPrimeFrobeniusFormulaPaid terminalStatus = false := rfl
example : heckeCharacterPaid terminalStatus = false := rfl
example : allGoodPrimeLocalEulerFactorAgreementPaid terminalStatus = false := rfl
example : ellipticLSeriesAgreementPaid terminalStatus = false := rfl
example : dirichletLocalFactorIdentifiedWithEllipticEulerFactor terminalStatus = false := rfl

example : firstGeometricBlocker terminalStatus = missingGeometricIsogenyDegreeCarrier := rfl
example : firstSplitArithmeticBlocker terminalStatus = missingCanonicalCubicCharacterCertificate := rfl

end Integration.EisensteinArithmeticCMTerminalMaxCutRegression
