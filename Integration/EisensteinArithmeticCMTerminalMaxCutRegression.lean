import Integration.EisensteinArithmeticCMTerminalMaxCutExact

/-!
Terminal regression after the split/local max-cut.

It pins both the newly paid local chain and the still-unpaid global/geometric
promotions.  In particular it prevents the old Cantor-series equality,
Dirichlet/elliptic local-factor collapse, or arithmetic-shell/elliptic-L
collapse from re-entering by simplification of terminology.
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

example : canonicalCubeFibreCharacterCertificatePaid terminalStatus = true := rfl
example : genericCubicJacobiTraceCompilerPaid terminalStatus = true := rfl
example : splitJacobiSixthCyclotomicIntegralityPaid terminalStatus = true := rfl
example : splitJacobiNormSquarePrimePaid terminalStatus = true := rfl
example : sixthCyclotomicToLiteralEisensteinCarrierPaid terminalStatus = true := rfl
example : splitJacobiPulledBackToLiteralEisensteinQAPaid terminalStatus = true := rfl
example : splitJacobiLiteralNormEqualsPrimePaid terminalStatus = true := rfl
example : splitPrimeFrobeniusFormulaPaid terminalStatus = true := rfl
example : splitPrimeLocalEulerPolynomialPaid terminalStatus = true := rfl
example : splitPrimeSixUnitNormalizationPaid terminalStatus = true := rfl
example : allGoodPrimeSameCurveLocalClassificationPaid terminalStatus = true := rfl

example : badPrimeThreeLocalFactorPaid terminalStatus = false := rfl
example : faithfulGeometricCMEmbeddingPaid terminalStatus = false := rfl
example : endomorphismDegreeEqualsNormPaid terminalStatus = false := rfl
example : groessencharacterPaid terminalStatus = false := rfl
example : sameCurveEulerProductAgreementPaid terminalStatus = false := rfl
example : ellipticLSeriesAgreementPaid terminalStatus = false := rfl

example : cantorScaleSeriesIdentifiedWithNormShellSeries terminalStatus = false := rfl
example : dirichletLocalFactorIdentifiedWithEllipticEulerFactor terminalStatus = false := rfl
example : arithmeticShellLSeriesIdentifiedWithEllipticLSeries terminalStatus = false := rfl

example : firstGeometricBlocker terminalStatus = missingGeometricIsogenyDegreeCarrier := rfl
example : firstGlobalArithmeticBlocker terminalStatus = missingBadPrimeThreeLocalFactor := rfl

end Integration.EisensteinArithmeticCMTerminalMaxCutRegression
