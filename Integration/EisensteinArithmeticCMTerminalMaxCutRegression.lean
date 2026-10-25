import Integration.EisensteinArithmeticCMTerminalMaxCutExact

/-!
Terminal regression after the finite/local max-cut.

It pins paid good-prime closure, both literal bad-prime reductions, and the
remaining global/geometric promotions.  External 36a1 metadata is provenance,
not proof authority.
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

example : arbitraryOrderThreeKernelEqualsCubesPaid terminalStatus = true := rfl
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

example : external36a1MetadataReceiptRecorded terminalStatus = true := rfl
example : badPrimeTwoLiteralReductionPaid terminalStatus = true := rfl
example : badPrimeTwoSingularityPaid terminalStatus = true := rfl
example : badPrimeTwoPointCountPaid terminalStatus = true := rfl
example : badPrimeThreeLiteralReductionPaid terminalStatus = true := rfl
example : badPrimeThreeSingularityPaid terminalStatus = true := rfl
example : badPrimeThreePointCountPaid terminalStatus = true := rfl
example : badPrimeReductionTypesPaid terminalStatus = false := rfl
example : badPrimeEllipticLocalFactorsPaid terminalStatus = false := rfl

example : faithfulGeometricCMEmbeddingPaid terminalStatus = false := rfl
example : endomorphismDegreeEqualsNormPaid terminalStatus = false := rfl
example : groessencharacterPaid terminalStatus = false := rfl
example : sameCurveEulerProductAgreementPaid terminalStatus = false := rfl
example : ellipticLSeriesAgreementPaid terminalStatus = false := rfl

example : cantorScaleSeriesIdentifiedWithNormShellSeries terminalStatus = false := rfl
example : dirichletLocalFactorIdentifiedWithEllipticEulerFactor terminalStatus = false := rfl
example : arithmeticShellLSeriesIdentifiedWithEllipticLSeries terminalStatus = false := rfl

example : firstGeometricBlocker terminalStatus = missingGeometricIsogenyDegreeCarrier := rfl
example : firstGlobalArithmeticBlocker terminalStatus = missingBadPrimeReductionTypesAndLocalFactors := rfl

end Integration.EisensteinArithmeticCMTerminalMaxCutRegression
