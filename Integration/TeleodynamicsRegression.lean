import Integration.TeleodynamicsCore

namespace Integration.Teleodynamics

example : |demoCorrelation.value| ≤ 1 := correlation_abs_le_one demoCorrelation

example : 0 ≤ coherenceDensity demoTensor := coherenceDensity_nonneg demoTensor

example : |demoAlignment.value| ≤ 1 := normalizedOverlap_abs_le_one demoAlignment

example : demoGradient.dPsi ≤ 0 := gradientFlow_nonincreasing demoGradient

example : consensusEnergyDerivative 2 3 1 ≤ 0 := by
  exact consensusEnergyDerivative_nonpos (by norm_num : (0 : ℝ) ≤ 2) 3 1

example : demoZeno.effectiveRate ≤ demoZeno.baselineRate :=
  zenoRate_le_baseline demoZeno

example : canonicalAuthorityBoundary.aboutnessAndCoherenceSeparated = true := rfl
example : canonicalAuthorityBoundary.companionTensorTypedRepair = true := rfl
example : canonicalAuthorityBoundary.berryGeometryEstablished = false := rfl
example : canonicalAuthorityBoundary.equalQualiaCoordinatesImplySamePhenomenology = false := rfl
example : canonicalAuthorityBoundary.nonlocalTransmissionEstablished = false := rfl

end Integration.Teleodynamics
