import Integration.TeleodynamicsConsensusSpectralGap

namespace Integration.TeleodynamicsConsensusSpectralGapRegression

open Integration.TeleodynamicsConsensusSpectralGap

example {E D dE λ : ℝ}
    (h : SpectralGapEnergyPoint E D dE λ) :
    dE ≤ -2 * λ * E :=
  spectral_gap_gives_energy_differential_inequality h

example : canonicalBoundary.energyDerivativeToGapInequalityPaid = true := rfl
example : canonicalBoundary.pythonExponentialDecayPreflightPassed = true := rfl
example : canonicalBoundary.gronwallIntegrationPaidHere = false := rfl
example : canonicalBoundary.connectivityAloneCreatesPositiveGap = false := rfl

end Integration.TeleodynamicsConsensusSpectralGapRegression
