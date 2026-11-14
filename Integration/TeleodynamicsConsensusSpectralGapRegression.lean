import Integration.TeleodynamicsConsensusSpectralGap

namespace Integration.TeleodynamicsConsensusSpectralGapRegression

open Integration.TeleodynamicsConsensusSpectralGap

example {E D dE lam : ℝ}
    (h : SpectralGapEnergyPoint E D dE lam) :
    dE ≤ -2 * lam * E :=
  spectral_gap_gives_energy_differential_inequality h

example : canonicalBoundary.energyDerivativeToGapInequalityPaid = true := rfl
example : canonicalBoundary.pythonExponentialDecayPreflightPassed = true := rfl
example : canonicalBoundary.gronwallIntegrationPaidHere = false := rfl
example : canonicalBoundary.connectivityAloneCreatesPositiveGap = false := rfl

end Integration.TeleodynamicsConsensusSpectralGapRegression
