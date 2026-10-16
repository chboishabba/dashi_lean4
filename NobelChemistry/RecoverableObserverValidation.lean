import NobelChemistry.RecoverableObserver

namespace NobelChemistry

example : reopenPhaseMagnitude (phaseLabel ChiralBias.leftSeed) (magnitudeCode ChiralBias.leftSeed) = ChiralBias.leftSeed := by rfl
example : realifiedObserver ChiralBias.leftSeed = RealifiedSector.transverse := by rfl
example : realifiedObserver ChiralBias.rightSeed = RealifiedSector.transverse := by rfl
example : phaseLabel (mirror ChiralBias.leftSeed) = conjugatePhaseLabel (phaseLabel ChiralBias.leftSeed) := by rfl
example : phaseValue (conjugatePhaseLabel PhaseLabel.zeta) = Complex.conj (phaseValue PhaseLabel.zeta) := by
  simpa using phaseValue_conjugate PhaseLabel.zeta

end NobelChemistry
