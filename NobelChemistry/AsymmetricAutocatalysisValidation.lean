import NobelChemistry.AsymmetricAutocatalysis

namespace NobelChemistry

example : mirror (mirror ChiralBias.leftSeed) = ChiralBias.leftSeed := by
  rfl

example : phase (mirror ChiralBias.leftSeed) = Complex.conj (phase ChiralBias.leftSeed) := by
  simpa using phase_mirror_eq_conj ChiralBias.leftSeed

end NobelChemistry
