import Mathlib.Data.ZMod.Basic
import Integration.OggSSP2BCentralizerNormEquivariance

/-! RED-first regression for the source-native norm equivariance compiler. -/

namespace Integration.OggSSP2BCentralizerNormEquivarianceRegression

abbrev K := ZMod 2
abbrev V := Fin 2 → K

private def a : V →ₗ[K] V := LinearMap.id
private def g : V →ₗ[K] V := LinearMap.id

example :
    g.comp (OggSSP2BCentralizerNormEquivariance.normMap a) =
      (OggSSP2BCentralizerNormEquivariance.normMap a).comp g := by
  apply OggSSP2BCentralizerNormEquivariance.norm_commutes
  simp [a, g]

end Integration.OggSSP2BCentralizerNormEquivarianceRegression
