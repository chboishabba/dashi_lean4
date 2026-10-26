import Mathlib.Data.ZMod.Basic
import Integration.OggSSP2BBlockIdempotentNaturality
import Integration.OggSSP2BSocleForcesUnique24

/-! RED-first regression for the last abstract 2B norm-weld compilers. -/

namespace Integration.OggSSP2BBlockIdempotentNaturalityRegression

abbrev K := ZMod 2
abbrev A := K
abbrev M := Fin 2 → K
abbrev S := Fin 2 → K

private def e : A := 1
private def f : M →ₗ[A] S := LinearMap.id

example (x : M) (hx : e • x = x) : e • f x = f x := by
  exact OggSSP2BBlockIdempotentNaturality.map_preserves_idempotent_block f e x hx

example :
    OggSSP2BBlockIdempotentNaturality.BlockSupported e f.range := by
  exact OggSSP2BBlockIdempotentNaturality.range_block_supported_of_source_block_supported
    f e (by intro x; simp [e])

end Integration.OggSSP2BBlockIdempotentNaturalityRegression

namespace Integration.OggSSP2BSocleForcesUnique24Regression

abbrev K := ZMod 2
abbrev V := Fin 24 → K

private def frob : V →ₗ[K] V := LinearMap.id
private def Inv (W : Submodule K V) : Prop := W = ⊤

private theorem finrankV : Module.finrank K V = 24 := by simp

private def socleReceipt :
    OggSSP2BSocleForcesUnique24.FrobeniusSocleReceipt (K := K) (S := V) frob Inv where
  frobenius_finrank := by simpa [frob] using finrankV
  frobenius_invariant := by simp [Inv, frob]
  frobenius_contained_in_every_nonzero_invariant := by
    intro W hW _
    simpa [Inv, frob] using hW

example :
    OggSSP2BUniqueInvariant24Range.UniqueInvariant24SubmoduleReceipt frob Inv :=
  socleReceipt.toUniqueInvariant24SubmoduleReceipt

end Integration.OggSSP2BSocleForcesUnique24Regression
