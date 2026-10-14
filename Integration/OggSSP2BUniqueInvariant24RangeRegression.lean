import Mathlib.LinearAlgebra.Dimension.Finite
import Integration.OggSSP2BUniqueInvariant24Range

/-! RED-first regression for the image-level Frobenius weld. -/
namespace Integration.OggSSP2BUniqueInvariant24RangeRegression

namespace U := Integration.OggSSP2BUniqueInvariant24Range

abbrev K := ZMod 2
abbrev V := Fin 24 → K

private def f : V →ₗ[K] V := LinearMap.id
private def frob : V →ₗ[K] V := LinearMap.id
private def Inv (W : Submodule K V) : Prop := True

private theorem finrankV : Module.finrank K V = 24 := by simp

private def unique : U.UniqueInvariant24SubmoduleReceipt (K := K) (S := V) frob Inv where
  frobenius_range_finrank_eq_24 := by simpa [frob] using finrankV
  frobenius_invariant := trivial
  unique_invariant_24 := by
    intro W hW _
    apply le_antisymm
    · exact le_top
    · rw [show frob.range = ⊤ by simp [frob]]
      exact (eq_top_of_finrank_eq (by simpa [finrankV] using hW)).ge

example : f.range = frob.range := by
  apply unique.range_eq_frobenius
  · simpa [f] using finrankV
  · trivial

end Integration.OggSSP2BUniqueInvariant24RangeRegression
