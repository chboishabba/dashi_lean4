import Mathlib.Data.ZMod.Basic
import Integration.OggSSP2BUniqueRangeNormWeld

/-! RED-first regression for the direct image-level norm weld. -/
namespace Integration.OggSSP2BUniqueRangeNormWeldRegression

namespace U := Integration.OggSSP2BUniqueInvariant24Range
namespace W := Integration.OggSSP2BUniqueRangeNormWeld

abbrev K := ZMod 2
abbrev V := Fin 24 → K

private def residual : V →ₗ[K] V := LinearMap.id
private def frob : V →ₗ[K] V := LinearMap.id
private def Inv (X : Submodule K V) : Prop := X = ⊤

private def unique : U.UniqueInvariant24SubmoduleReceipt (K := K) (S := V) frob Inv where
  frobenius_range_finrank_eq_24 := by simp [frob]
  frobenius_invariant := by simp [Inv, frob]
  unique_invariant_24 := by
    intro X _ hX
    simpa [Inv, frob] using hX

example : residual.range = frob.range :=
  W.residual_range_eq_frobenius_from_unique_target
    residual frob unique (by simp [residual]) (by simp [Inv, residual])

end Integration.OggSSP2BUniqueRangeNormWeldRegression
