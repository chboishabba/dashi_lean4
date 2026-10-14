import Mathlib.Data.ZMod.Basic
import Integration.OggSSP2BEquivariantRangeInvariant

/-! RED-first regression: range of an equivariant map is invariant. -/
namespace Integration.OggSSP2BEquivariantRangeInvariantRegression

namespace E := Integration.OggSSP2BEquivariantRangeInvariant

abbrev K := ZMod 2
abbrev V := Fin 2 → K

private def act : Bool → V →ₗ[K] V := fun _ => LinearMap.id
private def f : V →ₗ[K] V := LinearMap.id

private theorem hf : E.LinearEquivariant act act f := by
  intro g x
  rfl

example : E.RangeInvariant act f :=
  E.range_invariant_of_equivariant act act f hf

end Integration.OggSSP2BEquivariantRangeInvariantRegression
