import Mathlib
import AgdaMirror.DimensionFixedPoint

/-!
# Lean mirror of `DASHI/Algebra/Quantum/DimensionFixedPointInstance.agda`
(genuine, fully proved)

A fully concrete (minimal) instance of the holographic dimension-fixed-point
interface: the carrier is `Nat`, all operations total, and the stability
predicate is `D = 4`.  Feeding it through the already-proved extraction
`stableDim_eq_four` yields the concrete statement that every stable dimension of
this instance is `4`.
-/

namespace AgdaMirror.DimensionFixedPointInstance

open AgdaMirror.DimensionFixedPoint

/-- The concrete instance. -/
def dimensionFixedPointAxioms : DimensionFixedPointAxioms where
  R := Nat
  Rpow := fun _ _ => 0
  Rle := fun _ _ => True
  Rmul := fun _ _ => 0
  k := 0
  StableFixedPoint := fun D => D = 4
  HolographicBound := fun _ _ => trivial
  StabilityUnderDecimation := fun _ h => h

/-- The extraction specialised to the concrete instance: every stable dimension
is `4`. -/
theorem instance_stableDim_eq_four {D : Nat}
    (h : dimensionFixedPointAxioms.StableFixedPoint D) : D = 4 :=
  stableDim_eq_four dimensionFixedPointAxioms h

/-- The concrete instance does have a stable fixed point at `4`. -/
theorem instance_four_stable : dimensionFixedPointAxioms.StableFixedPoint 4 := rfl

end AgdaMirror.DimensionFixedPointInstance
