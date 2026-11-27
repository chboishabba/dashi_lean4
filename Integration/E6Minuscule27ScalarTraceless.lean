import Integration.E6Minuscule27CoordinateModel
import Integration.AlbertScalarTraceless
import Mathlib

/-!
# Exact 1 + 26 split of the minuscule coordinate model

The finite minuscule line action has a canonical 27-dimensional coordinate
module `Coordinate27 = Omega5Weight -> ℝ`.  Normalize coordinate sum by `1/9`,
so that the constant vector has trace `3`, exactly matching the Albert rank-3
trace normalization.

The generic DASHI scalar/traceless theorem then gives an actual linear
splitting and, using the paid 27-cardinality, an exact 26-dimensional trace-zero
subspace.  This is still a coordinate model, not yet the Albert algebra.
-/

namespace Integration.E6Minuscule27ScalarTraceless

open Integration.AlbertScalarTraceless
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27CoordinateModel

/-- Rank-three normalized trace on the 27-coordinate model. -/
noncomputable def normalizedCoordinateTrace : Coordinate27 →ₗ[ℝ] ℝ :=
  (1 / 9 : ℝ) • coordinateSum

/-- The constant vector has trace 3 because there are exactly 27 weights. -/
theorem normalizedCoordinateTrace_constant :
    normalizedCoordinateTrace constantVector = 3 := by
  simp [normalizedCoordinateTrace, coordinateSum, constantVector,
    omega5_weight_card]
  norm_num

/-- The coordinate model is now an instance of the same trace/unit interface
used by the Albert scalar/traceless theorem. -/
noncomputable def coordinateTraceUnitData : TraceUnitData Coordinate27 where
  unit := constantVector
  trace := normalizedCoordinateTrace
  trace_unit := normalizedCoordinateTrace_constant

/-- Exact scalar/traceless linear decomposition of the coordinate model. -/
noncomputable def coordinateScalarTracelessEquiv :
    Coordinate27 ≃ₗ[ℝ] ℝ × Traceless coordinateTraceUnitData :=
  scalarTracelessEquiv coordinateTraceUnitData

/-- The ambient coordinate module really has real dimension 27. -/
theorem coordinate_finrank_27 : Module.finrank ℝ Coordinate27 = 27 := by
  simpa [Coordinate27, omega5_weight_card] using
    (Module.finrank_pi ℝ (ι := Omega5Weight))

/-- Consequently the normalized trace-zero carrier really has dimension 26. -/
theorem coordinate_traceless_finrank_26 :
    Module.finrank ℝ (Traceless coordinateTraceUnitData) = 26 := by
  exact traceless_finrank_eq_26 coordinateTraceUnitData coordinate_finrank_27

/-- The normalized trace kernel is the same zero-sum augmentation carrier; the
factor 1/9 changes normalization, not the kernel. -/
theorem coordinate_traceless_eq_augmentation :
    Traceless coordinateTraceUnitData = Augmentation26 := by
  ext f
  change ((1 / 9 : ℝ) * coordinateSum f = 0) ↔ coordinateSum f = 0
  constructor
  · intro h
    have hn : (1 / 9 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h).resolve_left hn
  · intro h
    simp [h]

structure Boundary where
  ambientFinrank27Paid : Bool
  normalizedTraceUnit3Paid : Bool
  scalarTracelessLinearEquivPaid : Bool
  tracelessFinrank26Paid : Bool
  tracelessEqualsAugmentationPaid : Bool
  augmentationIsAlbertTracelessPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ambientFinrank27Paid := true
  normalizedTraceUnit3Paid := true
  scalarTracelessLinearEquivPaid := true
  tracelessFinrank26Paid := true
  tracelessEqualsAugmentationPaid := true
  augmentationIsAlbertTracelessPaid := false

end Integration.E6Minuscule27ScalarTraceless
