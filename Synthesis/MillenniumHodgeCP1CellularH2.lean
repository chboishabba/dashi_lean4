import Synthesis.MillenniumHodgeCP1TopologicalSphere
import Mathlib.Tactic

/-!
# Exact cellular H² model for CP¹ ≃ S²

Mathlib currently has the topology/manifold/CW infrastructure for spheres but
does not yet provide the homology-of-spheres computation.  We therefore make
the standard two-cell cochain calculation explicit rather than postulating a
singular cohomology theorem.

The CW model of S² has one 0-cell and one 2-cell and no 1-cells.  With rational
coefficients the degree-two cochain group is Q and both adjacent differentials
are zero, so H²_cell is literally Q.

The point-divisor generator is sent to 1.  The only remaining topological
same-object theorem is cellular cohomology = singular cohomology for the actual
sphere/CP¹ carrier.
-/

namespace Synthesis.Millennium.Hodge

structure CP1CellularCochain where
  degreeTwo : ℚ
deriving DecidableEq

def cellularZero : CP1CellularCochain :=
  ⟨0⟩

def cellularAdd
    (a b : CP1CellularCochain) :
    CP1CellularCochain :=
  ⟨a.degreeTwo + b.degreeTwo⟩

def cellularScale
    (q : ℚ)
    (a : CP1CellularCochain) :
    CP1CellularCochain :=
  ⟨q * a.degreeTwo⟩

def cellularCoboundaryFromDegreeOne
    (_ : PUnit) :
    CP1CellularCochain :=
  cellularZero

def cellularCoboundaryToDegreeThree
    (_ : CP1CellularCochain) :
    PUnit :=
  PUnit.unit

theorem cellular_d_squared_zero
    (x : PUnit) :
    cellularCoboundaryToDegreeThree
      (cellularCoboundaryFromDegreeOne x)
      = PUnit.unit :=
  rfl

def CP1CellularH2 :=
  ℚ

def cochainToH2
    (c : CP1CellularCochain) :
    CP1CellularH2 :=
  c.degreeTwo

def h2ToCochain
    (q : CP1CellularH2) :
    CP1CellularCochain :=
  ⟨q⟩

theorem cochain_h2_left_inverse
    (c : CP1CellularCochain) :
    h2ToCochain (cochainToH2 c) = c := by
  cases c
  rfl

theorem cochain_h2_right_inverse
    (q : CP1CellularH2) :
    cochainToH2 (h2ToCochain q) = q :=
  rfl

def cellularH2Equiv :
    CP1CellularCochain ≃ CP1CellularH2 where
  toFun := cochainToH2
  invFun := h2ToCochain
  left_inv := cochain_h2_left_inverse
  right_inv := cochain_h2_right_inverse

def pointDivisorCellularClass :
    CP1CellularH2 :=
  1

theorem pointDivisorCellularClass_is_generator :
    pointDivisorCellularClass = (1 : ℚ) :=
  rfl

theorem everyCellularH2Class_is_point_multiple
    (q : CP1CellularH2) :
    q = q * pointDivisorCellularClass := by
  simp [pointDivisorCellularClass]

structure CP1CellularToSingularComparison where
  SingularH2 : Type
  toSingular : CP1CellularH2 → SingularH2
  fromSingular : SingularH2 → CP1CellularH2
  leftInverse :
    Function.LeftInverse fromSingular toSingular
  rightInverse :
    Function.RightInverse fromSingular toSingular

def cellularToSingularEquiv
    (comparison : CP1CellularToSingularComparison) :
    CP1CellularH2 ≃ comparison.SingularH2 where
  toFun := comparison.toSingular
  invFun := comparison.fromSingular
  left_inv := comparison.leftInverse
  right_inv := comparison.rightInverse

theorem point_generator_surjects_after_comparison
    (comparison : CP1CellularToSingularComparison)
    (h : comparison.SingularH2) :
    ∃ q : ℚ,
      comparison.toSingular
        (q * pointDivisorCellularClass) = h := by
  refine ⟨comparison.fromSingular h, ?_⟩
  simpa [pointDivisorCellularClass] using
    comparison.rightInverse h

end Synthesis.Millennium.Hodge
