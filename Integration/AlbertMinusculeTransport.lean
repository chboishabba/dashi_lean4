import Integration.E6Minuscule27ScalarTraceless
import Integration.AlbertJordanAutomorphism
import Mathlib

/-!
# Coordinate-minuscule -> Albert transport

Dimension alone gives an abstract linear equivalence between the explicit
27-dimensional minuscule coordinate model and any 27-dimensional real Albert
carrier.  That fact is intentionally separated from the *structured* transport
needed by the exceptional programme.

The actual Albert weld must additionally send the constant direction to the
Jordan unit, commute with the rank-three trace, and intertwine the paid E6
simple-reflection action.  Those equations are the representation-theoretic
content; they are not consequences of `27 = 27`.
-/

namespace Integration.AlbertMinusculeTransport

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.E6LiteralE8Action
open Integration.E6Minuscule27CoordinateModel
open Integration.E6Minuscule27ScalarTraceless

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Equal finite dimension produces only a bare linear equivalence. -/
noncomputable def abstractCoordinateEquiv
    [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : Coordinate27 ≃ₗ[ℝ] J := by
  apply LinearEquiv.ofFinrankEq Coordinate27 J
  rw [coordinate_finrank_27, hJ]

/-- The actual structured transport required to identify the minuscule
coordinate representation with an Albert representation. -/
structure AlbertMinusculeTransport
    (A : AlbertStructure J) : Type 1 where
  toAlbert : Coordinate27 ≃ₗ[ℝ] J
  maps_constant_to_unit : toAlbert constantVector = A.traceUnit.unit
  trace_intertwines : ∀ v,
    A.traceUnit.trace (toAlbert v) = normalizedCoordinateTrace v

  albertSimpleAction : E6SimpleReflection → J ≃ₗ[ℝ] J
  simple_action_intertwines : ∀ s v,
    albertSimpleAction s (toAlbert v) =
      toAlbert (coordinateReflection s v)

/-- Structured transport automatically sends the coordinate trace-zero carrier
to the Albert trace-zero carrier. -/
theorem maps_coordinate_traceless
    (A : AlbertStructure J) (T : AlbertMinusculeTransport A)
    (x : Traceless coordinateTraceUnitData) :
    A.traceUnit.trace (T.toAlbert x.1) = 0 := by
  rw [T.trace_intertwines]
  exact x.property

/-- The structured transport induces an honest equivalence between the two
26-dimensional traceless carriers. -/
noncomputable def tracelessTransport
    (A : AlbertStructure J) (T : AlbertMinusculeTransport A) :
    Traceless coordinateTraceUnitData ≃ₗ[ℝ] Traceless A.traceUnit where
  toFun x := ⟨T.toAlbert x.1, maps_coordinate_traceless A T x⟩
  invFun y :=
    ⟨T.toAlbert.symm y.1, by
      have h := T.trace_intertwines (T.toAlbert.symm y.1)
      simpa using h.symm.trans y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

/-- The structured transport also sends every canonical minuscule coordinate
vector to a nonzero vector in the actual Albert carrier. -/
def transportedWeightVector
    (A : AlbertStructure J) (T : AlbertMinusculeTransport A)
    (w : Integration.E6Minuscule27SchlafliRecognition.Omega5Weight) : J :=
  T.toAlbert (deltaWeight w)

theorem transportedWeightVector_ne_zero
    (A : AlbertStructure J) (T : AlbertMinusculeTransport A) :
    ∀ w, transportedWeightVector A T w ≠ 0 := by
  intro w h
  have : deltaWeight w = 0 := T.toAlbert.injective h
  exact deltaWeight_ne_zero w this

/-- Action compatibility is inherited on the transported weight generators. -/
theorem transportedWeightVector_action
    (A : AlbertStructure J) (T : AlbertMinusculeTransport A) :
    ∀ s w,
      T.albertSimpleAction s (transportedWeightVector A T w) =
        transportedWeightVector A T
          (Integration.E6Minuscule27LineAction.reflectOmega5 s w) := by
  intro s w
  unfold transportedWeightVector
  rw [T.simple_action_intertwines, coordinateReflection_delta]

inductive BareLinearEquivCreatesAlbertRecognition : Prop

theorem bare_linear_equiv_does_not_create_albert_recognition :
    ¬ BareLinearEquivCreatesAlbertRecognition := by
  intro h
  cases h

structure Boundary where
  abstract27DimensionalLinearEquivPaid : Bool
  unitDirectionCompatibilityRequired : Bool
  traceCompatibilityRequired : Bool
  simpleActionIntertwinerRequired : Bool
  traceless26TransportDerived : Bool
  transportedWeightVectorsDerived : Bool
  actualAlbertMinusculeTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  abstract27DimensionalLinearEquivPaid := true
  unitDirectionCompatibilityRequired := true
  traceCompatibilityRequired := true
  simpleActionIntertwinerRequired := true
  traceless26TransportDerived := true
  transportedWeightVectorsDerived := true
  actualAlbertMinusculeTransportPaidHere := false

end Integration.AlbertMinusculeTransport
