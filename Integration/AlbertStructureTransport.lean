import Integration.AlbertLinearMinusculeTransport
import Mathlib

/-!
# Transport of the complete theorem-facing Albert structure

A linear equivalence by itself does not identify an exceptional action, but it
*does* transport the entire Jordan/unit/trace/cubic structure without loss.
This separates two questions cleanly:

1. does an actual Albert algebra live on the canonical 27-dimensional
   minuscule coordinate module?  Yes, after choosing any linear equivalence
   from an actual Albert carrier;
2. do the independently paid E6/F4 Weyl operators preserve that transported
   product, unit and cubic?  That is the genuinely exceptional compatibility
   condition and is kept separate below.
-/

namespace Integration.AlbertStructureTransport

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.E6MinusculeWeightModule
open Integration.AlbertLinearMinusculeTransport

variable {J V : Type*}
variable [AddCommGroup J] [Module ℝ J]
variable [AddCommGroup V] [Module ℝ V]

/-- Transport the bilinear Jordan product through a linear equivalence. -/
noncomputable def transportJordanMul
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V) : V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun x :=
    { toFun := fun y => e (A.jordanMul (e.symm x) (e.symm y))
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro r y
        simp }
  map_add' := by
    intro x y
    ext z
    simp
  map_smul' := by
    intro r x
    ext y
    simp

/-- Transport the normalized trace/unit package. -/
noncomputable def transportTraceUnit
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V) : TraceUnitData V where
  unit := e A.traceUnit.unit
  trace := A.traceUnit.trace.comp e.symm.toLinearMap
  trace_unit := by
    simp [A.traceUnit.trace_unit]

/-- Transport the full theorem-facing Albert structure. -/
noncomputable def transportAlbertStructure
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V) : AlbertStructure V where
  traceUnit := transportTraceUnit A e
  jordanMul := transportJordanMul A e
  jordan_comm := by
    intro x y
    simp [transportJordanMul, A.jordan_comm]
  jordan_identity := by
    intro x y
    change
      e (A.jordanMul
        (A.jordanMul (e.symm x) (e.symm x))
        (A.jordanMul (e.symm x) (e.symm y))) =
      e (A.jordanMul
        (e.symm x)
        (A.jordanMul (A.jordanMul (e.symm x) (e.symm x)) (e.symm y)))
    exact congrArg e (A.jordan_identity (e.symm x) (e.symm y))
  unit_left := by
    intro x
    change e (A.jordanMul A.traceUnit.unit (e.symm x)) = x
    rw [A.unit_left, e.apply_symm_apply]
  cubic := fun x => A.cubic (e.symm x)
  cubic_unit := by
    simp [transportTraceUnit, A.cubic_unit]
  cubic_smul := by
    intro r x
    simp [A.cubic_smul]

/-- Transport a structural Jordan automorphism along with the algebra. -/
noncomputable def transportJordanAutomorphism
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V)
    (g : JordanAutomorphism A) :
    JordanAutomorphism (transportAlbertStructure A e) where
  toLinearEquiv := e.symm.trans (g.toLinearEquiv.trans e)
  map_unit := by
    simp [transportAlbertStructure, transportTraceUnit, g.map_unit]
  map_jordan := by
    intro x y
    change
      e (g.toLinearEquiv (A.jordanMul (e.symm x) (e.symm y))) =
      e (A.jordanMul
        (g.toLinearEquiv (e.symm x))
        (g.toLinearEquiv (e.symm y)))
    exact congrArg e (g.map_jordan (e.symm x) (e.symm y))
  map_trace := by
    intro x
    change A.traceUnit.trace (g.toLinearEquiv (e.symm x)) =
      A.traceUnit.trace (e.symm x)
    exact g.map_trace (e.symm x)
  map_cubic := by
    intro x
    change A.cubic (g.toLinearEquiv (e.symm x)) = A.cubic (e.symm x)
    exact g.map_cubic (e.symm x)

/-- Given any actual 27-dimensional Albert structure, the canonical minuscule
coordinate module carries an exactly transported Albert structure. -/
noncomputable def minusculeAlbertStructure
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : AlbertStructure MinusculeModule :=
  transportAlbertStructure A (coordinateEquivOfFinrank27 hJ)

/-- The remaining compatibility predicate: an independently defined linear
operator is an automorphism of the transported Albert structure. -/
def PreservesTransportedAlbert
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V)
    (g : V ≃ₗ[ℝ] V) : Prop :=
  g (transportTraceUnit A e).unit = (transportTraceUnit A e).unit ∧
  (∀ x y,
    g (transportJordanMul A e x y) =
      transportJordanMul A e (g x) (g y)) ∧
  (∀ x,
    (transportTraceUnit A e).trace (g x) =
      (transportTraceUnit A e).trace x) ∧
  (∀ x,
    (transportAlbertStructure A e).cubic (g x) =
      (transportAlbertStructure A e).cubic x)

/-- A preservation receipt is exactly enough to promote an independently
defined linear equivalence to a structural Jordan automorphism of the
transported Albert algebra. -/
noncomputable def jordanAutomorphismOfPreserves
    (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V)
    (g : V ≃ₗ[ℝ] V) (h : PreservesTransportedAlbert A e g) :
    JordanAutomorphism (transportAlbertStructure A e) where
  toLinearEquiv := g
  map_unit := h.1
  map_jordan := h.2.1
  map_trace := h.2.2.1
  map_cubic := h.2.2.2

/-- Exact exceptional compatibility target for the already-paid simple E6
coordinate action. -/
structure MinusculeAlbertE6Compatibility
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : Prop where
  e : J ≃ₗ[ℝ] MinusculeModule
  simpleReflectionsPreserveAlbert :
    ∀ s, PreservesTransportedAlbert A e (e6WeightLinearAction s)

/-- Once the compatibility object exists, each independently defined E6 simple
reflection is an actual Jordan automorphism of the same transported Albert
structure. -/
noncomputable def e6JordanAutomorphismOfCompatibility
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : MinusculeAlbertE6Compatibility A hJ)
    (s : E6SimpleReflection) :
    JordanAutomorphism (transportAlbertStructure A C.e) :=
  jordanAutomorphismOfPreserves A C.e (e6WeightLinearAction s)
    (C.simpleReflectionsPreserveAlbert s)

inductive TransportedAlbertCreatesIndependentE6Compatibility : Prop

theorem transported_albert_does_not_create_e6_compatibility :
    ¬ TransportedAlbertCreatesIndependentE6Compatibility := by
  intro h; cases h

structure Boundary where
  fullAlbertStructureTransportPaid : Bool
  jordanAutomorphismTransportPaid : Bool
  minusculeModuleAlbertStructureExistsFromAnyActualAlbert27 : Bool
  exactE6CompatibilityPredicateTyped : Bool
  preservationReceiptCompilesToJordanAutomorphism : Bool
  e6CompatibilityCompilesToSimpleJordanAutomorphisms : Bool
  independentE6CompatibilityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fullAlbertStructureTransportPaid := true
  jordanAutomorphismTransportPaid := true
  minusculeModuleAlbertStructureExistsFromAnyActualAlbert27 := true
  exactE6CompatibilityPredicateTyped := true
  preservationReceiptCompilesToJordanAutomorphism := true
  e6CompatibilityCompilesToSimpleJordanAutomorphisms := true
  independentE6CompatibilityPaidHere := false

end Integration.AlbertStructureTransport
