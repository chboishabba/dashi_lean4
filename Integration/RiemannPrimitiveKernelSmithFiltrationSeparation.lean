import Mathlib
import Integration.RiemannPrimitiveKernelUnimodularBasis
import Integration.RiemannPrimitiveKernelMod243Filtration
import Integration.RiemannPrimitiveKernelExplicitSmithReduction

/-!
# Primitive RH kernel: Smith invariant versus 3-adic filtration

Capstone:
* the integer row is primitive, hence scalar Smith invariant 1;
* the coordinate depth tuple (0,5,5,5) is destroyed by a determinant-one
  column basis change, becoming (0,1,5,5);
* the mod-3^5 kernel is transported exactly by that same basis equivalence.

This separates lattice invariant, coordinate presentation, and filtered object.
-/

namespace Integration.RiemannPrimitiveKernelSmithFiltrationSeparation

open Integration.RiemannPrimitiveKernelUnimodularBasis
open Integration.RiemannPrimitiveKernelMod243Filtration
open Integration.RiemannPrimitiveKernelExplicitSmithReduction

theorem primitive_smith_invariant_one :
    smithInvariant = 1 :=
  smith_invariant_is_one

theorem raw_depth_profile_is_not_basis_invariant :
    transformedDepthProfile ≠ originalDepthProfile :=
  depth_profile_changes

theorem concrete_mod243_kernel_transport (y : Coord4) :
    originalKernel (coordinateEquiv y) ↔ transformedKernel y :=
  intrinsic_kernel_is_transport_invariant y

theorem coordinate_tail_description_changes :
    originalKernel secondBasis ∧ ¬ transformedKernel secondBasis :=
  coordinate_tail_flag_changes

theorem explicit_smith_form_owned :
    smithReduce originalRow = ⟨1,0,0,0⟩ :=
  explicit_smith_normal_form

theorem bare_row_map_surjective :
    Function.Surjective rowMap :=
  row_map_surjective

inductive StructuralLevel
  | scalarSmithInvariant
  | coordinateDepthPresentation
  | transportedFilteredKernel
  deriving DecidableEq, Repr

def primitiveRowLevel : StructuralLevel := .scalarSmithInvariant
def rawDepthTupleLevel : StructuralLevel := .coordinateDepthPresentation
def mod243KernelLevel : StructuralLevel := .transportedFilteredKernel

structure Boundary where
  smithInvariantOneOwned : Bool
  determinantOneCounterexampleOwned : Bool
  rawDepthTupleBasisInvariant : Bool
  mod243KernelTransportOwned : Bool
  explicitSmithOneZeroZeroZeroOwned : Bool
  bareRowMapSurjective : Bool
  coordinateTailDescriptionIntrinsic : Bool
  filteredKernelPreferredForFurtherStructure : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  smithInvariantOneOwned := true
  determinantOneCounterexampleOwned := true
  rawDepthTupleBasisInvariant := false
  mod243KernelTransportOwned := true
  explicitSmithOneZeroZeroZeroOwned := true
  bareRowMapSurjective := true
  coordinateTailDescriptionIntrinsic := false
  filteredKernelPreferredForFurtherStructure := true

end Integration.RiemannPrimitiveKernelSmithFiltrationSeparation
