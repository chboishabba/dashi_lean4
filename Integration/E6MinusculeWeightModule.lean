import Integration.E6Minuscule27SameObject
import Mathlib.LinearAlgebra.StdBasis
import Mathlib

/-!
# Canonical 27-dimensional coordinate module for the E6 minuscule weights

The finite minuscule orbit itself canonically indexes a real coordinate module
`Omega5Weight -> ℝ`.  This pays the existence of 27 distinct one-dimensional
weight lines independently of any Albert multiplication.  A future Albert weld
must identify an actual `H_3(O)` carrier with this module and prove that the
transported E6 operators preserve the Jordan product and cubic norm; a bare
linear equivalence is not enough.
-/

namespace Integration.E6MinusculeWeightModule

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27SameObject

/-- Canonical real vector space with one coordinate for every omega5 weight. -/
abbrev MinusculeModule := Omega5Weight → ℝ

/-- Its standard coordinate basis. -/
noncomputable def minusculeBasis : Basis Omega5Weight ℝ MinusculeModule :=
  Pi.basisFun ℝ Omega5Weight

/-- Exact dimension 27. -/
theorem minuscule_module_finrank : Module.finrank ℝ MinusculeModule = 27 := by
  rw [Module.finrank_eq_card_basis minusculeBasis]
  exact omega5_weight_card

/-- Basis vector associated to one minuscule weight. -/
noncomputable def weightVector (w : Omega5Weight) : MinusculeModule :=
  minusculeBasis w

@[simp] theorem weightVector_apply (w v : Omega5Weight) :
    weightVector w v = if w = v then 1 else 0 := by
  simp [weightVector, minusculeBasis, Pi.basisFun_apply, Pi.single_apply]

/-- Each coordinate vector is nonzero. -/
theorem weightVector_ne_zero (w : Omega5Weight) : weightVector w ≠ 0 :=
  Basis.ne_zero minusculeBasis w

/-- The actual one-dimensional coordinate line associated to a weight. -/
def coordinateWeightLine (w : Omega5Weight) : Submodule ℝ MinusculeModule :=
  Submodule.span ℝ ({weightVector w} : Set MinusculeModule)

/-- Different minuscule weights determine different coordinate lines. -/
theorem coordinateWeightLine_injective : Function.Injective coordinateWeightLine := by
  intro w v hline
  by_contra hwv
  have hwmem : weightVector w ∈ coordinateWeightLine v := by
    rw [← hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [Submodule.mem_span_singleton] at hwmem
  rcases hwmem with ⟨c, hc⟩
  have heval := congrFun hc w
  have hvw : v ≠ w := Ne.symm hwv
  simp [weightVector_apply, hwv, hvw] at heval

/-- Every omega5 reflection stays in the paid omega5 set. -/
theorem reflectOmega5_mem :
    ∀ s (w : Omega5Weight), reflectLabel s w.1 ∈ minusculeOmega5Set := by
  native_decide

/-- Simple-reflection permutation of the finite weight carrier. -/
def reflectOmega5 (s : E6SimpleReflection) (w : Omega5Weight) : Omega5Weight :=
  ⟨reflectLabel s w.1, reflectOmega5_mem s w⟩

@[simp] theorem reflectOmega5_involutive :
    ∀ s w, reflectOmega5 s (reflectOmega5 s w) = w := by
  native_decide

/-- Reindex coordinates by the involutive Weyl action. -/
noncomputable def e6WeightLinearAction (s : E6SimpleReflection) :
    MinusculeModule ≃ₗ[ℝ] MinusculeModule where
  toFun f := fun w => f (reflectOmega5 s w)
  invFun f := fun w => f (reflectOmega5 s w)
  left_inv f := by
    funext w
    change f (reflectOmega5 s (reflectOmega5 s w)) = f w
    rw [reflectOmega5_involutive]
  right_inv f := by
    funext w
    change f (reflectOmega5 s (reflectOmega5 s w)) = f w
    rw [reflectOmega5_involutive]
  map_add' f g := rfl
  map_smul' r f := rfl

/-- The reindexing action sends each basis vector to the reflected weight's
basis vector. -/
theorem e6_action_maps_weight_vector :
    ∀ s w, e6WeightLinearAction s (weightVector w) =
      weightVector (reflectOmega5 s w) := by
  intro s w
  funext v
  simp [e6WeightLinearAction, weightVector_apply]
  constructor <;> intro h
  · apply congrArg (reflectOmega5 s) at h
    simpa using h
  · simpa [h]

/-- Consequently it maps weight lines exactly. -/
theorem e6_action_maps_weight_line :
    ∀ s w,
      Submodule.map (e6WeightLinearAction s).toLinearMap (coordinateWeightLine w) =
        coordinateWeightLine (reflectOmega5 s w) := by
  intro s w
  rw [coordinateWeightLine, coordinateWeightLine, Submodule.map_span]
  simp [e6_action_maps_weight_vector]

inductive CoordinateWeightModuleCreatesAlbertProduct : Prop
inductive LinearAlbertIdentificationCreatesE6JordanAutomorphisms : Prop

theorem coordinate_module_does_not_create_albert_product :
    ¬ CoordinateWeightModuleCreatesAlbertProduct := by
  intro h; cases h

theorem linear_identification_does_not_create_jordan_automorphisms :
    ¬ LinearAlbertIdentificationCreatesE6JordanAutomorphisms := by
  intro h; cases h

structure Boundary where
  canonicalCoordinateModuleTyped : Bool
  exactDimension27Paid : Bool
  distinctWeightLinesPaid : Bool
  simpleReflectionLinearActionPaid : Bool
  lineIntertwiningPaid : Bool
  albertProductPaidHere : Bool
  e6JordanAutomorphismCompatibilityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  canonicalCoordinateModuleTyped := true
  exactDimension27Paid := true
  distinctWeightLinesPaid := true
  simpleReflectionLinearActionPaid := true
  lineIntertwiningPaid := true
  albertProductPaidHere := false
  e6JordanAutomorphismCompatibilityPaidHere := false

end Integration.E6MinusculeWeightModule
