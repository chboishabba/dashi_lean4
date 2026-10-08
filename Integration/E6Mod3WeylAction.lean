import Integration.E6Mod3QuadraticBridge
import Mathlib

/-!
# E6 Coxeter generators on the mod-3 quadratic quotient

DASHI derivation from the explicit quotient/isometry in
`E6Mod3QuadraticBridge`.

Local Python first computed the six simple-reflection matrices after reducing
the E6 Cartan lattice modulo 3, quotienting the radical, and conjugating into
the standard `F3Five` coordinates.  Exhaustive checks established:

* each generator is an involution;
* each preserves `standardQuadratic`;
* adjacent E6 generators satisfy the length-three braid relation;
* non-adjacent generators commute.

The definitions below encode those six transformations directly and ask Lean's
finite evaluator to pay the same Coxeter relations.  The Python closure of these
matrices has 51,840 elements and is transitive on the 72-point Q=2 shell, but
that closure cardinality is deliberately left as a diagnostic in this tranche;
it is not promoted to a kernel theorem without a dedicated finite-group owner.
-/

namespace Integration.E6Mod3WeylAction

open Integration.E6Mod3QuadraticBridge

inductive E6SimpleReflection
  | s0 | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Repr, Fintype

/-- Six E6 simple reflections in the standardized five-dimensional F3 quotient. -/
def reflectStandard : E6SimpleReflection → F3Five → F3Five
  | .s0, z => ⟨z.z0, z.z1, z.z2, z.z4, z.z3⟩
  | .s1, z =>
      ⟨2*(z.z1 + z.z2 + z.z3 + z.z4),
       2*(z.z0 + z.z2 + z.z3 + z.z4),
       2*(z.z0 + z.z1 + z.z3 + z.z4),
       2*(z.z0 + z.z1 + z.z2 + z.z4),
       2*(z.z0 + z.z1 + z.z2 + z.z3)⟩
  | .s2, z =>
      ⟨2*z.z1 + 2*z.z2 + 2*z.z3 + z.z4,
       2*z.z0 + 2*z.z2 + 2*z.z3 + z.z4,
       2*z.z0 + 2*z.z1 + 2*z.z3 + z.z4,
       2*z.z0 + 2*z.z1 + 2*z.z2 + z.z4,
       z.z0 + z.z1 + z.z2 + z.z3⟩
  | .s3, z => ⟨2*z.z1, 2*z.z0, z.z2, z.z3, z.z4⟩
  | .s4, z => ⟨z.z2, z.z1, z.z0, z.z3, z.z4⟩
  | .s5, z => ⟨z.z1, z.z0, z.z2, z.z3, z.z4⟩

/-- E6 Dynkin adjacency for the numbering used by the Cartan owner. -/
def coxeterAdjacent : E6SimpleReflection → E6SimpleReflection → Bool
  | .s0, .s2 | .s2, .s0 => true
  | .s1, .s3 | .s3, .s1 => true
  | .s2, .s3 | .s3, .s2 => true
  | .s3, .s4 | .s4, .s3 => true
  | .s4, .s5 | .s5, .s4 => true
  | _, _ => false

theorem simple_reflections_are_involutions :
    ∀ s x, reflectStandard s (reflectStandard s x) = x := by
  native_decide

theorem simple_reflections_preserve_quadratic :
    ∀ s x,
      standardQuadratic (reflectStandard s x) = standardQuadratic x := by
  native_decide

theorem adjacent_generators_satisfy_braid :
    ∀ i j,
      coxeterAdjacent i j = true →
      ∀ x, reflectStandard i (reflectStandard j (reflectStandard i x)) =
        reflectStandard j (reflectStandard i (reflectStandard j x)) := by
  native_decide

theorem nonadjacent_generators_commute :
    ∀ i j,
      i ≠ j → coxeterAdjacent i j = false →
      ∀ x, reflectStandard i (reflectStandard j x) =
        reflectStandard j (reflectStandard i x) := by
  native_decide

/-- The action restricts to the standard Q=2 shell. -/
def StandardQTwoShell := {z : F3Five // standardQuadratic z = 2}
instance : Fintype StandardQTwoShell := inferInstance

def reflectQTwo (s : E6SimpleReflection) (z : StandardQTwoShell) : StandardQTwoShell :=
  ⟨reflectStandard s z.1, by
    rw [simple_reflections_preserve_quadratic]
    exact z.2⟩

theorem reflect_qtwo_involutive :
    ∀ s z, reflectQTwo s (reflectQTwo s z) = z := by
  native_decide

/-- Python diagnostics retained as explicitly non-kernel status coordinates. -/
def pythonGeneratedMatrixClosureOrder : Nat := 51840
def pythonQTwoOrbitSize : Nat := 72

def generatedGroupOrder51840KernelProvedHere : Bool := false

def qTwoTransitivityKernelProvedHere : Bool := false

inductive PythonGroupOrderCreatesKernelTheorem : Prop

theorem pythonGroupOrderCannotCreateKernelTheorem :
    ¬ PythonGroupOrderCreatesKernelTheorem := by
  intro h
  cases h

structure Boundary where
  sixSimpleReflectionsTyped : Bool
  simpleReflectionsAreInvolutions : Bool
  simpleReflectionsPreserveQuadratic : Bool
  e6CoxeterRelationsPaid : Bool
  qTwoShellActionTyped : Bool
  pythonClosureOrderRecorded : Bool
  pythonOrbitSizeRecorded : Bool
  generatedGroupOrder51840KernelProvedHere : Bool
  qTwoTransitivityKernelProvedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixSimpleReflectionsTyped := true
  simpleReflectionsAreInvolutions := true
  simpleReflectionsPreserveQuadratic := true
  e6CoxeterRelationsPaid := true
  qTwoShellActionTyped := true
  pythonClosureOrderRecorded := true
  pythonOrbitSizeRecorded := true
  generatedGroupOrder51840KernelProvedHere := false
  qTwoTransitivityKernelProvedHere := false

end Integration.E6Mod3WeylAction
