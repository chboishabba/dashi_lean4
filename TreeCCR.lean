import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/TreeCCR.agda` (faithful interface + witness)

The tree-CCR refinement interface: an abstract carrier with a depth-indexed leaf
count, a depth-indexed induced Hilbert space, and a refinement map raising depth
by one.  Following the honesty discipline the abstract data are honest structure
fields; we back the interface with a genuine binary-tree witness (`LeafNodes n =
2 ^ n`) and prove the leaf-doubling law.
-/

namespace AgdaMirror.TreeCCR

/-- The tree-CCR refinement data. -/
structure TreeCCRAxioms where
  R : Type
  TreeDepth : Nat → Type
  LeafNodes : Nat → Nat
  InducedH : Nat → Type
  RefinementMap : ∀ n, InducedH n → InducedH (n + 1)

/-- A genuine binary-tree witness: `LeafNodes n = 2 ^ n`, with trivial spaces and
refinement map. -/
def binaryTreeCCR : TreeCCRAxioms where
  R := Unit
  TreeDepth := fun _ => Unit
  LeafNodes := fun n => 2 ^ n
  InducedH := fun _ => Unit
  RefinementMap := fun _ _ => ()

/-- Leaf-doubling law for the binary-tree witness. -/
theorem binaryTreeCCR_leaf_double (n : Nat) :
    binaryTreeCCR.LeafNodes (n + 1) = 2 * binaryTreeCCR.LeafNodes n := by
  simp [binaryTreeCCR, pow_succ, Nat.mul_comm]

end AgdaMirror.TreeCCR
