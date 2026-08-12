import Mathlib

/-!
# Lean mirror of `TenfoldBridges.agda` (genuine, fully proved)

Faithful transcription of `TenfoldBridges.agda`: the topological class
`topoClass n = n % 10`, a `Bridge` between two nodes of *different* class,
the symmetry operation swapping the endpoints, and the theorem that the swap
exposes the second node as the new first node.
-/

namespace AgdaMirror.TenfoldBridges

/-- Topological class. -/
def topoClass (n : Nat) : Nat := n % 10

/-- A bridge between two nodes of different topological class. -/
structure Bridge where
  nodeA : Nat
  nodeB : Nat
  different : topoClass nodeA ≠ topoClass nodeB

/-- Symmetry: swap the endpoints (the difference proof is reused symmetrically). -/
def bridgeSym (b : Bridge) : Bridge where
  nodeA := b.nodeB
  nodeB := b.nodeA
  different := fun eq => b.different eq.symm

/-- Example bridge `232 ↔ 323` (classes `2 ≠ 3`). -/
def bridge_232_323 : Bridge where
  nodeA := 232
  nodeB := 323
  different := by decide

/-- Symmetry preserves bridges: the new first node is the old second node. -/
theorem bridge_symmetry (b : Bridge) : (bridgeSym b).nodeA = b.nodeB := rfl

end AgdaMirror.TenfoldBridges
