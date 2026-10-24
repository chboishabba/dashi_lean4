import Integration.Address
import Mathlib.Tactic

/-!
# Finite-stage noncompact-surface exhaustion invariants, Lean native

CLASSICAL SOURCE: Ian Richards, "On the Classification of Noncompact
Surfaces" (1963), for the eventual global end/genus classification.

REUSE:
  Integration.Address.Addr n Bool for the EXISTING exact finite
  prefix carrier (rather than a second finite Cantor word type).
  DASHI Agda #1254 already records the same geometric pants/handle
  attachment schedules and independent integer checks.

At each finite stage we compute the numerical invariants of a
compact connected orientable surface with boundary:
  chi = 2 - 2g - b.
A genus-zero pair of pants attached at each outgoing boundary gives
b(n)=2^n, g(n)=0. A genus-one two-boundary collar at the lone end
gives g(n)=n,b(n)=1. Attaching one such collar at EACH of two ends
gives g(n)=2n,b(n)=2.

These are EXACT finite CW/Euler bookkeeping theorems. They DO NOT
construct actual glued topological surfaces, prove their limit is
a Hausdorff 2-manifold, identify their end spaces, or apply Richards'
classification. No mathematical claim is promoted across those gaps.
-/

namespace Synthesis.ExoticTopology

/-- Use the repository-owned prefix-address carrier rather than reimplementing it. -/
abbrev CantorBoundaryCodes (n : ℕ) :=
  Integration.Address.Addr n Bool

/-- The finite Cantor-tree frontier has precisely 2^n addresses. -/
theorem cantorBoundaryCodeCard (n : ℕ) :
    Fintype.card (CantorBoundaryCodes n) = 2 ^ n := by
  simp [CantorBoundaryCodes, Integration.Address.Addr,
    Fintype.card_fun]

/-- Exact orientable compact-surface-with-boundary Euler accounting. -/
def eulerForGenusBoundaries (genus boundaryCount : ℕ) : ℤ :=
  2 - 2 * (genus : ℤ) - (boundaryCount : ℤ)

/-- Formal stage data, distinct from a geometric 2-manifold. -/
structure FiniteSurfaceStage where
  genus : ℕ
  boundaryCount : ℕ

def cantorTreeStage (n : ℕ) : FiniteSurfaceStage :=
  ⟨0, 2 ^ n⟩

def lochNessStage (n : ℕ) : FiniteSurfaceStage :=
  ⟨n, 1⟩

def jacobsLadderStage (n : ℕ) : FiniteSurfaceStage :=
  ⟨2 * n, 2⟩

/-- The pair-of-pants frontier doubles at the next level. -/
theorem cantorTreeBoundarySuccessor (n : ℕ) :
    (cantorTreeStage (n+1)).boundaryCount =
      2 * (cantorTreeStage n).boundaryCount := by
  simp [cantorTreeStage, pow_succ]
  omega

/-- The Loch Ness genus increases once per outgoing one-ended collar. -/
theorem lochNessGenusSuccessor (n : ℕ) :
    (lochNessStage (n+1)).genus =
      (lochNessStage n).genus + 1 := by
  rfl

/-- Both Jacob's ladder ends acquire one handle at each stage. -/
theorem jacobsLadderGenusSuccessor (n : ℕ) :
    (jacobsLadderStage (n+1)).genus =
      (jacobsLadderStage n).genus + 2 := by
  simp [jacobsLadderStage]
  omega

theorem cantorTreeStageEuler (n : ℕ) :
    eulerForGenusBoundaries (cantorTreeStage n).genus
      (cantorTreeStage n).boundaryCount =
      2 - (2 ^ n : ℕ) := by
  simp [eulerForGenusBoundaries, cantorTreeStage]

theorem lochNessStageEuler (n : ℕ) :
    eulerForGenusBoundaries (lochNessStage n).genus
      (lochNessStage n).boundaryCount = 1 - 2 * (n : ℤ) := by
  simp [eulerForGenusBoundaries, lochNessStage]

theorem jacobsLadderStageEuler (n : ℕ) :
    eulerForGenusBoundaries (jacobsLadderStage n).genus
      (jacobsLadderStage n).boundaryCount = -4 * (n : ℤ) := by
  simp [eulerForGenusBoundaries, jacobsLadderStage, Nat.cast_mul]
  ring

/-- Rank of a 1-dimensional CW spine of a compact connected oriented
    surface with at least one boundary component.
    This is only the numeric rank; no topological retraction is made. -/
def spineRank (genus boundaryCount : ℕ) : ℕ :=
  2 * genus + boundaryCount - 1

theorem cantorTreeSpineRank (n : ℕ) :
    spineRank (cantorTreeStage n).genus
      (cantorTreeStage n).boundaryCount = 2 ^ n - 1 := by
  rfl

theorem lochNessSpineRank (n : ℕ) :
    spineRank (lochNessStage n).genus
      (lochNessStage n).boundaryCount = 2 * n := by
  simp [spineRank, lochNessStage]

theorem jacobsLadderSpineRank (n : ℕ) :
    spineRank (jacobsLadderStage n).genus
      (jacobsLadderStage n).boundaryCount = 4 * n + 1 := by
  simp [spineRank, jacobsLadderStage]
  omega

end Synthesis.ExoticTopology
