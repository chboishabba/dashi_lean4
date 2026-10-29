/-!
# Weighted directed 3×3 graph inside DASHI 369/trialectics

Downstream Lean mirror of the golden Agda
`DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact`.
This file is source-written but not currently kernel-checked.

The finite graph/matrix correspondence is standard mathematics.
Tivadar Danka's 26 Oct 2026 image is the input illustration, not
authorship of graph theory or this proof. Values are integer tenths.
A 3-vertex carrier does not imply weighted C3 equivariance; a
directed pair does not imply negation, intersectionality, Monster action,
a trialectic attached 2-cell, or a pants gluing theorem.
-/
import Mathlib

namespace AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369

inductive Vertex3 where
  | a | b | c
  deriving DecidableEq, Repr

structure Matrix3 (α : Type) where
  aa : α
  ab : α
  ac : α
  ba : α
  bb : α
  bc : α
  ca : α
  cb : α
  cc : α

abbrev WeightedGraph3 := Vertex3 → Vertex3 → Nat

def matrixToGraph (m : Matrix3 Nat) : WeightedGraph3
  | .a, .a => m.aa
  | .a, .b => m.ab
  | .a, .c => m.ac
  | .b, .a => m.ba
  | .b, .b => m.bb
  | .b, .c => m.bc
  | .c, .a => m.ca
  | .c, .b => m.cb
  | .c, .c => m.cc

def graphToMatrix (g : WeightedGraph3) : Matrix3 Nat :=
  ⟨g .a .a, g .a .b, g .a .c,
   g .b .a, g .b .b, g .b .c,
   g .c .a, g .c .b, g .c .c⟩

theorem matrix_graph_roundtrip (m : Matrix3 Nat) :
    graphToMatrix (matrixToGraph m) = m := by
  cases m
  rfl

theorem graph_matrix_roundtrip (g : WeightedGraph3)
    (s t : Vertex3) :
    matrixToGraph (graphToMatrix g) s t = g s t := by
  cases s <;> cases t <;> rfl

/-- Row is source, column is target. 5 = 0.5 and 22 = 2.2. -/
def fixture : Matrix3 Nat := ⟨5, 10, 0, 2, 0, 22, 18, 20, 0⟩

def present (w : Nat) : Nat := if w = 0 then 0 else 1

def nonzeroArcCount : Nat :=
  present (matrixToGraph fixture .a .a) +
  present (matrixToGraph fixture .a .b) +
  present (matrixToGraph fixture .a .c) +
  present (matrixToGraph fixture .b .a) +
  present (matrixToGraph fixture .b .b) +
  present (matrixToGraph fixture .b .c) +
  present (matrixToGraph fixture .c .a) +
  present (matrixToGraph fixture .c .b) +
  present (matrixToGraph fixture .c .c)

theorem six_arcs_including_loop : nonzeroArcCount = 6 := by decide

theorem reverse_is_not_weight_preserving :
    matrixToGraph fixture .a .b ≠ matrixToGraph fixture .b .a := by
  decide

def rotate : Vertex3 → Vertex3
  | .a => .b
  | .b => .c
  | .c => .a

theorem rotate_cube (v : Vertex3) :
    rotate (rotate (rotate v)) = v := by
  cases v <;> rfl

theorem fixture_not_c3_invariant :
    ¬ ∀ s t : Vertex3,
      matrixToGraph fixture (rotate s) (rotate t) =
        matrixToGraph fixture s t := by
  intro h
  have hLoop := h .a .a
  exact (by decide :
    matrixToGraph fixture (rotate .a) (rotate .a) ≠
      matrixToGraph fixture .a .a) hLoop

inductive AttachedFace where
  | reciprocal | coercive | underdetermined
  deriving DecidableEq, Repr

structure GraphWithFace where
  matrix : Matrix3 Nat
  face : AttachedFace

def observe (s : GraphWithFace) : Matrix3 Nat := s.matrix
def consume (s : GraphWithFace) : AttachedFace := s.face

def leftState : GraphWithFace := ⟨fixture, .reciprocal⟩
def rightState : GraphWithFace := ⟨fixture, .coercive⟩

def FactorsThrough {S V A : Type}
    (o : S → V) (c : S → A) : Prop :=
  ∃ decode : V → A, ∀ s, c s = decode (o s)

/-- Even the *complete* weighted matrix does not recover an attached face. -/
theorem attached_face_does_not_factor_through_matrix :
    ¬ FactorsThrough observe consume := by
  rintro ⟨decode, hd⟩
  have hLeft := hd leftState
  have hRight := hd rightState
  have bad : AttachedFace.reciprocal = AttachedFace.coercive := by
    calc
      AttachedFace.reciprocal = decode fixture := by
        simpa [leftState, observe, consume] using hLeft
      _ = AttachedFace.coercive := by
        simpa [rightState, observe, consume] using hRight.symm
  cases bad

end AgdaMirror.Reasoning.TrialecticWeightedDirectedGraph369
