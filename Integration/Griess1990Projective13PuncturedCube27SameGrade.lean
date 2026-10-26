import Integration.Griess1990Moufang81Explicit13Cycle
import Integration.Griess1990Moufang81ElementaryLift
import Mathlib

/-!
# SAME F3^3 grade carrier, two DIFFERENT structures: PG(2,3) and punctured P3^3

Original grade/exceptional Jordan source:
R. L. Griess Jr., J. Algebra 131 (1990), 281--293,
DOI 10.1016/0021-8693(90)90176-O.
The projective plane PG(2,3), signed coordinate permutations W(B3)
and graph theory are CLASSICAL finite geometry, not new DASHI theorems.

This module consumes the EXACT Lean #52 Griess `Grade = Fin 3 → ZMod3`
and its ACTUAL SOURCE-corrected order-13 Moufang lifts. It is motivated
by Agda #1249's original hypervoxel path graph and its native antipode,
Agda #1261's punctured 27 = 8+9+9 and 13=3+6+4 crystal audit, and the
existing Ibrahim/OEIS 1+26 and 2×13 arithmetic owners.

A nonzero F3³ grade IS precisely a centered ternary cube point. Divide
by the involution x↦−x and *retain* its one-bit orientation residual.
This gives an explicitly invertible 26↔(13×2) chart on the SAME 26 points.
It is NOT the 26-dimensional Q-vector space of traceless rational Albert
or an isomorphism of path-graph adjacency with Jordan product.

The source order-13 SL3(3)/Griess automorphism is already mathematically
valid on the Albert algebra, yet provably does NOT preserve this original
nonwrapping P3³ path adjacency. Do not promote the former to the latter.

This source is NOT Lean kernel-checked. All finite theorem statements
have corresponding exact source-equivalent Python receipts.
-/

namespace Integration.Griess1990Projective13PuncturedCube27SameGrade

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift
open Integration.Griess1990Moufang81Explicit13Cycle

abbrev NativePuncturedGrade := {x : Grade // x ≠ 0}

/-- Projective line reps: nine with x0=1, three with x0=0,x1=1,
one with x0=x1=0,x2=1. The same thirteen antipodal lines, NOT an
independently invented collection of numerical labels. -/
def projectiveRepresentative (i : Fin 13) : Grade :=
  if i.val < 9 then
    ![1, (i.val/3 : ZMod 3), (i.val%3 : ZMod 3)]
  else if i.val < 12 then
    ![0, 1, (i.val-9 : ZMod 3)]
  else ![0,0,1]

theorem projective_representatives_nonzero :
    ∀ i : Fin 13, projectiveRepresentative i ≠ 0 := by native_decide

/-- First nonzero coordinate must be +1. If it is -1=2, flip
all three coordinates. Do not confuse with ternary INDEX 111₃. -/
def firstNonzeroNegative (x : Grade) : Bool :=
  if x 0 != 0 then x 0 == 2
  else if x 1 != 0 then x 1 == 2
  else x 2 == 2

def positiveFirst (x : Grade) : Grade :=
  if firstNonzeroNegative x then -x else x

def projectiveIndex (x : Grade) : Fin 13 :=
  let y := positiveFirst x
  if y 0 == 1 then
    Fin.ofNat 13 (3*(y 1).val + (y 2).val)
  else if y 1 == 1 then
    Fin.ofNat 13 (9 + (y 2).val)
  else 12

/-- Explicit two-way codec with the orientation bit retained. -/
def encodeOriginal26 (x : NativePuncturedGrade) : Fin 13 × Bool :=
  (projectiveIndex x.1, firstNonzeroNegative x.1)

def decodeOriginal26 (a : Fin 13 × Bool) : NativePuncturedGrade :=
  ⟨if a.2 then -projectiveRepresentative a.1
    else projectiveRepresentative a.1, by
    have hp := projective_representatives_nonzero a.1
    split
    · intro hzero
      exact hp (neg_eq_zero.mp hzero)
    · exact hp⟩

theorem original26_decode_encode :
    ∀ x : NativePuncturedGrade,
      decodeOriginal26 (encodeOriginal26 x) = x := by native_decide

theorem original26_encode_decode :
    ∀ a : Fin 13 × Bool,
      encodeOriginal26 (decodeOriginal26 a) = a := by native_decide

def original26EquivProjective13Orientation :
    NativePuncturedGrade ≃ Fin 13 × Bool where
  toFun := encodeOriginal26
  invFun := decodeOriginal26
  left_inv := original26_decode_encode
  right_inv := original26_encode_decode

theorem native_grade_27_card : Fintype.card Grade = 27 := by native_decide
theorem punctured_26_card : Fintype.card NativePuncturedGrade = 26 := by native_decide
theorem projective_axes_13_card : Fintype.card (Fin 13) = 13 := by decide

/-- 3+6+4 is the *cubic support* partition, not the 9+3+1
projective representative chart and not an F4/E6 dimension argument. -/
def numberNonzero (x : Grade) : Nat :=
  (if x 0 == 0 then 0 else 1) +
    (if x 1 == 0 then 0 else 1) +
      (if x 2 == 0 then 0 else 1)

theorem support_one_three :
    (Finset.univ.filter fun i : Fin 13 =>
      numberNonzero (projectiveRepresentative i) = 1).card = 3 := by native_decide
theorem support_two_six :
    (Finset.univ.filter fun i : Fin 13 =>
      numberNonzero (projectiveRepresentative i) = 2).card = 6 := by native_decide
theorem support_three_four :
    (Finset.univ.filter fun i : Fin 13 =>
      numberNonzero (projectiveRepresentative i) = 3).card = 4 := by native_decide

/-- Original NON-WRAPPING path P3 adjacency in centered ZMod3
coordinates: 0 is adjacent to ±1, but +1 is NOT adjacent to -1. -/
def actualPathStep (x y : ZMod 3) : Prop :=
  (x = 0 ∧ y ≠ 0) ∨ (x ≠ 0 ∧ y = 0)

def originalCubeAdjacent (x y : Grade) : Prop :=
  (actualPathStep (x 0) (y 0) ∧ x 1 = y 1 ∧ x 2 = y 2) ∨
  (x 0 = y 0 ∧ actualPathStep (x 1) (y 1) ∧ x 2 = y 2) ∨
  (x 0 = y 0 ∧ x 1 = y 1 ∧ actualPathStep (x 2) (y 2))

/-- The old 27 original cube has 54 unoriented edges, puncturing
its origin deletes exactly six and leaves 48, rather than 54 or 24. -/
theorem original_full_cube_degree_edge_count :
    (Finset.univ.filter fun xy : Grade × Grade =>
       originalCubeAdjacent xy.1 xy.2).card = 108 := by native_decide

theorem original_punctured_cube_degree_edge_count :
    (Finset.univ.filter fun xy : NativePuncturedGrade × NativePuncturedGrade =>
       originalCubeAdjacent xy.1.1 xy.2.1).card = 96 := by native_decide

/-- A witness from the TRUE previously-owned Griess/M81 actor:
the same-grade order-13 word moves (0,1,0) to (1,1,1),
which is NOT nearest-neighbour to the fixed cube origin. -/
def gradeOrder13 (x : Grade) : Grade :=
  (shortOrder13Lift ⟨x,0⟩).grade

def chosenY : Grade := ![0,1,0]

theorem origin_adjacent_y : originalCubeAdjacent 0 chosenY := by
  native_decide

theorem original_order13_fixes_origin : gradeOrder13 0 = 0 := by
  native_decide

theorem selected_grade_order13_y_to_body_diagonal :
    gradeOrder13 chosenY = ![1,1,1] := by native_decide

theorem original_order13_breaks_actual_path_edge :
    ¬ originalCubeAdjacent (gradeOrder13 0)
      (gradeOrder13 chosenY) := by native_decide

theorem source_albert_order13_not_native_path_symmetry :
    ¬ (∀ x y : Grade, originalCubeAdjacent x y →
      originalCubeAdjacent (gradeOrder13 x) (gradeOrder13 y)) := by
  intro h
  exact original_order13_breaks_actual_path_edge
    (h 0 chosenY origin_adjacent_y)

end Integration.Griess1990Projective13PuncturedCube27SameGrade
