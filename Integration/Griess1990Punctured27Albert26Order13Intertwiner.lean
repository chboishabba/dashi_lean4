import Integration.Griess1990AlbertOrder13Traceless26
import Integration.Griess1990Projective13PuncturedCube27SameGrade
import Mathlib

/-!
# Constructive Q[C13]-same-representation weld: punctured grade26 ↔ Albert traceless26

This DOES NOT equate a finite 26-point SET with a 26-dimensional Q
vector space. The exact functor is the FREE RATIONAL VECTOR SPACE
on the 26 original nonzero F3^3 grades.

Original source: R. L. Griess Jr., *A Moufang loop, the exceptional
Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131
(1990), 281-293, DOI 10.1016/0021-8693(90)90176-O. Original
nonassociative phase g/Albert algebra and graded automorphisms are his
mathematics; explicit chart and finite basis certificate are DASHI
subsequent computation. Rational cyclic representation decomposition
is classical Maschke/cyclotomic theory, not a DASHI discovery.

Reuses:
- SAME literal Griess #52 Grade F3^3 and three source-corrected
  shears (not a new C13 generator).
- SAME literal punctured 26 grades / projective 13×orientation chart.
- SAME literal rational Cayley-Dickson Albert tracezero26 operator B,
  as independently audited in the preexisting order13 certificate.

The grade automorphism on punctured grades has two 13-orbits with
selected seeds x=(0,0,1), -x=(0,0,2).
The canonical 26-point permutation P consists of two 13-cycles.

Define the rational 26×26 matrix X with columns
  e0,B e0,...,B^12 e0, e1,B e1,...,B^12 e1.
Independent exact SymPy on the ACTUAL previous rational B matrix:
  B X = X P; det(X) = -729/4096 != 0.
Consequently the FREE Q[C13] module on nonzero source grades and the
ACTUAL Albert tracezero26 are LINEARLY equivariantly isomorphic.

26=(1+12)+(1+12) as rational C13 representations. In particular
the two 13D cycle modules are NOT 13D irreducibles over Q.

STOP RULE: this isomorphism is only C13-linear. The source grade
order13 automorphism FAILS original nonwrapping P3^3 adjacency;
no graph-operator, octonion Jordan product, full F4 or Monster VOA
intertwiner, RH or physical string dimension is constructed here.

SOURCE WRITTEN; no Lean/Lake kernel was available in this runtime.
-/

namespace Integration.Griess1990Punctured27Albert26Order13Intertwiner

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Projective13PuncturedCube27SameGrade
open Integration.Griess1990AlbertOrder13Traceless26

/-- The selected literal two 13-point orbits on punctured F3^3. -/
def sourceOrbitPoint (i : Fin 26) : Grade :=
  if i.val < 13 then
    (gradeOrder13^[i.val]) ![0,0,1]
  else
    (gradeOrder13^[i.val-13]) ![0,0,2]

def cycleSuccessor (i : Fin 26) : Fin 26 :=
  Fin.ofNat 26
    (if i.val < 13 then (i.val+1)%13
     else 13+(i.val-13+1)%13)

theorem both_source_orbits_are_nonzero :
    ∀ i : Fin 26, sourceOrbitPoint i ≠ 0 := by native_decide

theorem source_orbit_26_is_injective :
    Function.Injective sourceOrbitPoint := by native_decide

theorem source_orbit_26_covers_all_nonzero :
    ∀ x : Grade, x ≠ 0 → ∃ i : Fin 26, sourceOrbitPoint i = x := by
  native_decide

theorem original_grade_actor_is_two_cyclic_permutations :
    ∀ i : Fin 26,
      gradeOrder13 (sourceOrbitPoint i) =
        sourceOrbitPoint (cycleSuccessor i) := by native_decide

/-- The *free Q module* on the original 26 nonzero point labels,
not the original set itself. -/
abbrev LinearizedPunctured26 := Fin 26 → ℚ

/-- Permutes TWO original grade orbits, each of order thirteen. -/
def gradeCyclePermutation : Matrix (Fin 26) (Fin 26) ℚ :=
  fun row col =>
    if row = cycleSuccessor col then (1 : ℚ) else 0

/-- Cyclic basis vectors in the ACTUAL native Albert tracezero26.
The chosen first two native coordinate vectors are e0 and e1. -/
def albertCyclicBasis : Matrix (Fin 26) (Fin 26) ℚ :=
  fun row col =>
    if col.val < 13 then
      (nativeTracelessOrder13 ^ col.val) row 0
    else
      (nativeTracelessOrder13 ^ (col.val-13)) row 1

/-- THE positive actual same-operator certificate: B X = X P,
so the 26 spatial point labels AFTER RATIONAL LINEARIZATION carry
the same C13 representation as the genuine native Albert J0. -/
theorem albert_cyclic_basis_intertwines_grade_two13_cycles :
    nativeTracelessOrder13 * albertCyclicBasis =
      albertCyclicBasis * gradeCyclePermutation := by native_decide

/-- An explicit nonzero rational determinant, independent of an
invented 26=2×13 abstract cardinality bijection. -/
theorem albert_cyclic_basis_det :
    Matrix.det albertCyclicBasis = (-729/4096 : ℚ) := by
  native_decide

theorem albert_cyclic_basis_is_invertible :
    IsUnit (Matrix.det albertCyclicBasis) := by
  rw [albert_cyclic_basis_det]
  norm_num

/-- The Griess automorphism does NOT descend to an automorphism
of the native original P3^3 adjacency, even after this positive
linear representation weld. Original/linearized spatial semantics
and Jordan multiplication are different consumer structures. -/
theorem same_c13_action_not_a_path_graph_symmetry :
    ¬ (∀ x y : Grade,
      originalCubeAdjacent x y →
      originalCubeAdjacent (gradeOrder13 x) (gradeOrder13 y)) :=
  source_albert_order13_not_native_path_symmetry

end Integration.Griess1990Punctured27Albert26Order13Intertwiner
