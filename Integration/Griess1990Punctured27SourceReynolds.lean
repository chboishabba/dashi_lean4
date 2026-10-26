import Integration.Griess1990PuncturedCubeAntipodalSpectral
import Integration.Griess1990Punctured27Albert26Order13Intertwiner
import Integration.Griess1990Moufang81ElementaryLift
import Mathlib

/-!
# SOURCE-ACTION REYNOLDS MAX-CUT: native P3³ minus 0 versus Griess C13 / SL3(3)

Original owners and genealogy:
* R. L. Griess Jr. (1990), J. Algebra 131:281-293,
  DOI 10.1016/0021-8693(90)90176-O: ACTUAL F3³ graded Albert
  product, 81-Moufang and SL3(3) normalizer. This is HIS mathematics.
* Classical finite-group Reynolds orthogonal projection (not DASHI's
  theorem): average a linear action on End_Q(V), yielding its nearest
  fixed operator for the invariant Frobenius inner product.
* Gross (1974), Gross--Tucker (1977): original voltage-cover theory;
  signed graph vocabulary, not evidence of physical gauge flux.
* Agda #1249 owns the original native nonwrapping P3³ graph and antipode;
  Agda #1261 the original punctured27/crystal 13 axes; Lean #52
  earlier source order13, original 26 labels and native Albert J0 actor.

The ORIGINAL 26 point labels are a finite set, not the native Q-vector
space J0. We linearise the labels before comparing C13 representations.

EXACT local independent PYTHON:
  A original native 26-site adjacency (48 unordered, 96 ordered edges).
  Z=∑_(k=0..12) P^(-k) A P^k, A_C13=Z/13.
  Frobenius²(A)=96, Frobenius²(A_C13)=240/13,
  Frobenius²(A-A_C13)=1008/13; retained=5/26, lost=21/26.
  Pair-orbit 25 weights: {0:3,1:6,2:6,3:10}.
  Antipode EVEN sector retains 14/39 of its norm², ODD only 1/39.

For the full SOURCE SL3(3) label group, six actual elementary
shears classify all nonzero-grade ORDERED pairs as:
 equal 26; opposite 26; independent 624. ALL 96 native directed
 edges are in the independent class. Thus its unique Frobenius
 projection A_SL=(2/13)(J26-I26-Tantipode).
 Its unsigned 13-block is (4/13)(J13-I13) and its signed
 13-block is identically ZERO. Norm² retained=192/13;
 loss=1056/13; proportions 2/13 and 11/13.
 No full-group intertwiner with actual native Albert J0 follows.

These small source-specific rational arithmetic statements are formal
PROOF TARGETS, not Lean-kernel receipts. The Lean toolchain was not
available here. No Monster 3B/VOA, exceptional-root action, real
diamond system or physical graph-gauge connection is inferred.
-/

namespace Integration.Griess1990Punctured27SourceReynolds

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift
open Integration.Griess1990Projective13PuncturedCube27SameGrade
open Integration.Griess1990PuncturedCubeAntipodalSpectral
open Integration.Griess1990Punctured27Albert26Order13Intertwiner

/-- ACTUAL original P3³ graph, reordered by the two already existing
source-grade thirteen cycles; no new invented 26-point carrier. -/
def originalA : Matrix (Fin 26) (Fin 26) ℤ :=
  fun i j => adjacencyInt (sourceOrbitPoint i) (sourceOrbitPoint j)

/-- Unnormalised C13 Reynolds matrix with exact integer entries. -/
def cyclicNumerator : Matrix (Fin 26) (Fin 26) ℤ :=
  fun i j => ∑ k : Fin 13,
    originalA ((cycleSuccessor^[k.val]) i)
      ((cycleSuccessor^[k.val]) j)

def cyclicAverage : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j => (cyclicNumerator i j : ℚ) / 13

def squareSum (M : Matrix (Fin 26) (Fin 26) ℤ) : ℤ :=
  ∑ i : Fin 26, ∑ j : Fin 26, M i j * M i j

def crossSum (M N : Matrix (Fin 26) (Fin 26) ℤ) : ℤ :=
  ∑ i : Fin 26, ∑ j : Fin 26, M i j * N i j

theorem source_cycle_preserves_cyclic_numerator :
    ∀ i j : Fin 26,
      cyclicNumerator (cycleSuccessor i) (cycleSuccessor j) =
        cyclicNumerator i j := by native_decide

theorem original_A_squared_frobenius :
    squareSum originalA = 96 := by native_decide

theorem cyclic_numerator_squared_frobenius :
    squareSum cyclicNumerator = 3120 := by native_decide

theorem cyclic_reynolds_A_numerator_inner :
    crossSum originalA cyclicNumerator = 240 := by native_decide

theorem cyclic_reynolds_orthogonal_projection_identity :
    13 * crossSum originalA cyclicNumerator =
      squareSum cyclicNumerator := by
  rw [cyclic_reynolds_A_numerator_inner,
      cyclic_numerator_squared_frobenius]
  norm_num

theorem cyclic_reynolds_residual_exact :
    squareSum
      (fun i j => 13 * originalA i j - cyclicNumerator i j)
      = 13104 := by native_decide

/-- The actual Griess SL3 grade-action orbit classes. This is
a source-defined invariant weighted ADJACENCY, NOT the original
unweighted native graph's adjacency. -/
def sourceFullWeight (x y : Grade) : ℚ :=
  if x = 0 ∨ y = 0 ∨ x = y ∨ x = -y
  then 0 else 2 / 13

def fullSourceAverage : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j => sourceFullWeight (sourceOrbitPoint i) (sourceOrbitPoint j)

theorem full_source_weight_six_shear_invariant :
    ∀ s : Shear, ∀ x y : Grade,
      sourceFullWeight (gradeShear s x) (gradeShear s y) =
        sourceFullWeight x y := by native_decide

/-- Every source spatial directed edge is an INDEPENDENT grade pair. -/
theorem original_edges_are_source_independent :
    ∀ i j : Fin 26, originalA i j = 1 →
      fullSourceAverage i j = (2/13 : ℚ) := by native_decide

def squaredFrobeniusQ (M : Matrix (Fin 26) (Fin 26) ℚ) : ℚ :=
  ∑ i : Fin 26, ∑ j : Fin 26, M i j * M i j

theorem full_source_average_squared_norm :
    squaredFrobeniusQ fullSourceAverage = (192/13 : ℚ) := by
  native_decide

theorem full_source_average_residual_squared_norm :
    squaredFrobeniusQ
      (fun i j => (originalA i j : ℚ) - fullSourceAverage i j)
        = (1056/13 : ℚ) := by native_decide

/-- The entire ANTISYMMETRIC/signed 13D spatial sector is killed by
full source-grade SL3(3) Reynolds averaging. This is strictly stronger
than observing that one chosen source order13 shear is not an
original spatial graph automorphism. -/
theorem full_source_average_odd_parity_is_zero :
    ∀ i j : Fin 13,
      sourceFullWeight (projectiveRepresentative i)
        (projectiveRepresentative j) -
      sourceFullWeight (projectiveRepresentative i)
        (-projectiveRepresentative j) = 0 := by native_decide

theorem full_source_average_even_sector :
    ∀ i j : Fin 13,
      sourceFullWeight (projectiveRepresentative i)
        (projectiveRepresentative j) +
      sourceFullWeight (projectiveRepresentative i)
        (-projectiveRepresentative j) =
        (if i = j then 0 else (4/13 : ℚ)) := by native_decide

/-! ## P0 full-source commutant: exactly 3 orbital indicator kernels

EXACT local BFS over the actual six SL3 source generators finds
THREE ordered-pair grade orbits (same, negative, independent).
Thus the entire full-label-group commutant is
span_Q {identity, antipode, all-ones}, with spectral projectors
of ranks 1+12+13. This is classical permutation-module theory,
NOT an exceptional Jordan product/Monster/physical result.

Every fully SL3 grade-invariant operator is SCALAR on the odd13
anti-antipodal sector. The actual spatial signed 13-axis operator is
not scalar, so cannot commute with all six original grade shears.
-/

/-- Same original grade orbit chart, 26 selected nonzero points. -/
def sourceAntipodalMatrix : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j => if sourceOrbitPoint i = -sourceOrbitPoint j then 1 else 0

def sourceOneMatrix : Matrix (Fin 26) (Fin 26) ℚ :=
  fun _ _ => 1

/-- The three mutually orthogonal rational PROJECTORS onto 1,12,13
of the original 26-point grade permutation representation of
FULL SL3(3), not the actual Albert J0 26 representation. -/
def sourceTrivialProjector : Matrix (Fin 26) (Fin 26) ℚ :=
  fun _ _ => 1/26

def sourceEvenNonconstantProjector : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j =>
    (if i = j then (1/2 : ℚ) else 0) +
    (if sourceOrbitPoint i = -sourceOrbitPoint j then (1/2 : ℚ) else 0) -
    1/26

def sourceOddProjector : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j =>
    (if i = j then (1/2 : ℚ) else 0) -
    (if sourceOrbitPoint i = -sourceOrbitPoint j then (1/2 : ℚ) else 0)

theorem source_full_triv_projector_rank_one :
    Matrix.trace sourceTrivialProjector = (1 : ℚ) := by native_decide

theorem source_full_even_projector_rank_twelve :
    Matrix.trace sourceEvenNonconstantProjector = (12 : ℚ) := by native_decide

theorem source_full_odd_projector_rank_thirteen :
    Matrix.trace sourceOddProjector = (13 : ℚ) := by native_decide

theorem source_full_projectors_sum_identity :
    sourceTrivialProjector + sourceEvenNonconstantProjector +
      sourceOddProjector = 1 := by native_decide

theorem source_full_projectors_are_idempotent :
    sourceTrivialProjector * sourceTrivialProjector = sourceTrivialProjector ∧
    sourceEvenNonconstantProjector * sourceEvenNonconstantProjector =
      sourceEvenNonconstantProjector ∧
    sourceOddProjector * sourceOddProjector = sourceOddProjector := by
  native_decide

theorem source_full_projectors_are_pairwise_orthogonal :
    sourceTrivialProjector * sourceEvenNonconstantProjector = 0 ∧
    sourceTrivialProjector * sourceOddProjector = 0 ∧
    sourceEvenNonconstantProjector * sourceOddProjector = 0 := by
  native_decide

/-- All full-source-invariant rational kernels are CONSTANT on the
three ordered-pair orbitals (equal/opposite/independent). The
separate universality of this classification is checked by exact
finite orbit BFS over six native generators in the Python receipt. -/
def sourceInvariantKernel (equalCoeff oppositeCoeff independentCoeff : ℚ)
    (x y : Grade) : ℚ :=
  if x = y then equalCoeff
  else if x = -y then oppositeCoeff
  else independentCoeff

/-- Universal SIGNED sector is scalar for any orbital constants:
off-diagonal elements cancel, diagonal becomes equal-opposite. -/
theorem source_full_invariant_odd_sector_is_scalar
    (equalCoeff oppositeCoeff independentCoeff : ℚ) :
    ∀ i j : Fin 13,
      sourceInvariantKernel equalCoeff oppositeCoeff independentCoeff
        (projectiveRepresentative i) (projectiveRepresentative j) -
      sourceInvariantKernel equalCoeff oppositeCoeff independentCoeff
        (projectiveRepresentative i) (-projectiveRepresentative j) =
        (if i = j then equalCoeff-oppositeCoeff else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceInvariantKernel, projectiveRepresentative]


end Integration.Griess1990Punctured27SourceReynolds
