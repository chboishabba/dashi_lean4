import Integration.Griess1990Projective13PuncturedCube27SameGrade
import Mathlib

/-!
# The source-owned punctured P3³ adjacency splits 26 = 13⁺ ⊕ 13⁻

The 26 NONZERO spatial cube SITES are exactly the same underlying F3³
grade labels used by the genuine 1990 Griess graded Albert programme.
Unlike the rational Albert tracezero26 VECTOR module, they carry
the ORIGINAL nonwrapping path graph P3³ with its actual antipode.

Original mathematical donors: finite Cayley/voltage graph covering
theory (Gross 1974; Gross--Tucker 1977), classical spectral linear
algebra, and R. L. Griess Jr., J. Algebra 131 (1990) 281--293 for
the separate graded exceptional algebra. Implementation donors:
Agda #1249 original Cube.HypervoxelAdjacent and antipode; Agda #1261
native crystal/13-axis/nine-sheet; Lean #52 original F3³ Grade and
real source order13 actor. Do not reimplement any of these carriers.

For representative r_a in each of 13 projective grades let
 e_a^+ = e_(r_a) + e_(-r_a), e_a^- = e_(r_a) - e_(-r_a).
A26 commutes with native antipode, and is conjugate under a rational
26x26 H (H^T H = 2I) to diag(Aplus,Aminus). Aplus and Aminus are
respectively the unsigned and signed adjacency of the ACTUAL
13-vertex spatial quotient; they are not the PG(2,3) incidence
relation with 52 flags, nor the native Albert Jordan product.

The 13-axis graph is bipartite by support parity 7+6.
On the source-selected six support-two projective axes:
  Bplusᵀ Bplus = 2 I₆ + 2 J₆;
  (Bminusᵀ Bminus)² = 8 (Bminusᵀ Bminus), trace = 24.
Independent exact SymPy PASS implies characteristic polynomials
  χplus = t (t²-14)(t²-2)^5,
  χminus = t^7(t²-8)^3,
  χ26 = t^8(t²-14)(t²-8)^3(t²-2)^5.
These small Gram facts are the PARETO proof cuts before large
matrix characteristic-polynomial kernel work.

Selected Griess order13 source actor sends ALL 48 original punctured
edges to nonedges, with 26D adjacency conjugation Frobenius² = 192;
on the 13 quotient it preserves exactly 5/24 edges, Frobenius²=76.
Therefore the existing rational Q[C13] equivalence with Albert J0
does NOT intertwine actual spatial adjacency. No physical mechanism
or Monster/VOA same-object action is inferred.

SOURCE WRITTEN: the Lean kernel is NOT run here. Small finite
6x6 exact statements below are intentionally cheap proof targets.
-/

namespace Integration.Griess1990PuncturedCubeAntipodalSpectral

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Projective13PuncturedCube27SameGrade

/-- The actual source graph, evaluated on the existing F3³ grade. -/
def adjacencyInt (x y : Grade) : ℤ :=
  if originalCubeAdjacent x y then 1 else 0

/-- ACTUAL 13 point representatives, with antipodal sign retained. -/
def evenAdjacency (i j : Fin 13) : ℤ :=
  adjacencyInt (projectiveRepresentative i) (projectiveRepresentative j) +
  adjacencyInt (projectiveRepresentative i) (-projectiveRepresentative j)

def oddAdjacency (i j : Fin 13) : ℤ :=
  adjacencyInt (projectiveRepresentative i) (projectiveRepresentative j) -
  adjacencyInt (projectiveRepresentative i) (-projectiveRepresentative j)

def evenMatrix : Matrix (Fin 13) (Fin 13) ℤ := fun i j => evenAdjacency i j
def oddMatrix : Matrix (Fin 13) (Fin 13) ℤ := fun i j => oddAdjacency i j

/-- PRE-EXISTING support count on original thirteen graded directions. -/
def oddSupportAxis (i : Fin 7) : Fin 13 :=
  ![0, 4, 5, 7, 8, 9, 12] i

def faceAxis (i : Fin 6) : Fin 13 :=
  ![1, 2, 3, 6, 10, 11] i

/-- Source-specific 7x6 bipartite incidence blocks. -/
def evenIncidence : Matrix (Fin 7) (Fin 6) ℤ :=
  fun i j => evenAdjacency (oddSupportAxis i) (faceAxis j)

def oddIncidence : Matrix (Fin 7) (Fin 6) ℤ :=
  fun i j => oddAdjacency (oddSupportAxis i) (faceAxis j)

def evenGram : Matrix (Fin 6) (Fin 6) ℤ :=
  evenIncidence.transpose * evenIncidence

def oddGram : Matrix (Fin 6) (Fin 6) ℤ :=
  oddIncidence.transpose * oddIncidence

theorem antipode_preserves_native_path :
    ∀ x y : Grade,
      originalCubeAdjacent x y ↔ originalCubeAdjacent (-x) (-y) := by
  native_decide

theorem spatial_even_signed_symmetric :
    evenMatrix.transpose = evenMatrix ∧
      oddMatrix.transpose = oddMatrix := by
  native_decide

/-- Both parity adjacency blocks are genuinely bipartite 7+6. -/
theorem parity_bipartite :
    (∀ i j : Fin 7,
      evenAdjacency (oddSupportAxis i) (oddSupportAxis j) = 0 ∧
      oddAdjacency (oddSupportAxis i) (oddSupportAxis j) = 0) ∧
    (∀ i j : Fin 6,
      evenAdjacency (faceAxis i) (faceAxis j) = 0 ∧
      oddAdjacency (faceAxis i) (faceAxis j) = 0) := by
  native_decide

/-- THE cheap source-specific exact spectral certificates. -/
theorem actual_even_gram_is_twoI_plus_twoJ :
    evenGram =
      (2 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) +
      (2 : ℤ) • (Matrix.of fun _ _ : Fin 6 => (1 : ℤ)) := by
  native_decide

theorem actual_odd_gram_quadratic :
    oddGram * oddGram = (8 : ℤ) • oddGram := by
  native_decide

theorem actual_odd_gram_trace :
    Matrix.trace oddGram = (24 : ℤ) := by
  native_decide

/-- The previous true Griess order13 action is valid on the rational
Albert Jordan algebra, but it breaks ALL original native path edges.
Preserve this firewall whenever transporting the Q[C13] module. -/
theorem native_graph_not_griess_order13_equivariant :
    ¬ (∀ x y : Grade,
      originalCubeAdjacent x y →
      originalCubeAdjacent (gradeOrder13 x) (gradeOrder13 y)) :=
  source_albert_order13_not_native_path_symmetry

end Integration.Griess1990PuncturedCubeAntipodalSpectral
