import Mathlib

/-! Explicit full-rank CM seed in the cubic relative quadratic form.
The rational model is identified with the reported Dickson quadratic space
by Hasse–Minkowski in the controlling roadmap. This module retains the
actual signed skew matrix, determinant and finite reduction. It does not
assert an Agda/Lean formalization of the K3 period theorem or Buskin. -/

namespace DASHI.Hodge.CubicCM

open Matrix

def qdiag {F : Type*} [Field F] (theta : F) : Fin 6 → F :=
  ![theta, theta*(2-theta), -1, -(2-theta), -1, -(2-theta)]

def perturbation {F : Type*} [Field F] : Matrix (Fin 6) (Fin 6) F :=
  !![0,-1,-4,0,4,-6;
     1,0,-5,2,-5,-1;
     4,5,0,3,-6,2;
     0,-2,-3,0,-3,-6;
     -4,5,6,3,0,-5;
     6,1,-2,6,5,0]

def baseSkew {F : Type*} [Field F] (theta : F) :
    Matrix (Fin 6) (Fin 6) F :=
  !![0,-theta*(2-theta),0,0,0,0;
     theta*(2-theta),0,0,0,0,0;
     0,0,0,2*(2-theta),0,0;
     0,0,-2*(2-theta),0,0,0;
     0,0,0,0,0,3*(2-theta);
     0,0,0,0,-3*(2-theta),0]

def skewNumerator {F : Type*} [Field F] (theta : F) :
    Matrix (Fin 6) (Fin 6) F :=
  baseSkew theta + (130001 : F)⁻¹ • perturbation

def seed {F : Type*} [Field F] (theta : F) :
    Matrix (Fin 6) (Fin 6) F :=
  Matrix.diagonal (fun i => (qdiag theta i)⁻¹) * skewNumerator theta

theorem qdiag_det {F : Type*} [Field F] (theta : F) :
    (Matrix.diagonal (qdiag theta)).det = theta^2*(2-theta)^3 := by
  rw [Matrix.det_diagonal]
  simp [qdiag, Fin.prod_univ_succ]
  ring

theorem perturbation_skew {F : Type*} [Field F] :
    (perturbation : Matrix (Fin 6) (Fin 6) F).transpose = -perturbation := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perturbation]

theorem baseSkew_skew {F : Type*} [Field F] (theta : F) :
    (baseSkew theta).transpose = -baseSkew theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [baseSkew]

theorem seed_is_skew {F : Type*} [Field F] (theta : F)
    (ht : theta ≠ 0) (hp : 2-theta ≠ 0) :
    (seed theta).transpose * Matrix.diagonal (qdiag theta) +
      Matrix.diagonal (qdiag theta) * seed theta = 0 := by
  have hq : ∀ i, qdiag theta i ≠ 0 := by
    intro i
    fin_cases i <;> simp [qdiag, ht, hp]
  have hleft : Matrix.diagonal (qdiag theta) *
      Matrix.diagonal (fun i => (qdiag theta i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hq]
  have hright : Matrix.diagonal (fun i => (qdiag theta i)⁻¹) *
      Matrix.diagonal (qdiag theta) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hq]
  have hS : (skewNumerator theta).transpose = -skewNumerator theta := by
    simp [skewNumerator, baseSkew_skew, perturbation_skew]
  unfold seed
  rw [Matrix.transpose_mul, Matrix.transpose_diagonal, hS,
    Matrix.mul_assoc, hright, mul_one, ← Matrix.mul_assoc, hleft, one_mul]
  simp

/-- Exact reduction at theta=7 in the residue field of characteristic 13. -/
def seedMod13 : Matrix (Fin 6) (Fin 6) (ZMod 13) :=
  !![0,3,5,0,8,1;
     11,0,2,7,2,3;
     9,8,0,7,6,11;
     0,10,4,0,2,4;
     4,8,7,10,0,7;
     9,8,10,9,4,0]

theorem seed_reduction_mod13 : seed (7 : ZMod 13) = seedMod13 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seed, seedMod13, qdiag, skewNumerator, baseSkew,
      perturbation, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Uniform perturbation certificate used in the three real embeddings. -/
theorem perturbation_size : (69 / 130001 : ℚ) < 1 / 1000 := by norm_num


/-- Multiplication by theta on (1,theta,theta²), and its actual
rational trace Gram matrix. -/
def thetaMultiplication : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0,0,1;1,0,2;0,1,-1]

def traceGram : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3,-1,5;-1,5,-4;5,-4,13]

def traceDual : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1,-1/7,-3/7;-1/7,2/7,1/7;-3/7,1/7,2/7]

theorem traceGram_dual :
    traceGram * traceDual = 1 ∧ traceDual * traceGram = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [traceGram, traceDual, Matrix.mul_apply, Fin.sum_univ_succ]

theorem thetaMultiplication_cubic :
    thetaMultiplication ^ 3 + thetaMultiplication ^ 2 -
      2 • thetaMultiplication - 1 = 0 := by
  decide

def pf4 {F : Type*} [CommRing F] (M : Matrix (Fin 6) (Fin 6) F)
    (i j k l : Fin 6) : F :=
  M i j * M k l - M i k * M j l + M i l * M j k

def pf6 {F : Type*} [CommRing F] (M : Matrix (Fin 6) (Fin 6) F) : F :=
  M 0 1 * pf4 M 2 3 4 5 -
  M 0 2 * pf4 M 1 3 4 5 +
  M 0 3 * pf4 M 1 2 4 5 -
  M 0 4 * pf4 M 1 2 3 5 +
  M 0 5 * pf4 M 1 2 3 4

/-- Signed Pfaffian of the actual scaled skew numerator at the good
prime, not the determinant of the underlying unsigned carrier. -/
theorem scaledPfaffian_mod13 :
    pf6 ((130001 : ZMod 13) • baseSkew (7 : ZMod 13) + perturbation) = 12 := by
  decide

theorem scaledPfaffian_mod13_ne_zero :
    pf6 ((130001 : ZMod 13) • baseSkew (7 : ZMod 13) + perturbation) ≠ 0 := by
  rw [scaledPfaffian_mod13]
  decide


/-- Division-free Cayley numerator: the first positive relative two-plane
has metric diag(theta,theta*pi), pi=2-theta. This preserves the signed
determinant, even when the normalized entries have large denominators. -/
theorem cayley_plane_numerator (n pi : ℚ) :
    (n^2-pi)^2+pi*(2*n)^2=(n^2+pi)^2 := by ring

theorem cayley_plane_det (n pi : ℚ) (h : n^2+pi ≠ 0) :
    ((n^2-pi)/(n^2+pi))^2 -
      ((-2*n*pi)/(n^2+pi))*((2*n)/(n^2+pi))=1 := by
  field_simp [h] <;> ring

/-- The actual seed off-block entry after the first-plane rotation.
The common factor D*theta is a unit at the selected prime over 29. -/
theorem cayley_seed_entry (n theta D : ℚ)
    (ht : theta ≠ 0) (hp : 2-theta ≠ 0) (hD : D ≠ 0)
    (hn : n^2+(2-theta) ≠ 0) :
    ((n^2-(2-theta))/(n^2+(2-theta)))*(-4/(D*theta)) +
      ((-2*n*(2-theta))/(n^2+(2-theta)))*(-5/(D*theta*(2-theta))) =
      (-4*(n^2-(2-theta))+10*n)/(D*theta*(n^2+(2-theta))) := by
  field_simp [ht,hp,hD,hn] <;> ring

/-- Explicit noncancelling residue. No claim that rational correspondences
have uniformly bounded degree follows from this arithmetic identity. -/
theorem cayley_seed_residue29 :
    (-4*((1 : ZMod 29)^2-(2-3))+10*1) = 2 := by decide

end DASHI.Hodge.CubicCM
