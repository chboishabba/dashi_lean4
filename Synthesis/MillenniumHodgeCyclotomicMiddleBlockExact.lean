import Synthesis.MillenniumHodgeCubicCMExplicitSeed

/-!
The actual complementary-triple middle-star block is nonsplit. Construct
the order-seven candidate directly on that two-plane, not by substituting
an abstract field label. Its trace, determinant, quadratic relation and
orientation entries are explicit. Algebraic realization by cycle classes
is still an independent obligation on the generic projected motive.
-/
namespace DASHI.Hodge.CubicCM
open Matrix

def cyclotomicMiddleBlock {F : Type*} [Field F] (theta a b : F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![theta/2,-(1-theta-theta^2)*b/2;
     (1-theta-theta^2)*a/2,theta/2]

theorem cyclotomic_middle_norm_relation {F : Type*} [Field F] (theta : F)
    (ht : theta^3+theta^2-2*theta-1=0) :
    theta^2+(1-theta-theta^2)^2*(2-theta)=4 := by
  linear_combination (-theta^2+theta+2)*ht

theorem cyclotomicMiddleBlock_trace {F : Type*} [Field F] [CharZero F]
    (theta a b : F) :
    (cyclotomicMiddleBlock theta a b).trace = theta := by
  simp [cyclotomicMiddleBlock,Matrix.trace,Fin.sum_univ_two] <;> ring

theorem cyclotomicMiddleBlock_det {F : Type*} [Field F] [CharZero F]
    (theta a b : F) (ht : theta^3+theta^2-2*theta-1=0)
    (hab : a*b=2-theta) :
    (cyclotomicMiddleBlock theta a b).det = 1 := by
  have h := cyclotomic_middle_norm_relation theta ht
  rw [Matrix.det_fin_two]
  change theta/2*(theta/2) -
      (-(1-theta-theta^2)*b/2)*((1-theta-theta^2)*a/2) = 1
  have he : theta/2*(theta/2) -
      (-(1-theta-theta^2)*b/2)*((1-theta-theta^2)*a/2) =
      (theta^2+(1-theta-theta^2)^2*(a*b))/4 := by ring
  rw [he,hab,h]
  norm_num

/-- Actual two-plane operator equation, derived on its signed matrix
entries. Not merely equality of trace or characteristic data. -/
theorem cyclotomicMiddleBlock_quad {F : Type*} [Field F] [CharZero F]
    (theta a b : F) (ht : theta^3+theta^2-2*theta-1=0)
    (hab : a*b=2-theta) :
    cyclotomicMiddleBlock theta a b * cyclotomicMiddleBlock theta a b -
      theta • cyclotomicMiddleBlock theta a b + 1 = 0 := by
  have h := cyclotomic_middle_norm_relation theta ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclotomicMiddleBlock,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.one_apply] <;>
    first | ring | linear_combination (-1/4)*h - ((1-theta-theta^2)^2/4)*hab

/-- If the original F-action and a realization of the nonsplit J are
available, the matrix lift is its explicit rational linear combination.
This identifies the actual orientation-bearing block to be realized. -/
theorem cyclotomicMiddleBlock_formula {F : Type*} [Field F] [CharZero F]
    (theta a b : F) :
    cyclotomicMiddleBlock theta a b =
      (theta/2) • (1 : Matrix (Fin 2) (Fin 2) F) +
        ((1-theta-theta^2)/2) • middleStarBlock a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclotomicMiddleBlock,middleStarBlock,Matrix.one_apply] <;> ring

/-- Recover the ORIGINAL signed middle star as a polynomial in the
actual complementary-plane matrix. The coefficients below are exact
polynomial-ideal reductions against ab=2-theta and the cubic. -/
theorem cyclotomicMiddleBlock_recovers_star {F : Type*} [Field F] [CharZero F]
    (theta a b : F) (ht : theta^3+theta^2-2*theta-1=0)
    (hab : a*b=2-theta) :
    cyclotomicMiddleBlock theta a b ^ 4 -
      cyclotomicMiddleBlock theta a b ^ 3 = middleStarBlock a b := by
  have h : a*b+theta-2=0 := by rw [hab]; ring
  let qd : F := -(theta^2+theta-1)^2*
    (-a*b*theta^4-2*a*b*theta^3+a*b*theta^2+2*a*b*theta-a*b+
      theta^5-5*theta^3+6*theta^2-theta-2)/16
  let pd : F := (theta-2)*(theta-1)*
    (theta^5+2*theta^4-3*theta^3-theta^2+5*theta-2)/16
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ,cyclotomicMiddleBlock,middleStarBlock,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  · linear_combination qd*h+pd*ht
  · linear_combination
      (-b*(2*theta-1)*(theta^2+theta-1)^3/8)*h+
      (b*(theta+2)*(2*theta^4-5*theta^3+2*theta^2+2*theta-3)/8)*ht
  · linear_combination
      (a*(2*theta-1)*(theta^2+theta-1)^3/8)*h-
      (a*(theta+2)*(2*theta^4-5*theta^3+2*theta^2+2*theta-3)/8)*ht
  · linear_combination qd*h+pd*ht

/-- BIDI in the actual rational MATRIX subalgebra, not a scalar
field membership substitute. The algebra of realized correspondences
must still be shown to map to such a subalgebra on the actual motive. -/
theorem middleBlock_realizable_iff_cyclotomic {F : Type*} [Field F]
    [CharZero F] [Algebra ℚ F]
    (A : Subalgebra ℚ (Matrix (Fin 2) (Fin 2) F))
    (theta a b : F) (ht : theta^3+theta^2-2*theta-1=0)
    (hab : a*b=2-theta)
    (hθ : theta • (1 : Matrix (Fin 2) (Fin 2) F) ∈ A) :
    middleStarBlock a b ∈ A ↔ cyclotomicMiddleBlock theta a b ∈ A := by
  let T := theta • (1 : Matrix (Fin 2) (Fin 2) F)
  constructor
  · intro hJ
    have hT : T ∈ A := hθ
    have hnum : T+(1-T-T*T)*middleStarBlock a b ∈ A :=
      A.add_mem hT (A.mul_mem
        (A.sub_mem (A.sub_mem A.one_mem hT) (A.mul_mem hT hT)) hJ)
    have he : cyclotomicMiddleBlock theta a b =
        (1/2 : ℚ) • (T+(1-T-T*T)*middleStarBlock a b) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [T,cyclotomicMiddleBlock,middleStarBlock,
          Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,Algebra.smul_def]
        <;> ring
    rw [he]
    exact A.toSubmodule.smul_mem (1/2 : ℚ) hnum
  · intro hR
    rw [← cyclotomicMiddleBlock_recovers_star theta a b ht hab]
    exact A.sub_mem (A.pow_mem hR 4) (A.pow_mem hR 3)

end DASHI.Hodge.CubicCM
