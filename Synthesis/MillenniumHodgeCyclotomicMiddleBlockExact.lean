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
  linear_combination (-theta^2+theta+3)*ht

theorem cyclotomicMiddleBlock_trace {F : Type*} [Field F] [CharZero F]
    (theta a b : F) :
    (cyclotomicMiddleBlock theta a b).trace = theta := by
  simp [cyclotomicMiddleBlock,Matrix.trace,Fin.sum_univ_two]
  ring

theorem cyclotomicMiddleBlock_det {F : Type*} [Field F] [CharZero F]
    (theta a b : F) (ht : theta^3+theta^2-2*theta-1=0)
    (hab : a*b=2-theta) :
    (cyclotomicMiddleBlock theta a b).det = 1 := by
  have h := cyclotomic_middle_norm_relation theta ht
  rw [Matrix.det_fin_two]
  simp [cyclotomicMiddleBlock]
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
    first | ring | linear_combination -h/4 - ((1-theta-theta^2)^2/4)*hab

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

end DASHI.Hodge.CubicCM
