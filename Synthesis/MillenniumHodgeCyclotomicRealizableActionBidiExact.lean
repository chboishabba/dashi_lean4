import Synthesis.MillenniumHodgeCubicCMExplicitSeed

/-! Reverse-solve the exact original cyclotomic lift against a rational
subalgebra of realizable actions. This is a BIDI algebraic criterion,
not a construction of the cycle-class image or proof of Hodge. -/
namespace DASHI.Hodge.CubicCM

theorem middleStar_mem_iff_cyclotomic_mem {F : Type*} [Field F]
    [CharZero F] [Algebra ℚ F] (A : Subalgebra ℚ F) (theta j : F)
    (ht : theta^3+theta^2-2*theta-1=0) (hj : j^2=theta-2)
    (hθ : theta ∈ A) :
    j ∈ A ↔ middleCyclotomicLift theta j ∈ A := by
  constructor
  · intro hJ
    have hnum : theta + (1-theta-theta^2)*j ∈ A :=
      A.add_mem hθ (A.mul_mem (A.sub_mem (A.sub_mem A.one_mem hθ)
        (A.pow_mem hθ 2)) hJ)
    have hhalf : (1/2 : F) ∈ A := by
      simpa using A.algebraMap_mem (1/2 : ℚ)
    unfold middleCyclotomicLift
    convert A.mul_mem hnum hhalf using 1 <;> ring
  · intro hR
    rw [← middleCyclotomicLift_recovers_star theta j ht hj]
    exact A.sub_mem (A.pow_mem hR 4) (A.pow_mem hR 3)

end DASHI.Hodge.CubicCM
