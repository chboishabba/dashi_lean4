import Synthesis.MillenniumBSDEtaEllipticOneModFourReduction
import Mathlib.Tactic

/-!
# First surviving eta/elliptic coefficient agrees

The quarter-factorization `f(q)=q H(q^4)` has `H(0)=1`.  Since the Euler
products defining `H` are differentiable near zero, the product rule gives
`f'(0)=1`.  Thus the canonical eta Taylor coefficient `c₁` is 1, exactly the
already-constructed elliptic coefficient `a₁`.
-/

namespace Synthesis.Millennium.BSD

open Complex Set

theorem cmEta32QuarterFactor_differentiableAt_zero :
    DifferentiableAt ℂ cmEta32QuarterFactor 0 := by
  have hP : DifferentiableAt ℂ cmEtaEulerProduct 0 :=
    (cmEtaEulerProduct_differentiableOn_unitDisk 0 (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp))
  have hP2 :
      DifferentiableAt ℂ (fun u : ℂ => cmEtaEulerProduct (u ^ 2)) 0 :=
    hP.comp 0 (by fun_prop)
  change DifferentiableAt ℂ
    (fun u : ℂ => (cmEtaEulerProduct u) ^ 2 *
      (cmEtaEulerProduct (u ^ 2)) ^ 2) 0
  exact (hP.pow 2).mul (hP2.pow 2)

theorem cmEta32QProduct_hasDerivAt_zero :
    HasDerivAt cmEta32QProduct 1 0 := by
  have hHcomp :
      DifferentiableAt ℂ
        (fun q : ℂ => cmEta32QuarterFactor (q ^ 4)) 0 :=
    cmEta32QuarterFactor_differentiableAt_zero.comp 0 (by fun_prop)
  have hprod := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul hHcomp.hasDerivAt
  have hprodOne :
      HasDerivAt
        (fun q : ℂ => q * cmEta32QuarterFactor (q ^ 4)) 1 0 := by
    convert hprod using 1 <;> simp [cmEta32QuarterFactor_zero]
  exact hprodOne.congr_of_eq
    (funext cmEta32QProduct_eq_q_mul_quarterFactor).symm

theorem cmEta32TaylorCoeff_one :
    cmEta32TaylorCoeff 1 = 1 := by
  unfold cmEta32TaylorCoeff
  rw [iteratedDeriv_one, cmEta32QProduct_hasDerivAt_zero.deriv]
  norm_num

theorem cmEllipticCoefficientComplex_one :
    cmEllipticCoefficientComplex 1 = 1 := by
  simp [cmEllipticCoefficientComplex, cmAllNCoefficient_one]

theorem etaElliptic_agree_at_one :
    cmEta32TaylorCoeff 1 = cmEllipticCoefficientComplex 1 := by
  rw [cmEta32TaylorCoeff_one, cmEllipticCoefficientComplex_one]

end Synthesis.Millennium.BSD
