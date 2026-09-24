import Synthesis.MillenniumBSDCMEta32Kernel
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Tactic

/-!
# Literal q-product for the level-32 CM eta form

Writing q = exp(2πiz), the eta-product used by the CM continuation lane is

  f32(z) = q · (∏_{n≥0}(1-q^(4(n+1))))²
             · (∏_{n≥0}(1-q^(8(n+1))))².

This follows directly from mathlib's literal definition of Dedekind eta, so
the q-product is the same function as `cmEta32`, not an external modular-form
identification.
-/

namespace Synthesis.Millennium.BSD

open Complex
open Function

noncomputable def cmEta32QProduct (q : ℂ) : ℂ :=
  q * (∏' n : ℕ, (1 - q ^ (4 * (n + 1)))) ^ 2 *
    (∏' n : ℕ, (1 - q ^ (8 * (n + 1)))) ^ 2

theorem eta_q_scaled_four (n : ℕ) (z : ℂ) :
    ModularForm.eta_q n (4 * z) =
      (Function.Periodic.qParam 1 z) ^ (4 * (n + 1)) := by
  rw [ModularForm.eta_q_eq_cexp]
  rw [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem eta_q_scaled_eight (n : ℕ) (z : ℂ) :
    ModularForm.eta_q n (8 * z) =
      (Function.Periodic.qParam 1 z) ^ (8 * (n + 1)) := by
  rw [ModularForm.eta_q_eq_cexp]
  rw [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem eta_qParam_prefactor_four_eight (z : ℂ) :
    (Function.Periodic.qParam 24 (4 * z)) ^ 2 *
      (Function.Periodic.qParam 24 (8 * z)) ^ 2
      = Function.Periodic.qParam 1 z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem cmEta32_eq_qProduct (z : ℂ) :
    cmEta32 z =
      cmEta32QProduct (Function.Periodic.qParam 1 z) := by
  unfold cmEta32 cmEta32QProduct ModularForm.eta
  rw [mul_pow, mul_pow]
  rw [eta_qParam_prefactor_four_eight]
  simp_rw [eta_q_scaled_four, eta_q_scaled_eight]
  ring

theorem cmEta32QProduct_zero :
    cmEta32QProduct 0 = 0 := by
  simp [cmEta32QProduct]

theorem cmEta32QProduct_factorization (q : ℂ) :
    cmEta32QProduct q = q *
      ((∏' n : ℕ, (1 - q ^ (4 * (n + 1)))) ^ 2 *
       (∏' n : ℕ, (1 - q ^ (8 * (n + 1)))) ^ 2) := by
  simp [cmEta32QProduct, mul_assoc]

end Synthesis.Millennium.BSD
