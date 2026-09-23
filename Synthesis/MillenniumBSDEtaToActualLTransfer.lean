import Synthesis.MillenniumBSDEtaEllipticSturmEightBoundary
import Synthesis.MillenniumBSDJacobiEta32Reduction
import Synthesis.MillenniumBSDCMEta32Decay
import Synthesis.MillenniumBSDHasseGlobalCoefficientBound
import Synthesis.MillenniumBSDFullGlobalAnalyticLFunction
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Conditional transfer from the eta Mellin continuation to the actual elliptic L-series

This file is intentionally prize-facing and specialized.  The only remaining
analytic same-object producer is `Level32Weight2SturmPrinciple`.

Assuming that one theorem, the already-proved coefficient equality identifies
the normalized eta kernel with the exponential generating kernel of the
literal elliptic coefficients.  Mathlib's generic Mellin=Dirichlet theorem
then gives, on the absolute-convergence half-plane,

  Λ_eta(s) = Γ(s) * rho^(-s) * L(E,s),

where rho = 2*pi/sqrt(32).  Since Λ_eta is already entire and satisfies
`Λ_eta(2-s)=Λ_eta(s)`, this is the exact transport seam required to attach
the continuation and functional equation to the actual elliptic L-function.
-/

namespace Synthesis.Millennium.BSD

open Complex Set Filter

/-- The actual completed elliptic L-expression on its initial convergence domain. -/
noncomputable def cmCompletedEllipticLInitial (s : ℂ) : ℂ :=
  Gamma s * (cmEta32DecayRate : ℂ) ^ (-s) * cmLSeries s

/-- The only same-object datum consumed by the Mellin transfer: equality of every
canonical eta Taylor coefficient with the literal elliptic coefficient.  This is
deliberately producer-agnostic, so Sturm and Jacobi proofs can feed the same
analytic continuation compiler. -/
def EtaEllipticAllCoefficientAgreement : Prop :=
  ∀ n : ℕ, cmEta32TaylorCoeff n = cmEllipticCoefficientComplex n

/-- Sturm equality, together with the already-proved n=0 vanishing, gives the
producer-agnostic all-coefficient datum. -/
theorem etaElliptic_allCoefficientAgreement_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple) :
    EtaEllipticAllCoefficientAgreement := by
  intro n
  rcases n with _ | n
  · have heta : cmEta32TaylorCoeff 0 = 0 :=
      cmEta32TaylorCoeff_eq_zero_of_mod_four_ne_one (by norm_num)
    have hell : cmAllNCoefficient 0 = 0 := by
      rw [cmAllNCoefficient_eq_fullyExplicit, cmFullyExplicitCoefficient_zero]
    simp [cmEllipticCoefficientComplex, heta, hell]
  · exact etaElliptic_positiveAgreement_of_level32Sturm sturm (n + 1) (by omega)

/-- The Jacobi route feeds exactly the same all-coefficient interface.  The
positive coefficients come from the two specialized q-product identities plus
the finite representation/elliptic arithmetic theorem; the zero coefficient is
the already-proved support fact. -/
theorem etaElliptic_allCoefficientAgreement_of_jacobi
    (hOdd : cmJacobiOddProductIdentity)
    (hEven : cmJacobiEvenProductIdentity)
    (hArithmetic : JacobiRepresentationMatchesElliptic) :
    EtaEllipticAllCoefficientAgreement := by
  intro n
  rcases n with _ | n
  · have heta : cmEta32TaylorCoeff 0 = 0 :=
      cmEta32TaylorCoeff_eq_zero_of_mod_four_ne_one (by norm_num)
    have hell : cmAllNCoefficient 0 = 0 := by
      rw [cmAllNCoefficient_eq_fullyExplicit, cmFullyExplicitCoefficient_zero]
    simp [cmEllipticCoefficientComplex, heta, hell]
  · exact etaEllipticPositiveAgreement_of_jacobi hOdd hEven hArithmetic
      (n + 1) (by omega)

/-- The normalized eta kernel has the actual elliptic coefficients as its
exponential series from any all-coefficient producer. -/
theorem cmEta32Kernel_hasSum_ellipticCoefficients_of_coefficientAgreement
    (hcoeff : EtaEllipticAllCoefficientAgreement)
    {t : ℝ} (ht : 0 < t) :
    HasSum
      (fun n : ℕ =>
        cmEllipticCoefficientComplex n *
          Real.exp (-(cmEta32DecayRate * (n : ℝ)) * t))
      (cmEta32Kernel t) := by
  let q : ℂ := (Real.exp (-cmEta32DecayRate * t) : ℂ)
  have hq : ‖q‖ < 1 := by
    simp only [q, Complex.norm_real, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr cmEta32DecayRate_pos) ht
  have hformal := hasSum_cmEta32FormalSeries hq
  have hkernel : cmEta32QProduct q = cmEta32Kernel t := by
    unfold cmEta32Kernel
    rw [cmEta32_eq_qProduct, qParam_eta32Kernel]
    rfl
  rw [hkernel] at hformal
  refine hformal.congr_fun ?_
  intro n
  rw [cmEta32_formal_coeff_eq_TaylorCoeff]
  rw [hcoeff n]
  congr 1
  change q ^ n = (Real.exp (-(cmEta32DecayRate * (n : ℝ)) * t) : ℂ)
  simp only [q, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- Sturm remains available as a compatibility wrapper, but is no longer
load-bearing in the analytic transfer. -/
theorem cmEta32Kernel_hasSum_ellipticCoefficients_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple)
    {t : ℝ} (ht : 0 < t) :
    HasSum
      (fun n : ℕ =>
        cmEllipticCoefficientComplex n *
          Real.exp (-(cmEta32DecayRate * (n : ℝ)) * t))
      (cmEta32Kernel t) :=
  cmEta32Kernel_hasSum_ellipticCoefficients_of_coefficientAgreement
    (etaElliptic_allCoefficientAgreement_of_level32Sturm sturm) ht

/-- Hasse growth makes the scaled Mellin coefficient series absolutely summable. -/
theorem cmElliptic_scaledMellin_norm_summable
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    Summable (fun n : ℕ =>
      ‖cmEllipticCoefficientComplex n‖ /
        (cmEta32DecayRate * (n : ℝ)) ^ s.re) := by
  have hexp : (3 : ℝ) / 2 - s.re < -1 := by linarith
  have hmajor : Summable (fun n : ℕ =>
      cmEta32DecayRate ^ (-s.re) *
        (n : ℝ) ^ ((3 : ℝ) / 2 - s.re)) :=
    (Real.summable_nat_rpow.mpr hexp).mul_left _
  refine hmajor.of_nonneg_of_le (fun n => by positivity) ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [cmEllipticCoefficientComplex, cmAllNCoefficient_eq_fullyExplicit,
      cmFullyExplicitCoefficient_zero]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hcoeff := cmAllNCoefficient_abs_le_rpow_three_halves n
    have hrate0 : 0 ≤ cmEta32DecayRate := cmEta32DecayRate_pos.le
    have hrateNe : cmEta32DecayRate ≠ 0 := ne_of_gt cmEta32DecayRate_pos
    have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hn0
    calc
      ‖cmEllipticCoefficientComplex n‖ /
          (cmEta32DecayRate * (n : ℝ)) ^ s.re
        = |(cmAllNCoefficient n : ℝ)| /
          (cmEta32DecayRate * (n : ℝ)) ^ s.re := by
            simp [cmEllipticCoefficientComplex, Complex.norm_intCast]
      _ ≤ (n : ℝ) ^ ((3 : ℝ) / 2) /
          (cmEta32DecayRate * (n : ℝ)) ^ s.re := by
            gcongr
      _ = cmEta32DecayRate ^ (-s.re) *
          (n : ℝ) ^ ((3 : ℝ) / 2 - s.re) := by
            rw [Real.mul_rpow hrate0 hn0.le]
            rw [Real.rpow_neg hrate0]
            rw [Real.rpow_sub hn0 (3 / 2) s.re]
            field_simp [Real.rpow_ne_zero_of_pos cmEta32DecayRate_pos,
              Real.rpow_ne_zero_of_pos hn0]
            ring

/-- The Mellin transform of the eta kernel equals the completed actual elliptic L-expression. -/
theorem cmEta32_mellin_eq_completedEllipticLInitial_of_coefficientAgreement
    (hcoeff : EtaEllipticAllCoefficientAgreement)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    mellin cmEta32Kernel s = cmCompletedEllipticLInitial s := by
  have hs0 : 0 < s.re := by linarith
  have hp : ∀ n : ℕ,
      cmEllipticCoefficientComplex n = 0 ∨
        0 < cmEta32DecayRate * (n : ℝ) := by
    intro n
    rcases n with _ | n
    · left
      simp [cmEllipticCoefficientComplex, cmAllNCoefficient_eq_fullyExplicit,
        cmFullyExplicitCoefficient_zero]
    · right
      positivity
  have hm := hasSum_mellin
    (a := cmEllipticCoefficientComplex)
    (p := fun n : ℕ => cmEta32DecayRate * (n : ℝ))
    (F := cmEta32Kernel)
    (s := s)
    hp hs0
    (fun t ht =>
      cmEta32Kernel_hasSum_ellipticCoefficients_of_coefficientAgreement hcoeff ht)
    (cmElliptic_scaledMellin_norm_summable hs)
  have hLsum : HasSum
      (fun n : ℕ => LSeries.term ((↑) ∘ cmAllNCoefficient) s n)
      (cmLSeries s) := by
    exact (cmLSeriesSummable_hasse_global hs).hasSum
  have hscaled := hLsum.mul_left
    (Gamma s * (cmEta32DecayRate : ℂ) ^ (-s))
  have hsummands :
      (fun n : ℕ =>
        Gamma s * cmEllipticCoefficientComplex n /
          ((cmEta32DecayRate * (n : ℝ) : ℝ) : ℂ) ^ s)
      =
      (fun n : ℕ =>
        (Gamma s * (cmEta32DecayRate : ℂ) ^ (-s)) *
          LSeries.term ((↑) ∘ cmAllNCoefficient) s n) := by
    funext n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [cmEllipticCoefficientComplex, cmAllNCoefficient_eq_fullyExplicit,
        cmFullyExplicitCoefficient_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0]
      simp only [cmEllipticCoefficientComplex, Function.comp_apply]
      rw [show (((cmEta32DecayRate * (n : ℝ) : ℝ) : ℂ)) =
          (cmEta32DecayRate : ℂ) * (n : ℂ) by norm_num]
      rw [mul_cpow_ofReal_nonneg
        cmEta32DecayRate_pos.le (Nat.cast_nonneg n)]
      rw [cpow_neg]
      field_simp [cpow_ne_zero]
      ring
  rw [hsummands] at hm
  have hvalue := hm.unique hscaled
  simpa [cmCompletedEllipticLInitial] using hvalue

/-- Compatibility wrapper for the historical Sturm producer. -/
theorem cmEta32_mellin_eq_completedEllipticLInitial_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    mellin cmEta32Kernel s = cmCompletedEllipticLInitial s :=
  cmEta32_mellin_eq_completedEllipticLInitial_of_coefficientAgreement
    (etaElliptic_allCoefficientAgreement_of_level32Sturm sturm) hs

/-- On the initial half-plane, the already-entire eta completion is the actual
completed L from any coefficient-equality producer. -/
theorem cmEta32CompletedMellin_eq_completedEllipticLInitial_of_coefficientAgreement
    (hcoeff : EtaEllipticAllCoefficientAgreement)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    cmEta32CompletedMellin s = cmCompletedEllipticLInitial s := by
  rw [cmEta32CompletedMellin_eq_mellin]
  exact cmEta32_mellin_eq_completedEllipticLInitial_of_coefficientAgreement hcoeff hs

/-- Compatibility wrapper for the historical Sturm producer. -/
theorem cmEta32CompletedMellin_eq_completedEllipticLInitial_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    cmEta32CompletedMellin s = cmCompletedEllipticLInitial s :=
  cmEta32CompletedMellin_eq_completedEllipticLInitial_of_coefficientAgreement
    (etaElliptic_allCoefficientAgreement_of_level32Sturm sturm) hs

/--
Prize-facing analytic continuation object for the actual completed elliptic L-function.
Under the one specialized Sturm theorem it agrees with the literal Dirichlet L-expression
on its convergence half-plane, is entire, and satisfies the weight-two functional equation.
-/
noncomputable def cmCompletedEllipticLContinuation (s : ℂ) : ℂ :=
  cmEta32CompletedMellin s

theorem cmCompletedEllipticLContinuation_entire :
    Differentiable ℂ cmCompletedEllipticLContinuation := by
  exact cmEta32CompletedMellin_entire

theorem cmCompletedEllipticLContinuation_agrees_initial_of_coefficientAgreement
    (hcoeff : EtaEllipticAllCoefficientAgreement)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    cmCompletedEllipticLContinuation s = cmCompletedEllipticLInitial s :=
  cmEta32CompletedMellin_eq_completedEllipticLInitial_of_coefficientAgreement hcoeff hs

theorem cmCompletedEllipticLContinuation_agrees_initial_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    cmCompletedEllipticLContinuation s = cmCompletedEllipticLInitial s :=
  cmCompletedEllipticLContinuation_agrees_initial_of_coefficientAgreement
    (etaElliptic_allCoefficientAgreement_of_level32Sturm sturm) hs

theorem cmCompletedEllipticLContinuation_functional_equation (s : ℂ) :
    cmCompletedEllipticLContinuation (2 - s) =
      cmCompletedEllipticLContinuation s := by
  exact cmEta32CompletedMellin_functional_equation s

end Synthesis.Millennium.BSD
