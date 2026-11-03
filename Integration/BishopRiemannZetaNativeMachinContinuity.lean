import Integration.BishopRound11ImaginaryProductSemanticReflection
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# K04d: native complex exponential Dirichlet / genuine zeta (Lean mirror)

On the ORIGINAL mathematics, the Dirichlet term is exp(-s log(n+1)).
This file proves finite-term continuity, exact identification of the
constructed complex exponential term with the standard complex power,
and the actual Riemann zeta same-value formula in Re(s)>1.

The real Machin limit is mapped to the TRUE Real.pi by the already
proved faithful source evaluator. Mathlib's original completed zeta
is then continuous at that literal selected point.

IMPORTANT: this proves facts on the Lean faithful Bishop COMPLETION
mirror. The Agda RiemannAnalyticSubstrate has an opaque, independently
selected Function/zetaHalfPlane. It is NOT automatically identified
with this selected Lean riemannZeta. That source owner needs explicit
same-object transport and observed Agda elaboration.

Attribution: Dirichlet, Riemann, Cauchy, Bishop/Bridges, Murray,
Viktor Csimma, original DASHI authors, Mathlib zeta owners.
-/

namespace Integration.BishopRiemannZetaNativeMachinContinuity

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopRound11MachinSourceBinding
open Integration.BishopRound11ImaginaryProductSemanticReflection

noncomputable section

/-- Same literal complex exponential coefficient exp(-s L_n), after
native logarithm evaluation gives L_n = log(n+1). -/
def originalDirichletTerm (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * ((Real.log (((n + 1 : ℕ) : ℝ))) : ℂ))

/-- FINITE TERM: no assumptions; the original complex exponential
is continuous as a function of its variable s. -/
theorem originalDirichletTerm_continuous (n : ℕ) :
    Continuous (originalDirichletTerm n) := by
  unfold originalDirichletTerm
  fun_prop

private theorem successorNatComplexNonzero (n : ℕ) :
    (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  exact_mod_cast (show n + 1 ≠ 0 by omega)

/-- Same term as the actual classical Riemann Dirichlet coefficient. -/
theorem originalDirichletTerm_eq_cpow (n : ℕ) (s : ℂ) :
    originalDirichletTerm n s =
      1 / ((((n + 1 : ℕ) : ℂ)) ^ s) := by
  have hn := successorNatComplexNonzero n
  rw [one_div, Complex.cpow_def_of_ne_zero hn s, ← Complex.exp_neg]
  unfold originalDirichletTerm
  congr 1
  rw [Complex.natCast_log]
  ring

/-- The genuine complex series, not an abstract zeta-like function. -/
def originalDirichletValue (s : ℂ) : ℂ :=
  ∑' n : ℕ, originalDirichletTerm n s

/-- SAME-OBJECT on Lean's genuine mathematical zeta for Re(s)>1.
No alternate analytic function or finite prime sieve is introduced. -/
theorem originalDirichletValue_eq_riemannZeta (s : ℂ)
    (hs : 1 < s.re) :
    originalDirichletValue s = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  unfold originalDirichletValue
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using
    originalDirichletTerm_eq_cpow n s

private theorem realPiGreaterOne : (1 : ℝ) < Real.pi :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) Real.two_le_pi

theorem originalDirichletAtMachinPi_eq_genuineZeta :
    originalDirichletValue (Real.pi : ℂ) =
      riemannZeta (Real.pi : ℂ) :=
  originalDirichletValue_eq_riemannZeta (Real.pi : ℂ)
    (by simpa using realPiGreaterOne)

private theorem complexPiNeOne : (Real.pi : ℂ) ≠ 1 := by
  intro h
  have hp : Real.pi = 1 := by simpa using congrArg Complex.re h
  linarith [Real.two_le_pi]

private theorem complexPiNeZero : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- TRUE selected Riemann zeta is continuous at Bishop Machin pi,
once its actual source evaluator identifies the two points. -/
theorem riemannZeta_continuousAtMachinPi :
    ContinuousAt riemannZeta (Real.pi : ℂ) :=
  (differentiableAt_riemannZeta complexPiNeOne).continuousAt

/-- TRUE selected completed zeta has no pole at the Machin point.
The domain is proved, not inferred from an opaque Meromorphic field. -/
theorem completedRiemannZeta_continuousAtMachinPi :
    ContinuousAt completedRiemannZeta (Real.pi : ℂ) :=
  (differentiableAt_completedZeta complexPiNeZero complexPiNeOne).continuousAt

/-- The *original* Machin real on any Bishop source binding has
the same evaluated point as the actual Riemann/completed zeta target. -/
theorem sourceMachinPi_realArgument
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    ((eval (sourceMachinPi A B) : ℝ) : ℂ) = (Real.pi : ℂ) := by
  rw [sourceMachinPiEvaluatesToClassicalPi]

/-- Exact selected-source, not merely a name-aligned zeta evaluation. -/
theorem originalDirichletAtBishopSourcePi
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    originalDirichletValue
        (((eval (sourceMachinPi A B) : ℝ) : ℂ)) =
      riemannZeta
        (((eval (sourceMachinPi A B) : ℝ) : ℂ)) := by
  rw [sourceMachinPi_realArgument A B]
  exact originalDirichletAtMachinPi_eq_genuineZeta

end

end Integration.BishopRiemannZetaNativeMachinContinuity
