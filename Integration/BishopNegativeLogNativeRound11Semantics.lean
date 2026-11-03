import Integration.BishopRound11MachinSourceBinding
import Integration.BishopVendoredCompletionEquivalence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Bishop negative-log series: source-faithful Nat-exp inverse

This module deliberately mirrors the *actual* DASHI canonical source terms

  x^(n+1)/(n+1)

from `BishopNegativeLogGeometricSourceConvergenceExact.agda`, using the
exact pinned Bishop resampled arithmetic and exact convergence semantics.
No abstract inverse-log function is substituted for that limit.

Mathlib's independent real analytic theorem
`Real.hasSum_pow_div_log_of_abs_lt_one` identifies those finite series
under the canonical vendored evaluation.  Since evaluation reflects the
Bishop setoid equality, the original source series then satisfies
exp_B(L((n+1)/(n+2))) ~ (n+2), *when the original concrete Bishop
source convergence witness is connected*.

The imported `Round11MachinSourceBinding` provides the very same
source exponential convergence data, not an independent exponential.

IMPORTANT: This is a Lean mirror proof and cannot automatically
serve as an Agda kernel proof. The source convergence binder must
be connected to Agda's original canonical source term and genuine
Agda kernel checks must be observed before golden promotion.

Original authors: Riemann, Cauchy, Bishop and Bridges; Zachary
Murray (2022); pinned Viktor Csimma Bishop library; Mathlib and
the original DASHI source theorem owners.
-/

namespace Integration.BishopNegativeLogNativeRound11Semantics

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredExponentialSemantics
open Integration.BishopVendoredCompletionEquivalence
open Integration.BishopRound11MachinSourceBinding

noncomputable section

/-- Literal original negative-log coefficient x^(n+1)/(n+1). -/
def negativeLogTerm (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) : RegularRatReal :=
  A.mul (sourcePow A x (n + 1))
    (rational (1 / ((n + 1 : ℕ) : ℚ)))

theorem eval_negativeLogTerm (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (n : ℕ) :
    eval (negativeLogTerm A x n) =
      (eval x) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  rw [negativeLogTerm, A.eval_mul, eval_sourcePow, eval_rational]
  norm_cast <;> ring

/-- Finite prefixes use the vendored resampled Bishop real addition. -/
def negativeLogPartial (A : VendoredArithmeticMirror)
    (x : RegularRatReal) : ℕ → RegularRatReal
  | 0 => A.zero
  | n + 1 => A.add (negativeLogPartial A x n) (negativeLogTerm A x n)

theorem eval_negativeLogPartial (A : VendoredArithmeticMirror)
    (x : RegularRatReal) (N : ℕ) :
    eval (negativeLogPartial A x N) =
      ∑ n ∈ Finset.range N,
        (eval x) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  induction N with
  | zero =>
      simp [negativeLogPartial, A.eval_zero]
  | succ n ih =>
      rw [negativeLogPartial, A.eval_add, ih, eval_negativeLogTerm]
      simp only [Finset.sum_range_succ]

/-- Same original series convergence, not a free logarithm inverse. -/
structure NativeNegativeLogSourceConvergence
    (A : VendoredArithmeticMirror) where
  negativeLog : RegularRatReal → RegularRatReal
  convergence :
    ∀ x : RegularRatReal,
      0 < eval x → eval x < 1 →
      BishopConvergesTo A
        (negativeLogPartial A x) (negativeLog x)

theorem eval_nativeNegativeLog_eq_classical (A : VendoredArithmeticMirror)
    (L : NativeNegativeLogSourceConvergence A)
    (x : RegularRatReal)
    (hzero : 0 < eval x) (hone : eval x < 1) :
    eval (L.negativeLog x) = -Real.log (1 - eval x) := by
  have hx : |eval x| < 1 := abs_lt.mpr ⟨by linarith, hone⟩
  have hsource :
      Tendsto (fun N => eval (negativeLogPartial A x N))
        atTop (𝓝 (eval (L.negativeLog x))) :=
    eval_tendsto_of_bishopConvergesTo A (L.convergence x hzero hone)
  have hclassical :
      Tendsto (fun N => eval (negativeLogPartial A x N))
        atTop (𝓝 (-Real.log (1 - eval x))) := by
    simpa only [eval_negativeLogPartial] using
      (Real.hasSum_pow_div_log_of_abs_lt_one hx).tendsto_sum_nat
  exact tendsto_nhds_unique hsource hclassical

/-- The exact Agda input at index n is (n+1)/(n+2). -/
def natLogArgument (n : ℕ) : ℚ :=
  ((n + 1 : ℕ) : ℚ) / ((n + 2 : ℕ) : ℚ)

private theorem natLogArgument_eval (n : ℕ) :
    eval (rational (natLogArgument n)) =
      ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by
  simp [natLogArgument, eval_rational]

private theorem natLogArgument_bounds (n : ℕ) :
    0 < eval (rational (natLogArgument n)) ∧
      eval (rational (natLogArgument n)) < 1 := by
  rw [natLogArgument_eval]
  have hnum : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hden : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hlt : ((n + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 < n + 2 by omega)
  exact ⟨div_pos hnum hden, (div_lt_one hden).mpr hlt⟩

/-- Same-object Nat-log: the original Bishop power series evaluates
to log(n+2) for each *positive successor* argument. -/
theorem eval_nativeNatLog_successor (A : VendoredArithmeticMirror)
    (L : NativeNegativeLogSourceConvergence A)
    (n : ℕ) :
    eval (L.negativeLog (rational (natLogArgument n))) =
      Real.log (((n + 2 : ℕ) : ℝ)) := by
  obtain ⟨hzero, hone⟩ := natLogArgument_bounds n
  have hlog := eval_nativeNegativeLog_eq_classical A L
    (rational (natLogArgument n)) hzero hone
  rw [natLogArgument_eval] at hlog
  have hden : (0 : ℝ) < (((n + 2 : ℕ) : ℝ)) := by positivity
  have hsub :
      1 - (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) =
        (((n + 2 : ℕ) : ℝ))⁻¹ := by
    field_simp [ne_of_gt hden] <;> push_cast <;> ring
  rw [hsub, Real.log_inv] at hlog
  linarith

/-- The original Nat successor exponential inverse, reflected back
into the vendored Bishop SETOID (not raw sequence equality).
The n=0 log(1)=0 case is already proved on the Agda side. -/
theorem originalNatLog_successor_exp_inverse
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (L : NativeNegativeLogSourceConvergence A)
    (n : ℕ) :
    Equiv
      (B.expB (L.negativeLog (rational (natLogArgument n))))
      (rational (((n + 2 : ℕ) : ℚ))) := by
  apply eval_eq_iff_equiv.mp
  rw [eval_exp_eq_real_exp A (expMirror A B),
    eval_nativeNatLog_successor A L n, eval_rational]
  rw [Real.exp_log (by positivity : (0 : ℝ) < (((n + 2 : ℕ) : ℝ)))]
  norm_cast


/-!
## K04d-PAYMENT: remove the free native-log source convergence input

The original Bishop negative-log coefficients are already constructed in
`negativeLogTerm`. The vendored Bishop convergence bridge reconstructs
a quantitative Bishop limit directly from a Mathlib-summed series.
This `canonicalNegativeLog` is a **representative of that same series**,
not a new arbitrary logarithm authority.

For an actual original Agda `sourceNegativeLogValue`, its own proof of
convergence to these coefficients suffices to show equality of Bishop
setoid classes; no identification is silently presumed.
-/

/-- Canonical Bishop representative of the literal negative-log sum.
This replaces the previously free source convergence record by a
constructively specified completion representative. -/
def canonicalNegativeLog (x : RegularRatReal) : RegularRatReal :=
  encode (-Real.log (1 - eval x))

/-- Actual SOURCE finite sums converge to that representative using
the original pinned Bishop quantitative convergence predicate. -/
theorem canonicalNegativeLog_converges
    (A : VendoredArithmeticMirror)
    (x : RegularRatReal)
    (hzero : 0 < eval x)
    (hone : eval x < 1) :
    BishopConvergesTo A
      (negativeLogPartial A x) (canonicalNegativeLog x) := by
  apply bishopConvergesTo_of_eval_tendsto A
  rw [canonicalNegativeLog, eval_encode]
  have hx : |eval x| < 1 :=
    abs_lt.mpr ⟨by linarith, hone⟩
  simpa only [eval_negativeLogPartial] using
    (Real.hasSum_pow_div_log_of_abs_lt_one hx).tendsto_sum_nat

/-- The previously abstract convergence package now has a *concrete*
source-coefficient inhabitant, with no added analytic inverse law. -/
def canonicalNativeNegativeLogSourceConvergence
    (A : VendoredArithmeticMirror) :
    NativeNegativeLogSourceConvergence A where
  negativeLog := canonicalNegativeLog
  convergence := canonicalNegativeLog_converges A

/-- Exact Nat-positive-successor inverse with NO free log-convergence
witness, on the canonical original-series Bishop representative. -/
theorem canonicalNatSuccessorExpInverse
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (n : ℕ) :
    Equiv
      (B.expB (canonicalNegativeLog (rational (natLogArgument n))))
      (rational (((n + 2 : ℕ) : ℚ))) :=
  originalNatLog_successor_exp_inverse
    A B (canonicalNativeNegativeLogSourceConvergence A) n

/-- Every OTHER original Bishop limit of the literal SAME coefficients
is setoid-equal to the canonical source representative. -/
theorem anyOriginalNegativeLogLimit_equiv_canonical
    (A : VendoredArithmeticMirror)
    (x sourceLimit : RegularRatReal)
    (hzero : 0 < eval x)
    (hone : eval x < 1)
    (sourceConverges :
      BishopConvergesTo A (negativeLogPartial A x) sourceLimit) :
    Equiv sourceLimit (canonicalNegativeLog x) := by
  apply eval_eq_iff_equiv.mp
  exact tendsto_nhds_unique
    (eval_tendsto_of_bishopConvergesTo A sourceConverges)
    (eval_tendsto_of_bishopConvergesTo A
      (canonicalNegativeLog_converges A x hzero hone))

/-- The K04d LOG inverse works for ANY actually constructed source
series limit, including the original Bishop `Sequence.lim` value,
without supplying a free logarithm-inverse or free log-convergence
record. The source limit carries only its already-owned convergence
proof, as in the original Agda module. -/
theorem anyOriginalNatSuccessorExpInverse
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A)
    (n : ℕ)
    (sourceLimit : RegularRatReal)
    (sourceConverges :
      BishopConvergesTo A
        (negativeLogPartial A (rational (natLogArgument n)))
        sourceLimit) :
    Equiv
      (B.expB sourceLimit)
      (rational (((n + 2 : ℕ) : ℚ))) := by
  obtain ⟨hzero, hone⟩ := natLogArgument_bounds n
  have hsame :=
    anyOriginalNegativeLogLimit_equiv_canonical A
      (rational (natLogArgument n)) sourceLimit
      hzero hone sourceConverges
  apply eval_eq_iff_equiv.mp
  have hc := eval_respects_equiv hsame
  have hmain := eval_respects_equiv
    (canonicalNatSuccessorExpInverse A B n)
  rw [eval_exp_eq_real_exp A (expMirror A B) sourceLimit, hc]
  rw [← eval_exp_eq_real_exp A (expMirror A B)
      (canonicalNegativeLog (rational (natLogArgument n)))]
  exact hmain

end

end Integration.BishopNegativeLogNativeRound11Semantics
