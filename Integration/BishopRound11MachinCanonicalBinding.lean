import Integration.BishopVendoredArithmeticConcrete
import Integration.BishopVendoredCompletionEquivalence
import Integration.BishopRound11MachinSourceBinding
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Canonical Round11/Machin binding from the Bishop completion equivalence

The cross-language source receipt is setoid-valued: its limits are Bishop reals
specified by convergence, not by raw representative identity.

The evaluator/encoder equivalence therefore lets us build a canonical Lean
inhabitant of the exact Round11MachinSourceBinding shape:

* expB x  := encode (Real.exp (eval x));
* sinB x  := encode (Real.sin (eval x));
* cosB x  := encode (Real.cos (eval x));
* atan values := encodings of the corresponding classical arctangents.

The reverse convergence theorem converts the standard Mathlib series limits
back into Bishop's exact quantitative 1/k convergence.

Finally, uniqueness of ordinary limits plus evaluator faithfulness proves that
every other binding with the same convergence receipts is Bishop-equivalent
field-for-field to this canonical binding.

This closes mathematical inhabitance of the Lean binding shape.  It does not
claim that generated replay of the named Agda declarations has been observed.
-/

namespace Integration.BishopRound11MachinCanonicalBinding

open Filter
open scoped Topology BigOperators

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredArithmeticConcrete
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredCompletionEquivalence
open Integration.BishopVendoredExponentialSemantics
open Integration.BishopVendoredTrigSemantics
open Integration.BishopVendoredMachinPiSemantics
open Integration.BishopRound11MachinSourceBinding

noncomputable section

abbrev Arithmetic : VendoredArithmeticMirror :=
  concreteVendoredArithmeticMirror

def canonicalExp (x : RegularRatReal) : RegularRatReal :=
  encode (Real.exp (eval x))

def canonicalSin (x : RegularRatReal) : RegularRatReal :=
  encode (Real.sin (eval x))

def canonicalCos (x : RegularRatReal) : RegularRatReal :=
  encode (Real.cos (eval x))

def canonicalAtanOneFifth : RegularRatReal :=
  encode (Real.arctan (1 / 5 : ℝ))

def canonicalAtanOneTwoHundredThirtyNinth : RegularRatReal :=
  encode (Real.arctan (1 / 239 : ℝ))

private theorem exp_partialSums_tendsto
    (x : RegularRatReal) :
    Tendsto
      (fun N => eval (expPartialSum Arithmetic x N))
      atTop
      (𝓝 (eval (canonicalExp x))) := by
  rw [canonicalExp, eval_encode]
  have hs := NormedSpace.expSeries_div_hasSum_exp (eval x)
  rw [← Real.exp_eq_exp_ℝ]
  simpa only [eval_expPartialSum] using hs.tendsto_sum_nat

private theorem sine_partialSums_tendsto
    (x : RegularRatReal) :
    Tendsto
      (fun N => eval (sinePartialSum Arithmetic x N))
      atTop
      (𝓝 (eval (canonicalSin x))) := by
  rw [canonicalSin, eval_encode]
  simpa only [eval_sinePartialSum] using
    (Real.hasSum_sin (eval x)).tendsto_sum_nat

private theorem cosine_partialSums_tendsto
    (x : RegularRatReal) :
    Tendsto
      (fun N => eval (cosinePartialSum Arithmetic x N))
      atTop
      (𝓝 (eval (canonicalCos x))) := by
  rw [canonicalCos, eval_encode]
  simpa only [eval_cosinePartialSum] using
    (Real.hasSum_cos (eval x)).tendsto_sum_nat

private theorem atanOneFifth_partialSums_tendsto :
    Tendsto
      (fun N => eval (atanPartialSum Arithmetic bishopOneFifth N))
      atTop
      (𝓝 (eval canonicalAtanOneFifth)) := by
  rw [canonicalAtanOneFifth, eval_encode]
  have hpoint : eval bishopOneFifth = (1 / 5 : ℝ) := by
    rw [bishopOneFifth, eval_rational]
    norm_num [oneFifth]
  have hs :=
    Real.hasSum_arctan
      (x := (1 / 5 : ℝ))
      (by norm_num : ‖(1 / 5 : ℝ)‖ < 1)
  simpa only [eval_atanPartialSum, hpoint] using hs.tendsto_sum_nat

private theorem atan239_partialSums_tendsto :
    Tendsto
      (fun N =>
        eval (atanPartialSum Arithmetic
          bishopOneTwoHundredThirtyNinth N))
      atTop
      (𝓝 (eval canonicalAtanOneTwoHundredThirtyNinth)) := by
  rw [canonicalAtanOneTwoHundredThirtyNinth, eval_encode]
  have hpoint :
      eval bishopOneTwoHundredThirtyNinth = (1 / 239 : ℝ) := by
    rw [bishopOneTwoHundredThirtyNinth, eval_rational]
    norm_num [oneTwoHundredThirtyNinth]
  have hs :=
    Real.hasSum_arctan
      (x := (1 / 239 : ℝ))
      (by norm_num : ‖(1 / 239 : ℝ)‖ < 1)
  simpa only [eval_atanPartialSum, hpoint] using hs.tendsto_sum_nat

theorem canonicalExp_converges
    (x : RegularRatReal) :
    BishopConvergesTo Arithmetic
      (expPartialSum Arithmetic x)
      (canonicalExp x) :=
  bishopConvergesTo_of_eval_tendsto Arithmetic
    (exp_partialSums_tendsto x)

theorem canonicalSin_converges
    (x : RegularRatReal) :
    BishopConvergesTo Arithmetic
      (sinePartialSum Arithmetic x)
      (canonicalSin x) :=
  bishopConvergesTo_of_eval_tendsto Arithmetic
    (sine_partialSums_tendsto x)

theorem canonicalCos_converges
    (x : RegularRatReal) :
    BishopConvergesTo Arithmetic
      (cosinePartialSum Arithmetic x)
      (canonicalCos x) :=
  bishopConvergesTo_of_eval_tendsto Arithmetic
    (cosine_partialSums_tendsto x)

theorem canonicalAtanOneFifth_converges :
    BishopConvergesTo Arithmetic
      (atanPartialSum Arithmetic bishopOneFifth)
      canonicalAtanOneFifth :=
  bishopConvergesTo_of_eval_tendsto Arithmetic
    atanOneFifth_partialSums_tendsto

theorem canonicalAtan239_converges :
    BishopConvergesTo Arithmetic
      (atanPartialSum Arithmetic bishopOneTwoHundredThirtyNinth)
      canonicalAtanOneTwoHundredThirtyNinth :=
  bishopConvergesTo_of_eval_tendsto Arithmetic
    atan239_partialSums_tendsto

/-- Hypothesis-free inhabitant of the exact Lean-facing source-binding shape. -/
def canonicalBinding : Round11MachinSourceBinding Arithmetic where
  expB := canonicalExp
  sinB := canonicalSin
  cosB := canonicalCos

  atanOneFifth := canonicalAtanOneFifth
  atanOneTwoHundredThirtyNinth := canonicalAtanOneTwoHundredThirtyNinth

  expConverges := canonicalExp_converges
  sinConverges := canonicalSin_converges
  cosConverges := canonicalCos_converges

  atanOneFifthConverges := canonicalAtanOneFifth_converges
  atanOneTwoHundredThirtyNinthConverges := canonicalAtan239_converges

/-- Any two Bishop limits of the same source sequence are Bishop-equivalent. -/
theorem limit_equiv_of_two_convergences
    {f : ℕ → RegularRatReal}
    {x y : RegularRatReal}
    (hx : BishopConvergesTo Arithmetic f x)
    (hy : BishopConvergesTo Arithmetic f y) :
    Equiv x y := by
  apply equiv_of_eval_eq
  exact tendsto_nhds_unique
    (eval_tendsto_of_bishopConvergesTo Arithmetic hx)
    (eval_tendsto_of_bishopConvergesTo Arithmetic hy)

/-- Every admissible binding's exponential value is the same Bishop real as the
canonical one, pointwise in the input. -/
theorem exp_equiv_canonical
    (B : Round11MachinSourceBinding Arithmetic)
    (x : RegularRatReal) :
    Equiv (B.expB x) (canonicalBinding.expB x) :=
  limit_equiv_of_two_convergences
    (B.expConverges x)
    (canonicalBinding.expConverges x)

theorem sin_equiv_canonical
    (B : Round11MachinSourceBinding Arithmetic)
    (x : RegularRatReal) :
    Equiv (B.sinB x) (canonicalBinding.sinB x) :=
  limit_equiv_of_two_convergences
    (B.sinConverges x)
    (canonicalBinding.sinConverges x)

theorem cos_equiv_canonical
    (B : Round11MachinSourceBinding Arithmetic)
    (x : RegularRatReal) :
    Equiv (B.cosB x) (canonicalBinding.cosB x) :=
  limit_equiv_of_two_convergences
    (B.cosConverges x)
    (canonicalBinding.cosConverges x)

theorem atanOneFifth_equiv_canonical
    (B : Round11MachinSourceBinding Arithmetic) :
    Equiv B.atanOneFifth canonicalBinding.atanOneFifth :=
  limit_equiv_of_two_convergences
    B.atanOneFifthConverges
    canonicalBinding.atanOneFifthConverges

theorem atan239_equiv_canonical
    (B : Round11MachinSourceBinding Arithmetic) :
    Equiv B.atanOneTwoHundredThirtyNinth
      canonicalBinding.atanOneTwoHundredThirtyNinth :=
  limit_equiv_of_two_convergences
    B.atanOneTwoHundredThirtyNinthConverges
    canonicalBinding.atanOneTwoHundredThirtyNinthConverges

structure BindingSetoidAgreement
    (B : Round11MachinSourceBinding Arithmetic) : Prop where
  exp :
    ∀ x, Equiv (B.expB x) (canonicalBinding.expB x)
  sin :
    ∀ x, Equiv (B.sinB x) (canonicalBinding.sinB x)
  cos :
    ∀ x, Equiv (B.cosB x) (canonicalBinding.cosB x)
  atanOneFifth :
    Equiv B.atanOneFifth canonicalBinding.atanOneFifth
  atan239 :
    Equiv B.atanOneTwoHundredThirtyNinth
      canonicalBinding.atanOneTwoHundredThirtyNinth

theorem everyBinding_agrees_setoid
    (B : Round11MachinSourceBinding Arithmetic) :
    BindingSetoidAgreement B where
  exp := exp_equiv_canonical B
  sin := sin_equiv_canonical B
  cos := cos_equiv_canonical B
  atanOneFifth := atanOneFifth_equiv_canonical B
  atan239 := atan239_equiv_canonical B

structure Boundary where
  canonicalBindingInhabited : Bool
  bindingBuiltFromCompletionEquivalence : Bool
  leanToBishopConvergenceCompilerUsed : Bool
  everyAdmissibleBindingSetoidEquivalent : Bool

  generatedAgdaReplayObserved : Bool
  exactHeadLeanKernelReceiptObserved : Bool

def boundary : Boundary where
  canonicalBindingInhabited := true
  bindingBuiltFromCompletionEquivalence := true
  leanToBishopConvergenceCompilerUsed := true
  everyAdmissibleBindingSetoidEquivalent := true

  generatedAgdaReplayObserved := false
  exactHeadLeanKernelReceiptObserved := false

end

end Integration.BishopRound11MachinCanonicalBinding
