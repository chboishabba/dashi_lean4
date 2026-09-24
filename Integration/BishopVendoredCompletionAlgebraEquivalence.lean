import Integration.BishopVendoredCompletionEquivalence
import Integration.BishopVendoredArithmeticConcrete
import Integration.BishopVendoredOrderConvergenceEvaluation

/-!
# Algebra compatibility of the Bishop completion equivalence

The completion equivalence identifies Bishop regular reals modulo the vendored
setoid with Lean Real.  This module proves that the canonical encoder respects
the exact vendored arithmetic operations up to Bishop equivalence.

The source operations are the source-faithful concrete mirror:

* zero/one constant rational sequences;
* pointwise negation;
* 2*n-resampled addition;
* 2*max(Kx,Ky)*n-resampled multiplication.

No pointwise replacement of the source arithmetic is used.
-/

namespace Integration.BishopVendoredCompletionAlgebraEquivalence

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredCompletionEquivalence
open Integration.BishopVendoredArithmeticConcrete
open Integration.BishopVendoredOrderConvergenceEvaluation

noncomputable section

abbrev A : VendoredArithmeticMirror :=
  concreteVendoredArithmeticMirror

theorem encode_zero_equiv :
    Equiv (encode 0) A.zero := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_zero]

theorem encode_one_equiv :
    Equiv (encode 1) A.one := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_one]

theorem encode_neg_equiv (r : ℝ) :
    Equiv (encode (-r)) (A.neg (encode r)) := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_neg, eval_encode]

theorem encode_add_equiv (r s : ℝ) :
    Equiv (encode (r + s)) (A.add (encode r) (encode s)) := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_add, eval_encode, eval_encode]

theorem encode_sub_equiv (r s : ℝ) :
    Equiv (encode (r - s))
      (A.add (encode r) (A.neg (encode s))) := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_add, A.eval_neg, eval_encode, eval_encode]
  ring

theorem encode_mul_equiv (r s : ℝ) :
    Equiv (encode (r * s)) (A.mul (encode r) (encode s)) := by
  apply equiv_of_eval_eq
  rw [eval_encode, A.eval_mul, eval_encode, eval_encode]

/-- Any source representative can be replaced by the canonical encoding of its
value before or after vendored addition. -/
theorem add_encode_eval_equiv
    (x y : RegularRatReal) :
    Equiv
      (A.add x y)
      (encode (eval x + eval y)) := by
  apply equiv_of_eval_eq
  rw [A.eval_add, eval_encode]

/-- Same statement for vendored multiplication. -/
theorem mul_encode_eval_equiv
    (x y : RegularRatReal) :
    Equiv
      (A.mul x y)
      (encode (eval x * eval y)) := by
  apply equiv_of_eval_eq
  rw [A.eval_mul, eval_encode]

theorem neg_encode_eval_equiv
    (x : RegularRatReal) :
    Equiv
      (A.neg x)
      (encode (-eval x)) := by
  apply equiv_of_eval_eq
  rw [A.eval_neg, eval_encode]

/-- Source order is exactly ordinary order under the completion equivalence. -/
theorem bishop_order_iff_real_order
    {x y : RegularRatReal} :
    Le A x y ↔ eval x ≤ eval y :=
  eval_le_iff A

structure Boundary where
  zeroCompatibilityOwned : Bool
  oneCompatibilityOwned : Bool
  negCompatibilityOwned : Bool
  addCompatibilityOwned : Bool
  subCompatibilityOwned : Bool
  mulCompatibilityOwned : Bool
  arbitraryRepresentativeCompatibilityOwned : Bool
  bishopOrderExactlyReflected : Bool

def boundary : Boundary where
  zeroCompatibilityOwned := true
  oneCompatibilityOwned := true
  negCompatibilityOwned := true
  addCompatibilityOwned := true
  subCompatibilityOwned := true
  mulCompatibilityOwned := true
  arbitraryRepresentativeCompatibilityOwned := true
  bishopOrderExactlyReflected := true

end

end Integration.BishopVendoredCompletionAlgebraEquivalence
