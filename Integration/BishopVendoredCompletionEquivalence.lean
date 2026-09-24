import Integration.BishopVendoredRealEvaluation
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic

/-!
# Completion equivalence between vendored Bishop regular reals and Lean Real

The vendored Bishop carrier is a presentation by regular rational sequences
modulo the relation

  |x_n - y_n| <= 2/n.

The evaluator already proves

  eval x = eval y  <->  Equiv x y.

This module constructs the converse direction at the level of representatives:
for every Lean real r choose rational approximants q_n with

  |q_n - r| < 1/(2n)    (n != 0),

and use them as a Bishop regular real.

Consequences:

  eval (encode r) = r
  encode (eval x) ~ x.

Thus Lean Real and the vendored Bishop completion are the same completion up to
Bishop's own setoid equality.  No raw representative identity is claimed.
-/

namespace Integration.BishopVendoredCompletionEquivalence

open Filter
open scoped Topology

open Integration.BishopVendoredRealEvaluation

noncomputable section

private def radius (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ))

private theorem radius_pos {n : ℕ} (hn : n ≠ 0) :
    0 < radius n := by
  unfold radius
  positivity

private theorem exists_rat_approx
    (r : ℝ) (n : ℕ) (hn : n ≠ 0) :
    ∃ q : ℚ, |((q : ℝ) - r)| < radius n := by
  have hr : 0 < radius n := radius_pos hn
  obtain ⟨q, hql, hqu⟩ :
      ∃ q : ℚ, r - radius n < (q : ℝ) ∧ (q : ℝ) < r + radius n :=
    exists_rat_btwn (by linarith : r - radius n < r + radius n)
  refine ⟨q, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- Canonical chosen rational approximation.  Index zero is intentionally
irrelevant to the Bishop setoid/regularity contract and is fixed to zero. -/
def approxRat (r : ℝ) : ℕ → ℚ
  | 0 => 0
  | n + 1 =>
      Classical.choose (exists_rat_approx r (n + 1) (by omega))

theorem approxRat_spec
    (r : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |((approxRat r n : ℝ) - r)| < radius n := by
  cases n with
  | zero => contradiction
  | succ n =>
      exact Classical.choose_spec
        (exists_rat_approx r (n + 1) (by omega))

/-- The chosen rational approximation family is Bishop-regular. -/
def encode (r : ℝ) : RegularRatReal where
  seq := approxRat r
  regular m n hm hn := by
    have hm' := (approxRat_spec r m hm).le
    have hn' := (approxRat_spec r n hn).le
    have htri :
        |((approxRat r m : ℝ) - (approxRat r n : ℝ))|
          ≤ |((approxRat r m : ℝ) - r)| +
            |(r - (approxRat r n : ℝ))| := by
      exact abs_sub_le _ _ _
    calc
      |((approxRat r m : ℝ) - (approxRat r n : ℝ))|
          ≤ |((approxRat r m : ℝ) - r)| +
            |(r - (approxRat r n : ℝ))| := htri
      _ ≤ radius m + radius n := by
            gcongr
            simpa [abs_sub_comm] using hn'
      _ ≤ 1 / (m : ℝ) + 1 / (n : ℝ) := by
            unfold radius
            have hmpos : (0 : ℝ) < m := by
              exact_mod_cast Nat.pos_of_ne_zero hm
            have hnpos : (0 : ℝ) < n := by
              exact_mod_cast Nat.pos_of_ne_zero hn
            have hmhalf :
                1 / (2 * (m : ℝ)) ≤ 1 / (m : ℝ) := by
              apply one_div_le_one_div_of_le hmpos
              nlinarith
            have hnhalf :
                1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
              apply one_div_le_one_div_of_le hnpos
              nlinarith
            exact add_le_add hmhalf hnhalf

private theorem encoded_shift_dist_le
    (r : ℝ) (n : ℕ) :
    dist (shifted (encode r) n) r ≤
      1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  rw [Real.dist_eq]
  have h := (approxRat_spec r (n + 1) (by omega)).le
  simpa [shifted, encode, radius] using h

private theorem half_inv_succ_tendsto_zero :
    Tendsto
      (fun n : ℕ => 1 / (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have h :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  have hc :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hc.mul h

/-- The encoded representative converges to the real it encodes. -/
theorem tendsto_shifted_encode (r : ℝ) :
    Tendsto (shifted (encode r)) atTop (𝓝 r) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) encoded_shift_dist_le
    half_inv_succ_tendsto_zero

/-- Evaluation is a left inverse of the canonical encoding. -/
theorem eval_encode (r : ℝ) :
    eval (encode r) = r :=
  tendsto_nhds_unique (tendsto_eval (encode r)) (tendsto_shifted_encode r)

/-- Every Bishop representative is equivalent to the encoding of its evaluated
classical real. -/
theorem encode_eval_equiv
    (x : RegularRatReal) :
    Equiv (encode (eval x)) x := by
  intro n hn
  have henc := (approxRat_spec (eval x) n hn).le
  have hx := sample_dist_eval_le x n hn
  have htri :
      |((encode (eval x)).seq n : ℝ) - (x.seq n : ℝ)|
        ≤ |((encode (eval x)).seq n : ℝ) - eval x| +
          |eval x - (x.seq n : ℝ)| := by
    exact abs_sub_le _ _ _
  calc
    |((encode (eval x)).seq n : ℝ) - (x.seq n : ℝ)|
        ≤ |((encode (eval x)).seq n : ℝ) - eval x| +
          |eval x - (x.seq n : ℝ)| := htri
    _ ≤ radius n + 1 / (n : ℝ) := by
          gcongr
          · simpa [encode] using henc
          · simpa [abs_sub_comm] using hx
    _ ≤ 2 / (n : ℝ) := by
          unfold radius
          have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          field_simp
          nlinarith

/-- The opposite orientation is available by the exact evaluator/setoid
characterisation, without separately proving symmetry of the raw relation. -/
theorem equiv_encode_eval
    (x : RegularRatReal) :
    Equiv x (encode (eval x)) := by
  apply equiv_of_eval_eq
  rw [eval_encode]

/-- Surjectivity of the evaluator onto ordinary Lean Real. -/
theorem eval_surjective :
    Function.Surjective eval :=
  fun r => ⟨encode r, eval_encode r⟩

/-- The exact Bishop equivalence relation is an actual Lean Setoid. -/
def bishopSetoid : Setoid RegularRatReal where
  r := Equiv
  iseqv := {
    refl := fun x => equiv_of_eval_eq rfl
    symm := fun h => equiv_of_eval_eq (eval_respects_equiv h).symm
    trans := fun hxy hyz =>
      equiv_of_eval_eq
        ((eval_respects_equiv hxy).trans (eval_respects_equiv hyz))
  }

/-- Evaluation descends to the Bishop quotient. -/
def evalQuot : Quotient bishopSetoid → ℝ :=
  Quotient.lift eval (fun _ _ h => eval_respects_equiv h)

/-- Canonical inclusion of Lean Real into the Bishop quotient. -/
def encodeQuot (r : ℝ) : Quotient bishopSetoid :=
  Quotient.mk bishopSetoid (encode r)

@[simp]
theorem evalQuot_encodeQuot (r : ℝ) :
    evalQuot (encodeQuot r) = r :=
  eval_encode r

@[simp]
theorem encodeQuot_evalQuot
    (x : Quotient bishopSetoid) :
    encodeQuot (evalQuot x) = x := by
  refine Quotient.inductionOn x ?_
  intro representative
  apply Quotient.sound
  exact encode_eval_equiv representative

/-- The vendored Bishop completion quotient is equivalent to ordinary Lean Real.

This is an equivalence of the completed carriers.  It does not identify raw
regular-sequence representatives definitionally. -/
def bishopCompletionEquivReal :
    Quotient bishopSetoid ≃ ℝ where
  toFun := evalQuot
  invFun := encodeQuot
  left_inv := encodeQuot_evalQuot
  right_inv := evalQuot_encodeQuot

/-- Setoid-faithful completion equivalence receipt. -/
structure CompletionEquivalenceBoundary where
  rationalApproximationEncodingOwned : Bool
  encodingRegularityOwned : Bool
  evalEncodeIdentityOwned : Bool
  encodeEvalBishopEquivalenceOwned : Bool
  evaluatorSurjective : Bool
  evaluatorFaithfulOnSetoidClasses : Bool
  quotientSetoidConstructed : Bool
  quotientEquivalentToLeanReal : Bool
  rawRepresentativeIdentityClaimed : Bool

def completionEquivalenceBoundary : CompletionEquivalenceBoundary where
  rationalApproximationEncodingOwned := true
  encodingRegularityOwned := true
  evalEncodeIdentityOwned := true
  encodeEvalBishopEquivalenceOwned := true
  evaluatorSurjective := true
  evaluatorFaithfulOnSetoidClasses := true
  quotientSetoidConstructed := true
  quotientEquivalentToLeanReal := true
  rawRepresentativeIdentityClaimed := false

end

end Integration.BishopVendoredCompletionEquivalence
