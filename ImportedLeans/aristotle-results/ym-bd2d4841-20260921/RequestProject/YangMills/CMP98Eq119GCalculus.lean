/-
# Bałaban's Lie-calculus function `g` (CMP 98, preliminaries to Eq. (119))

Bałaban's averaging papers set

    g(z) = (e^{-z} − 1)/(−z) = (1 − e^{-z})/z ,

use `g(−i ad Y)` as the trivialisation appearing in the one-step averaging
derivative Eq. (119), and immediately afterwards use the identity

    g^{-1}(−i ad Y_x) e^{i ad Y_x} = g^{-1}(i ad Y_x) .

This file proves that calculus, in a complete normed real algebra `𝔸`
(so that it applies to `ad`-operators on any finite-dimensional Lie algebra,
and to matrices), with `g` defined by its entire power series so that no
removable singularity has to be argued about:

    balabanG x = Σ_{n≥0} (−1)ⁿ/(n+1)! · xⁿ .

Proved here:

* `balabanG_mul_self`, `self_mul_balabanG` — `x·g(x) = g(x)·x = 1 − e^{−x}`,
  i.e. the defining relation, with the singularity at `0` resolved
  (`balabanG_zero : g(0) = 1`).
* `balabanG_neg` — **the source identity** `g(−x) = e^{x} g(x)`.  This is the
  exact statement that the two opposite trivialisations differ by the adjoint
  factor, and it is proved by the Cauchy product of the two entire series
  together with the alternating binomial identity
  `Σ_{k≤n} (−1)^{n−k} C(n+1,k) = 1`, not assumed.
* `dexpPlus_eq_exp_mul_dexpMinus` — the same statement in the left/right
  trivialisation notation: `dexp₊ = Ad_{exp} ∘ dexp₋`.
* `inverse_transport` — the purely algebraic inverse-uniqueness step: if
  `G₊ = E·G₋` then any right inverse of `G₋` and left inverse of `G₊` satisfy
  `J₊·E = J₋`.  Instantiated at the `g`-calculus in `balabanJ_transport`, this
  is Bałaban's displayed transformation `g^{-1}(−z)e^{z} = g^{-1}(z)`.
* `norm_balabanG_sub_one_le` and `isUnit_balabanG_of_norm_lt_log_two` — a
  genuine small-field criterion: `‖g(x) − 1‖ ≤ e^{‖x‖} − 1`, so `g(x)` is
  invertible as soon as `‖x‖ < log 2`.  The inverses `J₋`, `J₊` used above are
  therefore *produced* in the small-field regime rather than postulated.
-/
import Mathlib

namespace YangMills.CMP98Eq119

open Finset

/-! ## 1. Two scalar identities -/

/-- `Σ_{k ≤ n} (−1)^{n−k} C(n+1,k) = 1`. -/
theorem alt_choose_sum (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * ((n + 1).choose k) = 1 := by
  have h0 : (∑ m ∈ range (n + 2), (-1 : ℝ) ^ m * ((n + 1).choose m)) = 0 := by
    have h := Int.alternating_sum_range_choose (n := n + 1)
    simp only [Nat.succ_ne_zero, if_false] at h
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    simpa using h'
  rw [Finset.sum_range_succ] at h0
  have hS : (∑ m ∈ range (n + 1), (-1 : ℝ) ^ m * ((n + 1).choose m)) = (-1) ^ n := by
    have hp : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    simp only [Nat.choose_self, Nat.cast_one, mul_one, hp] at h0
    linarith
  have hterm : ∀ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * ((n + 1).choose k)
      = (-1) ^ n * ((-1) ^ k * ((n + 1).choose k)) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsign : (-1 : ℝ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
      have h1 : (-1 : ℝ) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hk']
      have h2 : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (-1 : ℝ) ^ (n - k) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [h2]; ring
        _ = (-1) ^ n * (-1) ^ k := by rw [← mul_assoc, h1]
    rw [hsign]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hS, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The coefficient of `x ^ n` in the power series of `g`. -/
noncomputable def gCoeff (n : ℕ) : ℝ := (-1) ^ n / Nat.factorial (n + 1)

@[simp] theorem gCoeff_zero : gCoeff 0 = 1 := by norm_num [gCoeff]

/-- The Cauchy-product coefficient identity behind `g(−x) = e^x g(x)`:
`Σ_{k ≤ n} 1/k! · (−1)^{n−k}/(n−k+1)! = 1/(n+1)!`. -/
theorem coeff_conv (n : ℕ) :
    ∑ k ∈ range (n + 1), ((Nat.factorial k : ℝ))⁻¹ * gCoeff (n - k)
      = (Nat.factorial (n + 1) : ℝ)⁻¹ := by
  have hrewrite : ∑ k ∈ range (n + 1), ((Nat.factorial k : ℝ))⁻¹ * gCoeff (n - k)
      = (Nat.factorial (n + 1) : ℝ)⁻¹
        * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * ((n + 1).choose k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsub : n - k + 1 = n + 1 - k := by omega
    have hfac : ((n + 1).choose k) * Nat.factorial k * Nat.factorial (n + 1 - k)
        = Nat.factorial (n + 1) := Nat.choose_mul_factorial_mul_factorial (by omega)
    have hfacR : (((n + 1).choose k : ℝ)) * (Nat.factorial k : ℝ)
        * (Nat.factorial (n + 1 - k) : ℝ) = (Nat.factorial (n + 1) : ℝ) := by
      exact_mod_cast hfac
    have hk0 : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnk0 : (Nat.factorial (n + 1 - k) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn0 : (Nat.factorial (n + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [gCoeff, hsub]
    field_simp
    nlinarith [hfacR]
  rw [hrewrite, alt_choose_sum, mul_one]

/-! ## 2. The operator `g(x)` in a complete normed algebra -/

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- `g(x) = Σ_{n≥0} (−1)ⁿ/(n+1)! · xⁿ`, an entire function of `x`. -/
noncomputable def balabanG (x : A) : A := ∑' n : ℕ, gCoeff n • x ^ n

omit [CompleteSpace A] [NormOneClass A] in
theorem neg_pow_smul (x : A) (m : ℕ) : (-x) ^ m = ((-1 : ℝ) ^ m) • x ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, pow_succ, pow_succ]; simp [mul_neg]

omit [CompleteSpace A] in
theorem summable_norm_gTerms (x : A) : Summable fun n : ℕ => ‖gCoeff n • x ^ n‖ := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (Real.summable_pow_div_factorial ‖x‖)
  intro n
  rw [norm_smul]
  have h1 : ‖x ^ n‖ ≤ ‖x‖ ^ n := norm_pow_le _ _
  have h2 : ‖gCoeff n‖ ≤ (Nat.factorial n : ℝ)⁻¹ := by
    rw [gCoeff, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.factorial (n + 1) : ℝ)),
      div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have hle : Nat.factorial n ≤ Nat.factorial (n + 1) := Nat.factorial_le (by omega)
    exact_mod_cast by simpa using hle
  calc ‖gCoeff n‖ * ‖x ^ n‖ ≤ (Nat.factorial n : ℝ)⁻¹ * ‖x‖ ^ n :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = ‖x‖ ^ n / (Nat.factorial n : ℝ) := by ring

theorem summable_gTerms (x : A) : Summable fun n : ℕ => gCoeff n • x ^ n :=
  (summable_norm_gTerms x).of_norm

@[simp] theorem balabanG_zero : balabanG (0 : A) = 1 := by
  rw [balabanG, (summable_gTerms (0 : A)).tsum_eq_zero_add]
  simp

/-- `x · g(x) = 1 − e^{−x}`: the defining relation of Bałaban's `g`. -/
theorem self_mul_balabanG (x : A) : x * balabanG x = 1 - NormedSpace.exp (-x) := by
  have hs := summable_gTerms x
  have hexp : NormedSpace.exp (-x) = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • (-x) ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum : Summable fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹ • (-x) ^ n :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (-x)).of_norm
  rw [hexp, hsum.tsum_eq_zero_add, balabanG, ← hs.tsum_mul_left]
  have hterm : ∀ n : ℕ,
      ((Nat.factorial (n + 1) : ℝ))⁻¹ • (-x) ^ (n + 1) = -(gCoeff n • x ^ (n + 1)) := by
    intro n
    rw [neg_pow_smul, smul_smul, gCoeff, ← neg_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hleft : ∀ n : ℕ, x * (gCoeff n • x ^ n) = gCoeff n • x ^ (n + 1) := by
    intro n; rw [mul_smul_comm, pow_succ']
  simp only [hterm, hleft, tsum_neg, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul]
  abel

/-- `g(x) · x = 1 − e^{−x}`. -/
theorem balabanG_mul_self (x : A) : balabanG x * x = 1 - NormedSpace.exp (-x) := by
  have hs := summable_gTerms x
  have h1 : balabanG x * x = x * balabanG x := by
    rw [balabanG, ← hs.tsum_mul_left, ← hs.tsum_mul_right]
    refine tsum_congr (fun n => ?_)
    rw [smul_mul_assoc, mul_smul_comm, ← pow_succ, ← pow_succ']
  rw [h1, self_mul_balabanG]

/-- **The source identity** `g(−x) = e^{x} g(x)`. -/
theorem balabanG_neg (x : A) : balabanG (-x) = NormedSpace.exp x * balabanG x := by
  have hf : Summable fun n : ℕ => ‖((Nat.factorial n : ℝ))⁻¹ • x ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have hg := summable_norm_gTerms x
  have hexp : NormedSpace.exp x = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  simp only [balabanG]
  rw [hexp, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  refine tsum_congr (fun n => ?_)
  have hinner : ∀ k ∈ range (n + 1),
      (((Nat.factorial k : ℝ))⁻¹ • x ^ k) * (gCoeff (n - k) • x ^ (n - k))
        = (((Nat.factorial k : ℝ))⁻¹ * gCoeff (n - k)) • x ^ n := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_cancel' hk']
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_smul, coeff_conv, neg_pow_smul, smul_smul,
    gCoeff]
  congr 1
  have hsq : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hne : (Nat.factorial (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  nlinarith [hsq]

/-! ## 3. Left/right trivialisations and the inverse transport -/

/-- The trivialisation `dexp₋(x) = g(x)`. -/
noncomputable def dexpMinus (x : A) : A := balabanG x

/-- The opposite trivialisation `dexp₊(x) = g(−x)`. -/
noncomputable def dexpPlus (x : A) : A := balabanG (-x)

/-- `dexp₊ = Ad_{exp} ∘ dexp₋`, the left/right trivialisation relation. -/
theorem dexpPlus_eq_exp_mul_dexpMinus (x : A) :
    dexpPlus x = NormedSpace.exp x * dexpMinus x := balabanG_neg x

/-- Inverse uniqueness: if `G₊ = E · G₋`, any right inverse `J₋` of `G₋` and left
inverse `J₊` of `G₊` satisfy `J₊ · E = J₋`.  No further data is needed. -/
theorem inverse_transport {M : Type*} [Monoid M] {E Gm Gp Jm Jp : M}
    (hGp : Gp = E * Gm) (hm : Gm * Jm = 1) (hp : Jp * Gp = 1) : Jp * E = Jm := by
  calc Jp * E = Jp * E * (Gm * Jm) := by rw [hm, mul_one]
    _ = Jp * (E * Gm) * Jm := by simp [mul_assoc]
    _ = Jp * Gp * Jm := by rw [hGp]
    _ = Jm := by rw [hp, one_mul]

/-- Bałaban's displayed transformation `g^{-1}(−x) e^{x} = g^{-1}(x)`, derived
from `balabanG_neg` and inverse uniqueness alone. -/
theorem balabanJ_transport {x : A} {Jm Jp : A}
    (hm : balabanG x * Jm = 1) (hp : Jp * balabanG (-x) = 1) :
    Jp * NormedSpace.exp x = Jm :=
  inverse_transport (balabanG_neg x) hm hp

/-! ## 4. Small field: the trivialisation really is invertible -/

theorem norm_balabanG_sub_one_le (x : A) :
    ‖balabanG x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hs := summable_gTerms x
  have hshift : balabanG x - 1 = ∑' n : ℕ, gCoeff (n + 1) • x ^ (n + 1) := by
    rw [balabanG, hs.tsum_eq_zero_add]
    simp
  have hnormsum : Summable fun n : ℕ => ‖gCoeff (n + 1) • x ^ (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr (summable_norm_gTerms x)
  have hexpsum : Summable fun n : ℕ => ‖x‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
    (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖x‖)
  have hbound : ∀ n : ℕ, ‖gCoeff (n + 1) • x ^ (n + 1)‖
      ≤ ‖x‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    intro n
    rw [norm_smul]
    have h1 : ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_pow_le _ _
    have h2 : ‖gCoeff (n + 1)‖ ≤ (Nat.factorial (n + 1) : ℝ)⁻¹ := by
      rw [gCoeff, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.factorial (n + 1 + 1) : ℝ)),
        div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      have hle : Nat.factorial (n + 1) ≤ Nat.factorial (n + 1 + 1) := Nat.factorial_le (by omega)
      exact_mod_cast by simpa using hle
    calc ‖gCoeff (n + 1)‖ * ‖x ^ (n + 1)‖
        ≤ (Nat.factorial (n + 1) : ℝ)⁻¹ * ‖x‖ ^ (n + 1) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = ‖x‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by ring
  have hexp : Real.exp ‖x‖ - 1 = ∑' n : ℕ, ‖x‖ ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    have hR : Real.exp ‖x‖ = ∑' n : ℕ, ‖x‖ ^ n / (Nat.factorial n : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hR, (Real.summable_pow_div_factorial ‖x‖).tsum_eq_zero_add]
    simp
  rw [hshift, hexp]
  exact (norm_tsum_le_tsum_norm hnormsum).trans
    (Summable.tsum_le_tsum hbound hnormsum hexpsum)

/-- Small field ⇒ the trivialisation is invertible.  `log 2 ≈ 0.693`. -/
theorem isUnit_balabanG_of_norm_lt_log_two {x : A} (hx : ‖x‖ < Real.log 2) :
    IsUnit (balabanG x) := by
  have hlt : ‖1 - balabanG x‖ < 1 := by
    have h1 : ‖1 - balabanG x‖ = ‖balabanG x - 1‖ := norm_sub_rev _ _
    have h2 : Real.exp ‖x‖ < 2 := by
      have := Real.exp_lt_exp.mpr hx
      rwa [Real.exp_log (by norm_num)] at this
    calc ‖1 - balabanG x‖ = ‖balabanG x - 1‖ := h1
      _ ≤ Real.exp ‖x‖ - 1 := norm_balabanG_sub_one_le x
      _ < 1 := by linarith
  have hunit : IsUnit (1 - (1 - balabanG x)) := (Units.oneSub _ hlt).isUnit
  simpa using hunit

end YangMills.CMP98Eq119
