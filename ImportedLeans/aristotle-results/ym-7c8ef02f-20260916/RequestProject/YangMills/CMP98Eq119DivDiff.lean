/-
# The divided-difference identity behind Bałaban's `g`

Bałaban writes the one-step averaging derivative with the operators
`g(±i ad Y)`, which are the *left and right trivialisations of the differential
of the exponential map*.  Naming an operator `g` does not make it that
differential, so this file proves the algebraic half of the identification and
`CMP98Eq119Dexp` proves the analytic half.

The algebraic half is the classical divided-difference identity

    Σ_{i+j=n} u^i v^j / (n+1)!   summed over n   =   e^u · g(u − v)

for two **commuting** elements of a Banach algebra (the formal statement being
`exp_mul_balabanG_eq_divDiff`).  Its whole content is the finite polynomial
identity

    Σ_{m≤n} C(n+1, m+1) · u^{n−m} (v−u)^m  =  Σ_{i+j=n} u^i v^j ,

`dividedDiff_finset`, proved by induction using Pascal's rule and the binomial
theorem for the commuting pair `(v − u, u)`; the passage to the series is then
a Cauchy product.

Applied to the commuting pair `u = L_Y` (left multiplication) and `v = R_Y`
(right multiplication), whose difference is exactly `ad Y`, it yields

    Σ_n (n+1)!^{-1} Σ_{i+j=n} Y^i Z Y^j  =  e^{Y} · g(ad Y) Z ,

which is `dexpSeries_eq`.  The left-hand side is the coefficient of the linear
term of `exp (Y + tZ)`, so this is precisely the statement that Bałaban's `g`
is the trivialised differential of `exp`; the analytic step identifying the
left-hand side with the derivative is `CMP98Eq119Dexp`.
-/
import RequestProject.YangMills.CMP98Eq119Assembly

namespace YangMills.CMP98Eq119

open Finset

/-! ## 1. The finite polynomial identity -/

/-- For commuting `u, v` in any ring,
`Σ_{m ≤ n} C(n+1, m+1) · u^{n−m}(v−u)^m = Σ_{i+j=n} u^i v^j`.
Proved by induction: Pascal's rule splits the left side into `u ·` the previous
case plus the binomial expansion of `((v − u) + u)^{n+1} = v^{n+1}`. -/
theorem dividedDiff_finset {B : Type*} [Ring B] {u v : B} (h : Commute u v) (n : ℕ) :
    ∑ m ∈ range (n + 1), ((n + 1).choose (m + 1)) • (u ^ (n - m) * (v - u) ^ m)
      = ∑ i ∈ range (n + 1), u ^ i * v ^ (n - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcomm : Commute (v - u) u := h.symm.sub_left (Commute.refl u)
      have hbinom : ∑ m ∈ range (n + 2), ((n + 1).choose m) • (u ^ (n + 1 - m) * (v - u) ^ m)
          = v ^ (n + 1) := by
        have hb := hcomm.add_pow (n + 1)
        rw [sub_add_cancel] at hb
        rw [hb]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [nsmul_eq_mul, (hcomm.symm.pow_pow (n + 1 - m) m).eq,
          (Nat.cast_commute ((n + 1).choose m) ((v - u) ^ m * u ^ (n + 1 - m))).eq]
      have hsplit : ∀ m ∈ range (n + 2),
          ((n + 2).choose (m + 1)) • (u ^ (n + 1 - m) * (v - u) ^ m)
            = ((n + 1).choose m) • (u ^ (n + 1 - m) * (v - u) ^ m)
              + ((n + 1).choose (m + 1)) • (u ^ (n + 1 - m) * (v - u) ^ m) := by
        intro m _
        rw [Nat.choose_succ_succ (n + 1) m, add_smul]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hbinom]
      have htail : ∑ m ∈ range (n + 2), ((n + 1).choose (m + 1)) • (u ^ (n + 1 - m) * (v - u) ^ m)
          = u * ∑ i ∈ range (n + 1), u ^ i * v ^ (n - i) := by
        rw [Finset.sum_range_succ]
        have hzero : ((n + 1).choose (n + 2)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hzero, zero_smul, add_zero, ← ih, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hm' : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
        have hpow : u ^ (n + 1 - m) = u * u ^ (n - m) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hpow, mul_smul_comm, mul_assoc]
      rw [htail, Finset.mul_sum,
        Finset.sum_range_succ' (fun i => u ^ i * v ^ (n + 1 - i)) (n + 1)]
      simp only [pow_zero, one_mul, Nat.sub_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega

/-! ## 2. The scalar coefficient identity -/

/-- `(n+1)!^{-1} · C(n+1, m+1) = ((n−m)! (m+1)!)^{-1}` for `m ≤ n`: the
normalisation that turns the Cauchy product of `e^u` and `g(u−v)` into the
divided difference. -/
theorem divDiff_coeff {n m : ℕ} (hm : m ≤ n) :
    ((Nat.factorial (n - m) : ℝ))⁻¹ * ((Nat.factorial (m + 1) : ℝ))⁻¹
      = ((Nat.factorial (n + 1) : ℝ))⁻¹ * ((n + 1).choose (m + 1)) := by
  have hfac : ((n + 1).choose (m + 1)) * Nat.factorial (m + 1) * Nat.factorial (n - m)
      = Nat.factorial (n + 1) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hm)
    have hsub : n + 1 - (m + 1) = n - m := by omega
    rwa [hsub] at h
  have hfacR : (((n + 1).choose (m + 1) : ℝ)) * (Nat.factorial (m + 1) : ℝ)
      * (Nat.factorial (n - m) : ℝ) = (Nat.factorial (n + 1) : ℝ) := by exact_mod_cast hfac
  have h1 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (Nat.factorial (n - m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (Nat.factorial (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  nlinarith [hfacR]

/-! ## 3. The divided-difference series -/

section Series

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [NormOneClass B]

/-- **The divided-difference identity.**  For commuting `u, v`,
`e^u · g(u − v) = Σ_n (n+1)!^{-1} Σ_{i+j=n} u^i v^j`. -/
theorem exp_mul_balabanG_eq_divDiff {u v : B} (h : Commute u v) :
    NormedSpace.exp u * balabanG (u - v)
      = ∑' n : ℕ, ((Nat.factorial (n + 1) : ℝ))⁻¹
          • (∑ i ∈ range (n + 1), u ^ i * v ^ (n - i)) := by
  have hf : Summable fun n : ℕ => ‖((Nat.factorial n : ℝ))⁻¹ • u ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) u
  have hg := summable_norm_gTerms (u - v)
  have hexp : NormedSpace.exp u = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • u ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  simp only [balabanG]
  rw [hexp, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  refine tsum_congr (fun n => ?_)
  -- the `n`-th Cauchy term, reindexed by the exponent `m` of `(u − v)`
  have hterm : ∀ k ∈ range (n + 1),
      (((Nat.factorial k : ℝ))⁻¹ • u ^ k) * (gCoeff (n - k) • (u - v) ^ (n - k))
        = ((Nat.factorial (n + 1) : ℝ))⁻¹
            • (((n + 1).choose (n - k + 1)) • (u ^ k * (v - u) ^ (n - k))) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsub : n - (n - k) = k := by omega
    have hle : n - k ≤ n := by omega
    have hsign : (v - u) ^ (n - k) = ((-1 : ℝ) ^ (n - k)) • (u - v) ^ (n - k) := by
      rw [← neg_pow_smul]
      congr 1
      abel
    have hstep : ((Nat.factorial k : ℝ))⁻¹ * gCoeff (n - k)
        = ((Nat.factorial (n + 1) : ℝ))⁻¹ * (((n + 1).choose (n - k + 1) : ℝ))
            * (-1 : ℝ) ^ (n - k) := by
      have hc := divDiff_coeff (n := n) (m := n - k) hle
      rw [hsub] at hc
      have hne : ((-1 : ℝ) ^ (n - k)) * ((-1 : ℝ) ^ (n - k)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [gCoeff]
      field_simp at hc ⊢
      nlinarith [hc, hne]
    rw [smul_mul_smul_comm, hsign, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      smul_smul]
    congr 1
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]
  congr 1
  -- reflect `k ↦ n − k` to match `dividedDiff_finset`
  have hrefl : ∑ k ∈ range (n + 1), ((n + 1).choose (n - k + 1)) • (u ^ k * (v - u) ^ (n - k))
      = ∑ m ∈ range (n + 1), ((n + 1).choose (m + 1)) • (u ^ (n - m) * (v - u) ^ m) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have h1 : n - (n - m) = m := by omega
    have h2 : n + 1 - 1 - m = n - m := by omega
    rw [h2, h1]
  rw [hrefl, dividedDiff_finset h]

end Series

/-! ## 4. `g(ad Y)` is the trivialised divided difference -/

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A]

omit [CompleteSpace A] [Nontrivial A] in
theorem lmulA_pow (Y : A) (i : ℕ) : (lmulA Y : A →L[ℝ] A) ^ i = lmulA (Y ^ i) := by
  rw [map_pow]

omit [CompleteSpace A] [Nontrivial A] in
theorem rmulA_pow (Y : A) (j : ℕ) :
    (rmulA (MulOpposite.op Y) : A →L[ℝ] A) ^ j = rmulA (MulOpposite.op (Y ^ j)) := by
  rw [← map_pow, ← MulOpposite.op_pow]

omit [CompleteSpace A] [Nontrivial A] in
theorem lmul_rmul_apply (Y Z : A) (i j : ℕ) :
    ((lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ j) Z = Y ^ i * Z * Y ^ j := by
  rw [lmulA_pow, rmulA_pow, ContinuousLinearMap.mul_apply, rmulA_apply, lmulA_apply,
    MulOpposite.unop_op, mul_assoc]

/-- The `B`-valued divided-difference series for the multiplication pair, whose
value at `Z` is the linear term of `exp (Y + tZ)`. -/
noncomputable def divDiffOp (Y : A) : ℕ → (A →L[ℝ] A) := fun n =>
  ((Nat.factorial (n + 1) : ℝ))⁻¹
    • (∑ i ∈ range (n + 1),
        (lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i))

omit [CompleteSpace A] in
/-- The scalar-valued series that dominates `divDiffOp`. -/
theorem norm_divDiffOp_le (Y : A) (n : ℕ) :
    ‖divDiffOp Y n‖ ≤ ‖Y‖ ^ n / (Nat.factorial n : ℝ) := by
  have hL : ‖(lmulA Y : A →L[ℝ] A)‖ ≤ ‖Y‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => norm_mul_le _ _)
  have hR : ‖(rmulA (MulOpposite.op Y) : A →L[ℝ] A)‖ ≤ ‖Y‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => by
      calc ‖z * Y‖ ≤ ‖z‖ * ‖Y‖ := norm_mul_le _ _
        _ = ‖Y‖ * ‖z‖ := by ring)
  have hterm : ∀ i ∈ range (n + 1),
      ‖(lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)‖ ≤ ‖Y‖ ^ n := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    calc ‖(lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)‖
        ≤ ‖(lmulA Y : A →L[ℝ] A) ^ i‖ * ‖(rmulA (MulOpposite.op Y) : A →L[ℝ] A) ^ (n - i)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(lmulA Y : A →L[ℝ] A)‖ ^ i * ‖(rmulA (MulOpposite.op Y) : A →L[ℝ] A)‖ ^ (n - i) :=
          mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ ‖Y‖ ^ i * ‖Y‖ ^ (n - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hL i)
            (pow_le_pow_left₀ (norm_nonneg _) hR _) (by positivity) (by positivity)
      _ = ‖Y‖ ^ n := by rw [← pow_add]; congr 1; omega
  have hsum : ‖∑ i ∈ range (n + 1),
      (lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)‖
      ≤ (n + 1) * ‖Y‖ ^ n := by
    calc ‖∑ i ∈ range (n + 1),
          (lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)‖
        ≤ ∑ i ∈ range (n + 1), ‖Y‖ ^ n := norm_sum_le_of_le _ hterm
      _ = (n + 1) * ‖Y‖ ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hfac : (Nat.factorial (n + 1) : ℝ) = (n + 1) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpos : (0 : ℝ) < (n + 1) := by positivity
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [divDiffOp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hfac]
  rw [div_eq_inv_mul]
  calc ((n + 1) * (Nat.factorial n : ℝ))⁻¹ * ‖∑ i ∈ range (n + 1),
        (lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)‖
      ≤ ((n + 1) * (Nat.factorial n : ℝ))⁻¹ * ((n + 1) * ‖Y‖ ^ n) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((Nat.factorial n : ℝ))⁻¹ * ‖Y‖ ^ n := by
        field_simp

omit [CompleteSpace A] in
theorem summable_norm_divDiffOp (Y : A) : Summable fun n => ‖divDiffOp Y n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_divDiffOp_le Y)
    (Real.summable_pow_div_factorial ‖Y‖)

/-- **`g(ad Y)` is the trivialised divided difference.**  The series whose `n`-th
term is `(n+1)!^{-1} Σ_{i+j=n} Y^i Z Y^j` — the linear term of `exp (Y + tZ)` —
equals `e^{Y} · g(ad Y) Z`. -/
theorem dexpSeries_eq (Y Z : A) :
    ∑' n : ℕ, ((Nat.factorial (n + 1) : ℝ))⁻¹
        • (∑ i ∈ range (n + 1), Y ^ i * Z * Y ^ (n - i))
      = NormedSpace.exp Y * balabanG (adOp Y) Z := by
  have hcomm : Commute (lmulA Y : A →L[ℝ] A) (rmulA (MulOpposite.op Y)) :=
    commute_lmulA_rmulA Y
  have hop := exp_mul_balabanG_eq_divDiff hcomm
  have hsub : (lmulA Y : A →L[ℝ] A) - rmulA (MulOpposite.op Y) = adOp Y := rfl
  rw [hsub] at hop
  have heval := congrArg (fun T : A →L[ℝ] A => T Z) hop
  simp only at heval
  rw [ContinuousLinearMap.mul_apply, ← lmulA_exp, lmulA_apply] at heval
  have hsummable : Summable (divDiffOp Y) := (summable_norm_divDiffOp Y).of_norm
  have happ : (∑' n : ℕ, divDiffOp Y n) Z = ∑' n : ℕ, (divDiffOp Y n) Z :=
    ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℝ A Z) hsummable
  rw [heval, show (∑' n : ℕ, ((Nat.factorial (n + 1) : ℝ))⁻¹
      • (∑ i ∈ range (n + 1),
          (lmulA Y : A →L[ℝ] A) ^ i * (rmulA (MulOpposite.op Y)) ^ (n - i)))
      = ∑' n : ℕ, divDiffOp Y n from rfl, happ]
  refine tsum_congr (fun n => ?_)
  rw [divDiffOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (lmul_rmul_apply Y Z i (n - i)).symm)

end Algebra

end YangMills.CMP98Eq119
