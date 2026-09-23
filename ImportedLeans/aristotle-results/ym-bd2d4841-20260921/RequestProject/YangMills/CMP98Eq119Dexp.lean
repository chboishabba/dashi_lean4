/-
# Bałaban's `g` really is the differential of the exponential map

`CMP98Eq119DivDiff` proved the algebraic half of the identification: the
divided-difference series

    D(Y, Z) = Σ_n (n+1)!^{-1} Σ_{i+j=n} Y^i Z Y^j

equals `e^{Y} · g(ad Y) Z`.  This file proves the analytic half — that
`D(Y, Z)` **is** the derivative of `exp` at `Y` in the direction `Z`:

    d/dt exp (Y + t Z) |_{t=0} = e^{Y} · g(ad Y) Z .

Mathlib's derivative of `exp` in a Banach algebra covers only the commutative
case, so the noncommutative statement is proved here from scratch, by an
elementary second-order remainder estimate:

* `dexpS` is the linear coefficient `S_n = Σ_{i+j=n−1} Y^i Z Y^j`, defined by
  the recursion `S_{n+1} = Y S_n + Z Y^n` (`dexpS_eq_sum` identifies it with
  the divided-difference sum);
* `dexpR` is the remainder `(Y + tZ)^n − Y^n − t S_n`, which satisfies the
  exact recursion `R_{n+1} = (Y + tZ) R_n + t² Z S_n` (`dexpR_succ`) and hence
  the bound `‖R_n‖ ≤ t² ‖Z‖² n² K^n` for `|t| ≤ 1` (`norm_dexpR_le`);
* summing against `1/n!` gives `‖exp(Y+tZ) − exp Y − t·D‖ ≤ C t²`
  (`norm_exp_sub_sub_le`), whence `hasDerivAt_exp_dexp`;
* combining with `dexpSeries_eq` gives the headline
  `hasDerivAt_exp_balabanG`, and `hasDerivAt_exp_dexpPlus` restates it in the
  opposite (right-trivialised) convention.

So the operators Bałaban writes as `g(∓ ad Y)` in Eq. (119) are not merely
named after the trivialised differential of `exp`: in this development they
are proved to be it.
-/
import RequestProject.YangMills.CMP98Eq119DivDiff

namespace YangMills.CMP98Eq119

open Finset Asymptotics

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A]

/-! ## 1. The linear coefficient `S_n` and the remainder `R_n` -/

/-- `S_n = Σ_{i+j=n−1} Y^i Z Y^j`, defined by its recursion. -/
noncomputable def dexpS (Y Z : A) : ℕ → A
  | 0 => 0
  | (n + 1) => Y * dexpS Y Z n + Z * Y ^ n

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
@[simp] theorem dexpS_zero (Y Z : A) : dexpS Y Z 0 = 0 := rfl

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
theorem dexpS_succ (Y Z : A) (n : ℕ) :
    dexpS Y Z (n + 1) = Y * dexpS Y Z n + Z * Y ^ n := rfl

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
/-- `S_{n+1}` is the divided-difference sum. -/
theorem dexpS_eq_sum (Y Z : A) (n : ℕ) :
    dexpS Y Z (n + 1) = ∑ i ∈ range (n + 1), Y ^ i * Z * Y ^ (n - i) := by
  induction n with
  | zero => simp [dexpS]
  | succ n ih =>
      rw [dexpS_succ, ih, Finset.mul_sum,
        Finset.sum_range_succ' (fun i => Y ^ i * Z * Y ^ (n + 1 - i)) (n + 1)]
      simp only [pow_zero, one_mul, Nat.sub_zero]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [← mul_assoc, ← mul_assoc, ← pow_succ']
      congr 2
      omega

/-- The Taylor remainder `R_n(t) = (Y + tZ)^n − Y^n − t S_n`. -/
noncomputable def dexpR (Y Z : A) (t : ℝ) (n : ℕ) : A :=
  (Y + t • Z) ^ n - Y ^ n - t • dexpS Y Z n

omit [NormOneClass A] [Nontrivial A] in
@[simp] theorem dexpR_zero (Y Z : A) (t : ℝ) : dexpR Y Z t 0 = 0 := by
  simp [dexpR]

omit [NormOneClass A] [Nontrivial A] in
/-- The exact remainder recursion. -/
theorem dexpR_succ (Y Z : A) (t : ℝ) (n : ℕ) :
    dexpR Y Z t (n + 1) = (Y + t • Z) * dexpR Y Z t n + (t ^ 2) • (Z * dexpS Y Z n) := by
  simp only [dexpR, dexpS, pow_succ' (Y + t • Z) n, pow_succ' Y n, mul_sub, smul_add,
    mul_smul_comm, add_mul, smul_mul_assoc, smul_smul, sq]
  abel

/-! ## 2. The remainder estimate -/

/-- The comparison radius: at least `1`, and at least `‖Y‖ + ‖Z‖`. -/
noncomputable def dexpK (Y Z : A) : ℝ := max (‖Y‖ + ‖Z‖) 1

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
theorem one_le_dexpK (Y Z : A) : 1 ≤ dexpK Y Z := le_max_right _ _

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
theorem dexpK_nonneg (Y Z : A) : 0 ≤ dexpK Y Z := le_trans zero_le_one (one_le_dexpK Y Z)

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
theorem dexpK_pow_nonneg (Y Z : A) (n : ℕ) : 0 ≤ dexpK Y Z ^ n :=
  pow_nonneg (dexpK_nonneg Y Z) n

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] in
theorem norm_le_dexpK (Y Z : A) : ‖Y‖ ≤ dexpK Y Z :=
  le_trans (le_add_of_nonneg_right (norm_nonneg Z)) (le_max_left _ _)

omit [NormedAlgebra ℝ A] [Nontrivial A] in
theorem norm_dexpS_le (Y Z : A) (n : ℕ) :
    ‖dexpS Y Z n‖ ≤ (n : ℝ) * ‖Z‖ * dexpK Y Z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hK1 : (1 : ℝ) ≤ dexpK Y Z := one_le_dexpK Y Z
      have hK0 : (0 : ℝ) ≤ dexpK Y Z := dexpK_nonneg Y Z
      have hKn : (0 : ℝ) ≤ dexpK Y Z ^ n := dexpK_pow_nonneg Y Z n
      have hZ : (0 : ℝ) ≤ ‖Z‖ := norm_nonneg _
      have hY : ‖Y‖ ≤ dexpK Y Z := norm_le_dexpK Y Z
      have hYn : ‖Y ^ n‖ ≤ dexpK Y Z ^ n :=
        le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hY n)
      have hstep : ‖Y * dexpS Y Z n‖ ≤ dexpK Y Z * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n) :=
        le_trans (norm_mul_le _ _) (mul_le_mul hY ih (norm_nonneg _) hK0)
      have hlast : ‖Z * Y ^ n‖ ≤ ‖Z‖ * dexpK Y Z ^ n :=
        le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left hYn (norm_nonneg _))
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      calc ‖dexpS Y Z (n + 1)‖ ≤ ‖Y * dexpS Y Z n‖ + ‖Z * Y ^ n‖ := by
            rw [dexpS_succ]; exact norm_add_le _ _
        _ ≤ dexpK Y Z * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n) + ‖Z‖ * dexpK Y Z ^ n :=
            add_le_add hstep hlast
        _ ≤ ((n + 1 : ℕ) : ℝ) * ‖Z‖ * dexpK Y Z ^ (n + 1) := by
            have hb : (0 : ℝ) ≤ ‖Z‖ * dexpK Y Z ^ n := mul_nonneg hZ hKn
            rw [pow_succ]
            push_cast
            nlinarith [mul_nonneg hb (sub_nonneg.2 hK1), mul_nonneg (mul_nonneg hb hnn) hK0]

omit [Nontrivial A] in
theorem norm_dexpR_le (Y Z : A) {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    ‖dexpR Y Z t n‖ ≤ t ^ 2 * ‖Z‖ ^ 2 * (n : ℝ) ^ 2 * dexpK Y Z ^ n := by
  have hK1 : (1 : ℝ) ≤ dexpK Y Z := one_le_dexpK Y Z
  have hK0 : (0 : ℝ) ≤ dexpK Y Z := dexpK_nonneg Y Z
  have hbase : ‖Y + t • Z‖ ≤ dexpK Y Z := by
    calc ‖Y + t • Z‖ ≤ ‖Y‖ + ‖t • Z‖ := norm_add_le _ _
      _ = ‖Y‖ + |t| * ‖Z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖Y‖ + 1 * ‖Z‖ := by
          have := mul_le_mul_of_nonneg_right ht (norm_nonneg Z)
          linarith
      _ ≤ dexpK Y Z := by rw [one_mul]; exact le_max_left _ _
  induction n with
  | zero => simp
  | succ n ih =>
      have hKn : (0 : ℝ) ≤ dexpK Y Z ^ n := dexpK_pow_nonneg Y Z n
      have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ha : (0 : ℝ) ≤ t ^ 2 * ‖Z‖ ^ 2 * dexpK Y Z ^ n :=
        mul_nonneg (mul_nonneg ht2 (sq_nonneg _)) hKn
      have h1 : ‖(Y + t • Z) * dexpR Y Z t n‖
          ≤ dexpK Y Z * (t ^ 2 * ‖Z‖ ^ 2 * (n : ℝ) ^ 2 * dexpK Y Z ^ n) :=
        le_trans (norm_mul_le _ _) (mul_le_mul hbase ih (norm_nonneg _) hK0)
      have h2 : ‖(t ^ 2) • (Z * dexpS Y Z n)‖
          ≤ t ^ 2 * (‖Z‖ * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n)) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht2]
        refine mul_le_mul_of_nonneg_left ?_ ht2
        exact le_trans (norm_mul_le _ _)
          (mul_le_mul_of_nonneg_left (norm_dexpS_le Y Z n) (norm_nonneg _))
      calc ‖dexpR Y Z t (n + 1)‖
          ≤ ‖(Y + t • Z) * dexpR Y Z t n‖ + ‖(t ^ 2) • (Z * dexpS Y Z n)‖ := by
            rw [dexpR_succ]; exact norm_add_le _ _
        _ ≤ dexpK Y Z * (t ^ 2 * ‖Z‖ ^ 2 * (n : ℝ) ^ 2 * dexpK Y Z ^ n)
              + t ^ 2 * (‖Z‖ * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n)) := add_le_add h1 h2
        _ ≤ t ^ 2 * ‖Z‖ ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * dexpK Y Z ^ (n + 1) := by
            have hexp : t ^ 2 * ‖Z‖ ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * dexpK Y Z ^ (n + 1)
                = (dexpK Y Z * (t ^ 2 * ‖Z‖ ^ 2 * (n : ℝ) ^ 2 * dexpK Y Z ^ n)
                    + t ^ 2 * (‖Z‖ * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n)))
                  + ((n : ℝ) * (2 * dexpK Y Z - 1) * (t ^ 2 * ‖Z‖ ^ 2 * dexpK Y Z ^ n)
                    + dexpK Y Z * (t ^ 2 * ‖Z‖ ^ 2 * dexpK Y Z ^ n)) := by
              push_cast
              ring
            have e1 : (0 : ℝ)
                ≤ (n : ℝ) * (2 * dexpK Y Z - 1) * (t ^ 2 * ‖Z‖ ^ 2 * dexpK Y Z ^ n) :=
              mul_nonneg (mul_nonneg hnn (by linarith)) ha
            have e2 : (0 : ℝ) ≤ dexpK Y Z * (t ^ 2 * ‖Z‖ ^ 2 * dexpK Y Z ^ n) :=
              mul_nonneg hK0 ha
            rw [hexp]
            linarith

/-! ## 3. Summability of the majorants -/

theorem pow_le_two_pow_pow (j n : ℕ) : ((n : ℝ)) ^ j ≤ ((2 : ℝ) ^ j) ^ n := by
  have h : (n : ℝ) ≤ 2 ^ n := by
    have h' : n < 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast h'.le
  calc ((n : ℝ)) ^ j ≤ ((2 : ℝ) ^ n) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg n) h j
    _ = ((2 : ℝ) ^ j) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]

/-- `Σ_n n^j K^n / n!` converges for every `j` and every `K ≥ 0`. -/
theorem summable_poly_pow_div_factorial (j : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    Summable fun n : ℕ => (n : ℝ) ^ j * K ^ n / (Nat.factorial n : ℝ) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Real.summable_pow_div_factorial (2 ^ j * K))
  · exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) j) (pow_nonneg hK n))
      (Nat.cast_nonneg _)
  · have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_div_iff_of_pos_right hfac, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_two_pow_pow j n) (pow_nonneg hK n)

omit [Nontrivial A] in
theorem norm_dexpS_term_le (Y Z : A) (n : ℕ) :
    ‖((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n‖
      ≤ ‖Z‖ * ((n : ℝ) ^ 1 * dexpK Y Z ^ n / (Nat.factorial n : ℝ)) := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Nat.factorial n : ℝ))⁻¹)]
  have hstep : ((Nat.factorial n : ℝ))⁻¹ * ‖dexpS Y Z n‖
      ≤ ((Nat.factorial n : ℝ))⁻¹ * ((n : ℝ) * ‖Z‖ * dexpK Y Z ^ n) :=
    mul_le_mul_of_nonneg_left (norm_dexpS_le Y Z n) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

omit [Nontrivial A] in
theorem summable_norm_dexpTerm (Y Z : A) :
    Summable fun n : ℕ => ‖((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_dexpS_term_le Y Z)
    ((summable_poly_pow_div_factorial 1 (dexpK_nonneg Y Z)).mul_left ‖Z‖)

omit [Nontrivial A] in
theorem norm_dexpR_term_le (Y Z : A) {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    ‖((Nat.factorial n : ℝ))⁻¹ • dexpR Y Z t n‖
      ≤ (‖Z‖ ^ 2 * t ^ 2) * ((n : ℝ) ^ 2 * dexpK Y Z ^ n / (Nat.factorial n : ℝ)) := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Nat.factorial n : ℝ))⁻¹)]
  have hstep := mul_le_mul_of_nonneg_left (norm_dexpR_le Y Z ht n)
    (by positivity : (0 : ℝ) ≤ ((Nat.factorial n : ℝ))⁻¹)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ## 4. The derivative -/

section Complete

variable [CompleteSpace A]

/-- The derivative candidate `D(Y,Z) = Σ_n S_n / n!`. -/
noncomputable def dexpD (Y Z : A) : A := ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n

omit [Nontrivial A] in
theorem summable_dexpTerm (Y Z : A) :
    Summable fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n :=
  (summable_norm_dexpTerm Y Z).of_norm

/-- The constant in the second-order estimate. -/
noncomputable def dexpC (Y Z : A) : ℝ :=
  ‖Z‖ ^ 2 * ∑' n : ℕ, (n : ℝ) ^ 2 * dexpK Y Z ^ n / (Nat.factorial n : ℝ)

omit [NormedAlgebra ℝ A] [NormOneClass A] [Nontrivial A] [CompleteSpace A] in
theorem dexpC_nonneg (Y Z : A) : 0 ≤ dexpC Y Z :=
  mul_nonneg (sq_nonneg _)
    (tsum_nonneg (fun n => div_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 2) (dexpK_pow_nonneg Y Z n))
      (Nat.cast_nonneg _)))

omit [Nontrivial A] in
/-- The second-order remainder estimate. -/
theorem norm_exp_sub_sub_le (Y Z : A) {t : ℝ} (ht : |t| ≤ 1) :
    ‖NormedSpace.exp (Y + t • Z) - NormedSpace.exp Y - t • dexpD Y Z‖ ≤ dexpC Y Z * t ^ 2 := by
  have hsa : Summable fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹ • (Y + t • Z) ^ n :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (Y + t • Z)).of_norm
  have hsb : Summable fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹ • Y ^ n :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) Y).of_norm
  have hsc : Summable fun n : ℕ => t • (((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n) :=
    (summable_dexpTerm Y Z).const_smul t
  have hexp1 : NormedSpace.exp (Y + t • Z)
      = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • (Y + t • Z) ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hexp2 : NormedSpace.exp Y = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • Y ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hD : t • dexpD Y Z = ∑' n : ℕ, t • (((Nat.factorial n : ℝ))⁻¹ • dexpS Y Z n) :=
    (tsum_const_smul'' t).symm
  have hsplit : NormedSpace.exp (Y + t • Z) - NormedSpace.exp Y - t • dexpD Y Z
      = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • dexpR Y Z t n := by
    rw [hexp1, hexp2, hD, ← hsa.tsum_sub hsb, ← (hsa.sub hsb).tsum_sub hsc]
    refine tsum_congr (fun n => ?_)
    rw [dexpR, smul_sub, smul_sub, smul_comm]
  have hmaj : Summable fun n : ℕ =>
      (‖Z‖ ^ 2 * t ^ 2) * ((n : ℝ) ^ 2 * dexpK Y Z ^ n / (Nat.factorial n : ℝ)) :=
    (summable_poly_pow_div_factorial 2 (dexpK_nonneg Y Z)).mul_left _
  have hsummableR : Summable fun n : ℕ => ‖((Nat.factorial n : ℝ))⁻¹ • dexpR Y Z t n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_dexpR_term_le Y Z ht) hmaj
  rw [hsplit]
  refine le_trans (norm_tsum_le_tsum_norm hsummableR) ?_
  refine le_trans (Summable.tsum_le_tsum (norm_dexpR_term_le Y Z ht) hsummableR hmaj)
    (le_of_eq ?_)
  rw [tsum_mul_left, dexpC]
  ring

omit [Nontrivial A] in
/-- **The derivative of `exp` in a noncommutative Banach algebra.** -/
theorem hasDerivAt_exp_dexp (Y Z : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + t • Z)) (dexpD Y Z) 0 := by
  have hC0 : 0 ≤ dexpC Y Z := dexpC_nonneg Y Z
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < min 1 (c / (dexpC Y Z + 1)) :=
    lt_min one_pos (div_pos hc (by linarith))
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 (c / (dexpC Y Z + 1)), hpos, fun {t} htdist => ?_⟩
  have habs : |t| < min 1 (c / (dexpC Y Z + 1)) := by simpa [dist_eq_norm] using htdist
  have ht1 : |t| ≤ 1 := le_of_lt (lt_of_lt_of_le habs (min_le_left _ _))
  have ht2 : |t| ≤ c / (dexpC Y Z + 1) := le_of_lt (lt_of_lt_of_le habs (min_le_right _ _))
  have hzero : NormedSpace.exp (Y + (0 : ℝ) • Z) = NormedSpace.exp Y := by simp
  have hstep : ‖NormedSpace.exp (Y + t • Z) - NormedSpace.exp (Y + (0 : ℝ) • Z)
      - (t - 0) • dexpD Y Z‖ ≤ dexpC Y Z * t ^ 2 := by
    rw [hzero, sub_zero]
    exact norm_exp_sub_sub_le Y Z ht1
  refine le_trans hstep ?_
  have hsq : t ^ 2 = |t| * |t| := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg t)]
  have hCle : dexpC Y Z * |t| ≤ c := by
    have h1 : dexpC Y Z * |t| ≤ (dexpC Y Z + 1) * (c / (dexpC Y Z + 1)) :=
      mul_le_mul (by linarith) ht2 (abs_nonneg t) (by linarith)
    rwa [mul_div_cancel₀ _ (by linarith : dexpC Y Z + 1 ≠ 0)] at h1
  rw [hsq]
  calc dexpC Y Z * (|t| * |t|) = (dexpC Y Z * |t|) * |t| := by ring
    _ ≤ c * |t| := mul_le_mul_of_nonneg_right hCle (abs_nonneg t)
    _ = c * ‖t - 0‖ := by rw [sub_zero, Real.norm_eq_abs]

/-! ## 5. The identification with Bałaban's `g` -/

/-- `D(Y,Z) = e^{Y} · g(ad Y) Z`. -/
theorem dexpD_eq (Y Z : A) : dexpD Y Z = NormedSpace.exp Y * balabanG (adOp Y) Z := by
  rw [← dexpSeries_eq Y Z, dexpD, (summable_dexpTerm Y Z).tsum_eq_zero_add]
  simp only [dexpS_zero, smul_zero, zero_add]
  exact tsum_congr (fun n => by rw [dexpS_eq_sum])

/-- **Bałaban's `g` is the trivialised differential of `exp`.**  The derivative
of `exp` at `Y` in the direction `Z` is `e^{Y} · g(ad Y) Z`, so the operator
Eq. (119) calls `g^{-1}(ad Y_x)` really does invert the differential of the
exponential in the left trivialisation. -/
theorem hasDerivAt_exp_balabanG (Y Z : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + t • Z))
      (NormedSpace.exp Y * balabanG (adOp Y) Z) 0 := by
  rw [← dexpD_eq]
  exact hasDerivAt_exp_dexp Y Z

/-- The same statement in the opposite (right-trivialised) convention:
`d/dt exp(Y+tZ)|₀ = g(−ad Y) Z · e^{Y}`. -/
theorem hasDerivAt_exp_dexpPlus (Y Z : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + t • Z))
      (balabanG (-(adOp Y)) Z * NormedSpace.exp Y) 0 := by
  have hball : ∀ x : A, x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℝ A).radius := by
    intro x
    rw [NormedSpace.expSeries_radius_eq_top ℝ A]
    exact edist_lt_top _ _
  have hcancel : balabanG (-(adOp Y)) Z * NormedSpace.exp Y
      = NormedSpace.exp Y * balabanG (adOp Y) Z := by
    rw [balabanG_adOp_neg_apply, mul_assoc, ← NormedSpace.exp_add_of_commute_of_mem_ball
      (𝕂 := ℝ) (Commute.neg_left (Commute.refl Y)) (hball (-Y)) (hball Y)]
    simp
  rw [hcancel]
  exact hasDerivAt_exp_balabanG Y Z

end Complete

/-! ## 6. Axiom audit -/

#print axioms dexpS_eq_sum
#print axioms norm_dexpR_le
#print axioms norm_exp_sub_sub_le
#print axioms hasDerivAt_exp_dexp
#print axioms dexpD_eq
#print axioms hasDerivAt_exp_balabanG
#print axioms hasDerivAt_exp_dexpPlus

end YangMills.CMP98Eq119
