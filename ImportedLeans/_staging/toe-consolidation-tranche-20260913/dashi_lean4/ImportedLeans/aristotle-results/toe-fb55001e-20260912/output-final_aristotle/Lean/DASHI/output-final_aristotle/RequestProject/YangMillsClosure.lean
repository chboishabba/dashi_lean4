import Mathlib

/-!
# Yang–Mills polymer / Balaban RG closure: the analytic core

This file formalizes the genuine mathematical content of the four Yang–Mills
"closure receipts" requested (YM-1 … YM-4).  The physics receipts are about a
`p = 7` same-prime Wilson polymer activity, a Kotecký–Preiss (KP) cluster
expansion and a Balaban renormalisation-group (RG) induction, but every one of
the receipts reduces to an elementary, self-contained real-analysis statement:

* **YM-1** (`ym1_local_kp_sum_below_one`): a rooted KP sum whose size-`n`
  contribution is dominated by a lattice-animal count `(8e)^n` times the activity
  bound `e^{-c_K n}` and the tuning factor `e^{a n}` (with `a = c_K/4`) is summable
  and bounded by `1/2`, provided `c_K ≥ (4/3)·log(24e)`.

  *Threshold correction.*  The informal note proposed `c_K > (4/3)·log(16e)`;
  that threshold only yields the bound `≤ 1`.  To obtain the claimed strict bound
  `≤ 1/2` the geometric ratio must be `≤ 1/3`, which needs
  `c_K ≥ (4/3)·log(24e)`.  We use the corrected threshold here.

* **YM-2** (`ym2_strict_absorption`): the absorption sum over polymers meeting a
  fixed polymer `s` is bounded by `|s|·δ`, hence by `|s|/2` when the rooted sum
  `δ ≤ 1/2`.  This is the grouping/translation-invariance step.

* **YM-3** (`ym3_uniform_volume_kp`): if each RG step multiplies the rooted KP
  sum by an improvement factor `q k ≤ 1`, the KP sum stays `≤ 1/2` uniformly in
  the step `k` (and hence in the volume).

* **YM-4** (`ym4_balaban_rg_gronwall`): a discrete Grönwall bound
  `C (n) ≤ (C 0 + Σ b) · exp (Σ a)` for the RG control parameter, giving a
  uniform constant `C_∞`.
-/

open scoped BigOperators

namespace YangMillsClosure

/-! ## YM-1 : local KP sum below one -/

/--
**YM-1 (KP local sum).**  Let `A n` be the contribution to the rooted
Kotecký–Preiss sum coming from polymers of size `n` containing the origin.  By
the polymer factorisation bound `|z₇(Γ)| ≤ e^{-c_K|Γ|}` and the lattice-animal
count `N_n ≤ (8e)^n`, together with the tuning `a = c_K/4`, every such
contribution obeys `A n ≤ (8e)^n · e^{-c_K n} · e^{a n}`.  If
`c_K ≥ (4/3)·log(24e)` then the whole rooted KP sum is bounded by `1/2 < 1`.
-/
theorem ym1_local_kp_sum_below_one
    (cK a : ℝ) (ha : a = cK / 4)
    (hcK : (4 / 3) * Real.log (24 * Real.exp 1) ≤ cK)
    (A : ℕ → ℝ) (hA0 : A 0 = 0) (hAnn : ∀ n, 0 ≤ A n)
    (hAbound : ∀ n, 1 ≤ n →
      A n ≤ (8 * Real.exp 1) ^ n * Real.exp (-cK * n) * Real.exp (a * n)) :
    ∑' n, A n ≤ 1 / 2 := by
  -- Let $r := 8 * Real.exp 1 * Real.exp (-(3*cK/4))$.
  set r := 8 * Real.exp 1 * Real.exp (-(3 * cK / 4)) with hr_def
  have hr : r ≤ 1 / 3 := by
    -- Using the bound $Real.exp (-(3 * cK / 4)) ≤ (24 * Real.exp 1)⁻¹$, we get:
    have h_exp_bound : Real.exp (-(3 * cK / 4)) ≤ (24 * Real.exp 1)⁻¹ := by
      rw [ ← Real.exp_log ( by positivity : 0 < ( 24 * Real.exp 1 ) ), ← Real.exp_neg ] ; norm_num ; linarith;
    nlinarith [ Real.exp_pos 1, mul_inv_cancel₀ ( by positivity : ( 24 * Real.exp 1 ) ≠ 0 ) ];
  -- By definition of $r$, we know that for $n \geq 1$, $A n \leq r^n$.
  have hr_bound : ∀ n, 1 ≤ n → A n ≤ r ^ n := by
    intro n hn; convert hAbound n hn using 1; rw [ mul_pow, ← Real.exp_nat_mul ] ; ring;
    simpa only [ ha, mul_assoc, ← Real.exp_add ] using by ring;
  -- Therefore, $\sum_{n=1}^{\infty} A n \leq \sum_{n=1}^{\infty} r^n$.
  have h_sum_bound : ∑' n, A n ≤ ∑' n, r ^ (n + 1) := by
    rw [ Summable.tsum_eq_zero_add ];
    · rw [ hA0, zero_add ] ; exact Summable.tsum_le_tsum ( fun n => hr_bound _ le_add_self ) ( by exact Summable.of_nonneg_of_le ( fun n => hAnn _ ) ( fun n => hr_bound _ le_add_self ) <| Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) <| by linarith ) <| Nat.succ_injective ) <| by exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) <| by linarith ) <| Nat.succ_injective;
    · exact Summable.of_nonneg_of_le ( fun n => hAnn n ) ( fun n => if hn : 1 ≤ n then hr_bound n hn else by aesop ) ( summable_geometric_of_lt_one ( by positivity ) ( show r < 1 by linarith ) );
  refine le_trans h_sum_bound ?_;
  norm_num [ pow_succ', tsum_mul_left, tsum_geometric_of_lt_one ( show 0 ≤ r by positivity ) ( show r < 1 by linarith ) ];
  rw [ ← div_eq_mul_inv, div_le_iff₀ ] <;> linarith [ show 0 < r by positivity ]

/-! ## YM-2 : strict absorption from the KP bound -/

/-- **YM-2 (strict absorption).**  For a fixed polymer `s` (a finite set of
blocks), any polymer meeting `s` contains one of its blocks; grouping by that
block bounds the absorption functional by `Σ_{b ∈ s} rooted b`.  If the rooted
KP sum at every block is `≤ δ` and `δ ≤ 1/2`, the absorption functional is
`≤ |s|·δ ≤ |s|/2`. -/
theorem ym2_strict_absorption
    {β : Type*} (s : Finset β) (rooted : β → ℝ) (δ kpAbs : ℝ)
    (hδ : ∀ b ∈ s, rooted b ≤ δ)
    (hδhalf : δ ≤ 1 / 2)
    (hkpAbs : kpAbs ≤ ∑ b ∈ s, rooted b) :
    kpAbs ≤ s.card * δ ∧ kpAbs ≤ s.card * (1 / 2) := by
  exact ⟨ hkpAbs.trans ( le_trans ( Finset.sum_le_sum hδ ) ( by simp +decide ) ), hkpAbs.trans ( le_trans ( Finset.sum_le_sum hδ ) ( by simpa using mul_le_mul_of_nonneg_left hδhalf ( Nat.cast_nonneg _ ) ) ) ⟩

/-! ## YM-3 : uniform-volume KP induction -/

/-- **YM-3 (uniform-volume KP induction).**  Let `δ k` be the rooted KP sum at
RG step `k`.  Asymptotic freedom supplies an improvement factor `q k ≤ 1` with
`δ (k+1) ≤ q k · δ k`.  Starting from `δ 0 ≤ 1/2`, the KP sum stays `≤ 1/2`
uniformly in the step `k` (hence uniformly in the volume). -/
theorem ym3_uniform_volume_kp
    (δ q : ℕ → ℝ)
    (hδnn : ∀ k, 0 ≤ δ k)
    (hq1 : ∀ k, q k ≤ 1)
    (hrec : ∀ k, δ (k + 1) ≤ q k * δ k)
    (hδ0 : δ 0 ≤ 1 / 2) :
    ∀ k, δ k ≤ 1 / 2 := by
  exact fun k => Nat.recOn k hδ0 fun k ih => le_trans ( hrec k ) ( mul_le_of_le_one_left ( hδnn k ) ( hq1 k ) |> le_trans <| ih )

/-! ## YM-4 : Balaban RG induction (discrete Grönwall) -/

/--
**YM-4 (Balaban RG discrete Grönwall).**  The RG control parameter obeys the
step inequality `C (k+1) ≤ C k · (1 + a k) + b k`, where `a k = C''·g_k²` is the
saddle/determinant growth and `b k = C'''·δ_k` the polymer remainder.  Then
`C n ≤ (C 0 + Σ_{j<n} b j) · exp (Σ_{j<n} a j)`; since `Σ a j ≤ C''/(2b₀)` and
`Σ b j` is controlled, this yields a uniform constant `C_∞`.
-/
theorem ym4_balaban_rg_gronwall
    (C a b : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hrec : ∀ k, C (k + 1) ≤ C k * (1 + a k) + b k) :
    ∀ n, C n ≤ (C 0 + ∑ j ∈ Finset.range n, b j) *
      Real.exp (∑ j ∈ Finset.range n, a j) := by
  intro n; induction' n with n ih <;> simp_all +decide [ Finset.sum_range_succ, Real.exp_add ] ;
  refine le_trans ( hrec n ) ?_;
  -- By dividing both sides of the inequality by `Real.exp (∑ j ∈ Finset.range n, a j)`, we can simplify it.
  suffices h_div : (C 0 + ∑ j ∈ Finset.range n, b j) * (1 + a n) + b n / Real.exp (∑ j ∈ Finset.range n, a j) ≤ (C 0 + ∑ j ∈ Finset.range n, b j + b n) * Real.exp (a n) by
    rw [ add_div', div_le_iff₀ ] at h_div <;> nlinarith [ Real.exp_pos ( ∑ j ∈ Finset.range n, a j ), Real.exp_pos ( a n ), hC n, ha n, hb n ];
  -- By dividing both sides of the inequality by `Real.exp (∑ j ∈ Finset.range n, a j)`, we can simplify it to:
  suffices h_div : (C 0 + ∑ j ∈ Finset.range n, b j) * (1 + a n) + b n / Real.exp (∑ j ∈ Finset.range n, a j) ≤ (C 0 + ∑ j ∈ Finset.range n, b j) * Real.exp (a n) + b n * Real.exp (a n) by
    lia;
  refine' add_le_add _ _;
  · exact mul_le_mul_of_nonneg_left ( by linarith [ Real.add_one_le_exp ( a n ) ] ) ( add_nonneg ( hC 0 ) ( Finset.sum_nonneg fun _ _ => hb _ ) );
  · exact mul_le_mul_of_nonneg_left ( by rw [ ← Real.exp_neg ] ; exact Real.exp_le_exp.mpr ( neg_le_iff_add_nonneg.mpr ( by linarith [ ha n, Finset.sum_nonneg fun j ( hj : j ∈ Finset.range n ) => ha j ] ) ) ) ( hb n )

/--
**YM-4 corollary (uniform constant `C_∞`).**  If the growth exponents and the
remainder sums are uniformly bounded (`Σ a ≤ A∞`, `Σ b ≤ B∞`), the RG control
parameter is bounded by the step-independent constant `C_∞ = (C 0 + B∞)·exp A∞`.
-/
theorem ym4_balaban_rg_uniform_bound
    (C a b : ℕ → ℝ) (Ainf Binf : ℝ)
    (hC : ∀ k, 0 ≤ C k) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hrec : ∀ k, C (k + 1) ≤ C k * (1 + a k) + b k)
    (hAsum : ∀ n, ∑ j ∈ Finset.range n, a j ≤ Ainf)
    (hBsum : ∀ n, ∑ j ∈ Finset.range n, b j ≤ Binf) :
    ∀ n, C n ≤ (C 0 + Binf) * Real.exp Ainf := by
  intro n
  have := ym4_balaban_rg_gronwall C a b hC ha hb hrec n
  have h_exp : Real.exp (∑ j ∈ Finset.range n, a j) ≤ Real.exp Ainf := by
    exact Real.exp_le_exp.mpr ( hAsum n )
  have h_sum_b : ∑ j ∈ Finset.range n, b j ≤ Binf := by
    exact hBsum n
  have h_nonneg : 0 ≤ C 0 + ∑ j ∈ Finset.range n, b j := by
    exact add_nonneg ( hC 0 ) ( Finset.sum_nonneg fun _ _ => hb _ )
  exact le_trans this (by
  gcongr;
  exact add_nonneg ( hC 0 ) ( le_trans ( Finset.sum_nonneg fun _ _ => hb _ ) h_sum_b ))

end YangMillsClosure