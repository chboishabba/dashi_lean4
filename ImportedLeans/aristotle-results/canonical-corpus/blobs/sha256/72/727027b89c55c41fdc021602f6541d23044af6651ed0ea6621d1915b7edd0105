/-
**G8.1 — the anchored form before any inequality: row variance and wedge.**

G7 closed the *norm-and-count* lane: if each anchored minor is bounded by the
product of its two diagonal norms, then counting `O(HL)` of them lands exactly
at the critical scale `L⁶` and an arithmetic saving `H^{-θ}` with `θ > 2` would
be needed (`ShortWindowPrimeTarget.lean`).  This file proves that this lane is
closed for a *reason that is an artefact of the inequality used*, and supplies
the exact algebra that avoids paying that budget.

Three exact identities, no estimates:

* `anchorMinorSum_eq_diag_mul_trace_sub_rowNormSq` — the whole `O(q)`-minor
  observable is a **row variance**:

      `∑_{j ≠ i₀} (G_{i₀i₀}G_{jj} − G_{i₀j}²) = G_{i₀i₀}·tr G − ‖G_{i₀,*}‖²`,

  i.e. one diagonal entry, one trace, one row second moment — a *correlated
  difference*, not a sum of `q` separately estimated determinants.

* `lagrange_identity` / `anchorMinor_eq_wedgeSum` — the anchored minor is an
  exterior square:

      `(∑a²)(∑b²) − (∑ab)² = ½ ∑_{s,t} (a_s b_t − a_t b_s)²`,

  the discrete realisation of `‖f‖²‖g‖² − ⟨f,g⟩² = ½∬|f(s)g(t)−f(t)g(s)|²`.

* `anchorMinorPair_shift` — and this is the decisive one: for **any** pair
  `x, x + e`,

      `‖x‖²‖x+e‖² − ⟪x,x+e⟫² = ‖x‖²‖e‖² − ⟪x,e⟫²   ( ≤ ‖x‖²‖e‖² )`.

  The anchored minor sees only the *difference* of the two vectors.  For a
  translate family `v(s)` that is `M`-Lipschitz in the shift, this gives
  `translatedWedge_factor`: the minor at shift `s` carries the extra factor
  `s²`, which the bound `‖v(0)‖²‖v(s)‖²` throws away completely.

Consequences drawn here:

* `anchorMinorSum_le_shift_budget` — the whole anchored observable of a
  Lipschitz translate family costs `‖v i₀‖² M² ∑_j s_j²` instead of
  `∑_j ‖v i₀‖²‖v j‖²`;
* `anchorMinorSum_lt_normCount_budget` — and this is *strictly* smaller
  whenever the shifts are small compared with the vector norms.  So the
  norm-and-count budget is genuinely lossy: bounding the anchored determinant by
  its two diagonal norms discards a factor that is available in the algebra.
* `anchorMinorSum_grid_shift_budget` — at grid spacing `h` over a window of `q`
  shifts the budget is `‖v i₀‖² M² h² q³`, replacing count `q` times norm² by
  `M²h²q³`; `grid_shift_gain_lt_one` records exactly when this is a gain.

Nothing here refers to `ζ`, and nothing here is an estimate of arithmetic data:
it is the algebra that must be performed *before* the explicit formula is
substituted, so that no cancellation is destroyed first.
-/
import RiemannAnalytic.AnchoredMinorConsumer

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The row-variance form of the anchored observable -/

/-- The local trace of the Gram matrix of a family: `tr G = ∑_j ‖v j‖²`. -/
def gramTraceOf {n : Type*} [Fintype n] (v : n → E) : ℝ := ∑ j, ‖v j‖ ^ 2

/-- The second moment of the anchor row of the Gram matrix:
`‖G_{i₀,*}‖² = ∑_j ⟪v i₀, v j⟫²`. -/
def gramRowNormSq {n : Type*} [Fintype n] (v : n → E) (i₀ : n) : ℝ :=
  ∑ j, ⟪v i₀, v j⟫_ℝ ^ 2

omit [InnerProductSpace ℝ E] in
theorem gramTraceOf_nonneg {n : Type*} [Fintype n] (v : n → E) : 0 ≤ gramTraceOf v :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem gramRowNormSq_nonneg {n : Type*} [Fintype n] (v : n → E) (i₀ : n) :
    0 ≤ gramRowNormSq v i₀ :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **The anchored observable is an anchored row variance.**

    `∑_{j ≠ i₀} (G_{i₀i₀}G_{jj} − G_{i₀j}²) = G_{i₀i₀}·tr G − ‖G_{i₀,*}‖²`.

The `O(q)` anchored minors assemble into three quantities — one diagonal entry,
one local trace, one row second moment — and it is their *correlated
difference* that carries the signal.  This is the form in which the arithmetic
side should be asked to evaluate it: not as `q` separately estimated
determinants. -/
theorem anchorMinorSum_eq_diag_mul_trace_sub_rowNormSq {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (i₀ : n) :
    anchorMinorSum v i₀ = ‖v i₀‖ ^ 2 * gramTraceOf v - gramRowNormSq v i₀ := by
  classical
  have hself : anchorMinor v i₀ i₀ = 0 := anchorMinor_self v i₀
  have hsum : anchorMinorSum v i₀ = ∑ j, anchorMinor v i₀ j := by
    unfold anchorMinorSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀), hself, add_zero]
  rw [hsum]
  unfold anchorMinor gramTraceOf gramRowNormSq
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-! ### The wedge (Lagrange) identity -/

/-- **Lagrange's identity**: the Cauchy–Schwarz defect of two coordinate vectors
is exactly half the total squared exterior area of their `2 × 2` minors.  This
is the discrete realisation of

    `‖f‖²‖g‖² − ⟨f,g⟩² = ½ ∬ |f(s)g(t) − f(t)g(s)|² ds dt`. -/
theorem lagrange_identity {m : Type*} [Fintype m] (a b : m → ℝ) :
    (∑ s, a s ^ 2) * (∑ s, b s ^ 2) - (∑ s, a s * b s) ^ 2
      = 1 / 2 * ∑ s, ∑ t, (a s * b t - a t * b s) ^ 2 := by
  set A := ∑ s, a s ^ 2 with hA
  set B := ∑ s, b s ^ 2 with hB
  set C := ∑ s, a s * b s with hC
  have hexp : ∀ s : m, ∑ t, (a s * b t - a t * b s) ^ 2
      = a s ^ 2 * B - a s * b s * 2 * C + b s ^ 2 * A := by
    intro s
    have hterm : ∀ t : m, (a s * b t - a t * b s) ^ 2
        = a s ^ 2 * b t ^ 2 - a s * b s * 2 * (a t * b t) + b s ^ 2 * a t ^ 2 :=
      fun t => by ring
    rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hterm t,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hA, ← hB, ← hC]
  rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hexp s,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul]
  have h2 : ∑ x : m, b x ^ 2 * A = B * A := by rw [← Finset.sum_mul, ← hB]
  rw [← hA, ← hC, h2]
  ring

/-- The anchored minor of two coordinate vectors is the squared wedge: half the
total squared area of all its `2 × 2` sub-minors. -/
theorem anchorMinor_eq_wedgeSum {m : Type*} [Fintype m] (a b : m → ℝ) :
    (∑ s, a s ^ 2) * (∑ s, b s ^ 2) - (∑ s, a s * b s) ^ 2
      = 1 / 2 * ∑ s, ∑ t, (a s * b t - a t * b s) ^ 2 :=
  lagrange_identity a b

/-! ### The anchored minor sees only the difference of the two vectors -/

/-- **The shift identity.**  For any pair `x`, `x + e`,

    `‖x‖²‖x+e‖² − ⟪x, x+e⟫² = ‖x‖²‖e‖² − ⟪x, e⟫²`.

The anchored determinant does not depend on the bulk of the second vector at
all — only on its displacement from the anchor. -/
theorem anchorMinorPair_shift (x e : E) :
    ‖x‖ ^ 2 * ‖x + e‖ ^ 2 - ⟪x, x + e⟫_ℝ ^ 2 = ‖x‖ ^ 2 * ‖e‖ ^ 2 - ⟪x, e⟫_ℝ ^ 2 := by
  have hnorm : ‖x + e‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, e⟫_ℝ + ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [inner_add_add_self, real_inner_comm e x]
    ring
  have hinner : ⟪x, x + e⟫_ℝ = ‖x‖ ^ 2 + ⟪x, e⟫_ℝ := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
  rw [hnorm, hinner]
  ring

/-- The anchored minor in difference form: it is the Cauchy–Schwarz defect of
the anchor against the *displacement* `v j − v i₀`. -/
theorem anchorMinor_eq_shift {n : Type*} (v : n → E) (i₀ j : n) :
    anchorMinor v i₀ j
      = ‖v i₀‖ ^ 2 * ‖v j - v i₀‖ ^ 2 - ⟪v i₀, v j - v i₀⟫_ℝ ^ 2 := by
  have hj : v j = v i₀ + (v j - v i₀) := by abel
  unfold anchorMinor
  rw [hj]
  simpa using anchorMinorPair_shift (v i₀) (v j - v i₀)

/-- The displacement bound for a single anchored minor. -/
theorem anchorMinor_le_normSq_mul_shiftSq {n : Type*} (v : n → E) (i₀ j : n) :
    anchorMinor v i₀ j ≤ ‖v i₀‖ ^ 2 * ‖v j - v i₀‖ ^ 2 := by
  rw [anchorMinor_eq_shift]
  nlinarith [sq_nonneg (⟪v i₀, v j - v i₀⟫_ℝ)]

/-- **`translatedWedge_factor`.**  For a family of translates `v s` of a single
profile that is `M`-Lipschitz in the shift parameter, the anchored minor at
shift `s` carries the factor `s²`:

    `Δ(v 0, v s) ≤ ‖v 0‖² M² s²`.

The bound `‖v 0‖²‖v s‖²` — the norm-and-count budget — discards this factor
entirely. -/
theorem translatedWedge_factor {V : ℝ → E} {M : ℝ}
    (hLip : ∀ s : ℝ, ‖V s - V 0‖ ≤ M * |s|) (s : ℝ) :
    ‖V 0‖ ^ 2 * ‖V s‖ ^ 2 - ⟪V 0, V s⟫_ℝ ^ 2 ≤ ‖V 0‖ ^ 2 * (M ^ 2 * s ^ 2) := by
  have hM0 : 0 ≤ M * |s| := le_trans (norm_nonneg _) (hLip s)
  have hkey := anchorMinor_le_normSq_mul_shiftSq (fun r : ℝ => V r) 0 s
  unfold anchorMinor at hkey
  refine hkey.trans ?_
  have hsq : ‖V s - V 0‖ ^ 2 ≤ M ^ 2 * s ^ 2 := by
    have := hLip s
    nlinarith [norm_nonneg (V s - V 0), sq_abs s]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-! ### The anchored budget of a Lipschitz translate family -/

/-- **The shift budget for the whole anchored observable.**  If every member of
the family is within `M · |σ j|` of the anchor, then

    `∑_{j ≠ i₀} Δ(v i₀, v j) ≤ ‖v i₀‖² M² ∑_j σ j²`,

replacing "count × norm²" by "count × (shift)²". -/
theorem anchorMinorSum_le_shift_budget {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (i₀ : n) {M : ℝ} {σ : n → ℝ}
    (hshift : ∀ j, ‖v j - v i₀‖ ≤ M * |σ j|) :
    anchorMinorSum v i₀ ≤ ‖v i₀‖ ^ 2 * (M ^ 2 * ∑ j, σ j ^ 2) := by
  classical
  have hterm : ∀ j, anchorMinor v i₀ j ≤ ‖v i₀‖ ^ 2 * (M ^ 2 * σ j ^ 2) := by
    intro j
    refine (anchorMinor_le_normSq_mul_shiftSq v i₀ j).trans ?_
    have hsq : ‖v j - v i₀‖ ^ 2 ≤ M ^ 2 * σ j ^ 2 := by
      have := hshift j
      nlinarith [norm_nonneg (v j - v i₀), sq_abs (σ j)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hsum : anchorMinorSum v i₀ ≤ ∑ j, ‖v i₀‖ ^ 2 * (M ^ 2 * σ j ^ 2) := by
    unfold anchorMinorSum
    refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
    intro j _ _
    positivity
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]

/-- The plain norm-and-count budget, for comparison: bounding each anchored
determinant by the product of its two diagonal norms. -/
theorem anchorMinorSum_le_normCount_budget {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (i₀ : n) :
    anchorMinorSum v i₀ ≤ ∑ j ∈ Finset.univ.erase i₀, ‖v i₀‖ ^ 2 * ‖v j‖ ^ 2 := by
  refine Finset.sum_le_sum fun j _ => ?_
  unfold anchorMinor
  nlinarith [sq_nonneg (⟪v i₀, v j⟫_ℝ)]

omit [InnerProductSpace ℝ E] in
/-- **The norm-and-count budget is genuinely lossy.**  If the family is a
Lipschitz translate family whose displacements are strictly smaller than the
vector norms, then the shift budget is *strictly* below the norm-and-count
budget.  This is the exact sense in which G7's critical-scale computation is an
artefact of the inequality used, not a property of the anchored determinant. -/
theorem anchorMinorSum_lt_normCount_budget {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (i₀ : n) {M : ℝ} {σ : n → ℝ}
    (hv0 : 0 < ‖v i₀‖)
    (hne : (Finset.univ.erase i₀).Nonempty)
    (hsmall : ∀ j ∈ Finset.univ.erase i₀, M ^ 2 * σ j ^ 2 < ‖v j‖ ^ 2)
    (hσ0 : σ i₀ = 0) :
    ‖v i₀‖ ^ 2 * (M ^ 2 * ∑ j, σ j ^ 2)
      < ∑ j ∈ Finset.univ.erase i₀, ‖v i₀‖ ^ 2 * ‖v j‖ ^ 2 := by
  classical
  have hsplit : ∑ j, σ j ^ 2 = ∑ j ∈ Finset.univ.erase i₀, σ j ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀), hσ0]
    simp
  have hstrict : ∑ j ∈ Finset.univ.erase i₀, M ^ 2 * σ j ^ 2
      < ∑ j ∈ Finset.univ.erase i₀, ‖v j‖ ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne hsmall
  have hpos : (0 : ℝ) < ‖v i₀‖ ^ 2 := by positivity
  calc ‖v i₀‖ ^ 2 * (M ^ 2 * ∑ j, σ j ^ 2)
      = ‖v i₀‖ ^ 2 * ∑ j ∈ Finset.univ.erase i₀, M ^ 2 * σ j ^ 2 := by
        rw [hsplit, Finset.mul_sum]
    _ < ‖v i₀‖ ^ 2 * ∑ j ∈ Finset.univ.erase i₀, ‖v j‖ ^ 2 :=
        mul_lt_mul_of_pos_left hstrict hpos
    _ = ∑ j ∈ Finset.univ.erase i₀, ‖v i₀‖ ^ 2 * ‖v j‖ ^ 2 := by rw [Finset.mul_sum]

/-! ### The grid case: spacing `h`, window of `q` shifts -/

/-- **The anchored budget on a shift grid.**  For a window of `q` translates at
spacing `h`, the anchored observable costs at most `‖v i₀‖² M² h² q³` — the
count enters cubed, but each unit of count is weighted by `h²`, which the
norm-and-count budget never sees. -/
theorem anchorMinorSum_grid_shift_budget {q : ℕ} (v : Fin q → E) (i₀ : Fin q) {M h : ℝ}
    (hshift : ∀ j : Fin q, ‖v j - v i₀‖ ≤ M * |h * ((j : ℕ) : ℝ)|) :
    anchorMinorSum v i₀ ≤ ‖v i₀‖ ^ 2 * (M ^ 2 * (h ^ 2 * (q : ℝ) ^ 3)) := by
  classical
  have hb := anchorMinorSum_le_shift_budget v i₀ (σ := fun j : Fin q => h * ((j : ℕ) : ℝ)) hshift
  refine hb.trans ?_
  have hcount : ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ h ^ 2 * (q : ℝ) ^ 3 := by
    have hterm : ∀ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ h ^ 2 * (q : ℝ) ^ 2 := by
      intro j
      have hj : ((j : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.lt_of_lt_of_le j.isLt le_rfl).le
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have : ((j : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg h]
    calc ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2
        ≤ ∑ _j : Fin q, h ^ 2 * (q : ℝ) ^ 2 := Finset.sum_le_sum fun j _ => hterm j
      _ = (q : ℝ) * (h ^ 2 * (q : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = h ^ 2 * (q : ℝ) ^ 3 := by ring
  have : M ^ 2 * ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ M ^ 2 * (h ^ 2 * (q : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hcount (by positivity)
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **The exact gain ledger for the grid.**  Against a norm-and-count budget
`q · ‖v i₀‖² · N²` (each vector of squared norm `N²`), the shift budget is
smaller precisely when `M²h²q² < N²`, i.e. when the total window displacement
`M·hq` stays below the vector scale.  At source spacing `h ≍ 1/L` and window
count `q ≍ HL` that reads `M²H² < N²`. -/
theorem grid_shift_gain_lt_one {M h N : ℝ} {q : ℕ} (hq : 0 < (q : ℝ))
    (hgain : M ^ 2 * (h ^ 2 * (q : ℝ) ^ 2) < N ^ 2) :
    M ^ 2 * (h ^ 2 * (q : ℝ) ^ 3) < (q : ℝ) * N ^ 2 := by
  calc M ^ 2 * (h ^ 2 * (q : ℝ) ^ 3) = (q : ℝ) * (M ^ 2 * (h ^ 2 * (q : ℝ) ^ 2)) := by ring
    _ < (q : ℝ) * N ^ 2 := mul_lt_mul_of_pos_left hgain hq

end RiemannAnalytic
