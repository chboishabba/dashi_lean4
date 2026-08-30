/-
**From the exterior observable `e₂` to the weighted zero-pair budget.**

The weighted transverse-area functional of `WeightedGramTarget.lean`,

    D = ∑_ρ m_ρ² Δ_ρ,      Δ_ρ = ‖a_ρ‖² ‖b_ρ‖² − ⟪a_ρ, b_ρ⟫²,

is indexed by *zero reflection pairs*, whereas the exterior observable
`e₂(G) = ½((tr G)² − tr G²)` of `TraceInterface.lean` is the total pairwise area
of the *whole* evaluation family.  The two indexings have to be compared before
any trace-side estimate can be used as a budget.  This file does exactly that.

* `pairFamily a b : ι × Bool → E` assembles the two vectors of every zero pair
  into one family, and `pairDefect a b ρ` is that pair's Gram defect.
* `sum_pairDefect_le_e2` — **the comparison.**  The zero-pair-indexed total is
  at most the total pairwise exterior area of the assembled family:

      ∑_ρ Δ_ρ  ≤  e₂(G),      G = Gram(pairFamily a b).

  The proof is the one the geometry suggests: every pairwise defect is
  nonnegative (Cauchy–Schwarz), and the pairs `(a_ρ, b_ρ)` occur among all
  pairs, twice each in the ordered double sum.
* `weightedGramSum_le_e2` — the same with multiplicities: with `m_ρ² ≤ M`,

      ∑_ρ m_ρ² Δ_ρ  ≤  M · e₂(G).

* `e2_gram_le_e2_gram_add_tail` — the transport of `e₂` between two families
  (`G = A + E`), with the explicit tail of `e2OfTraces_sub_le`.
* `abs_offset_le_of_e2_budget` — the capstone at fixed height: a budget for
  `M · e₂(G)` confines every transverse offset to the tube `|α_ρ| ≤ √(E/c)`.
* `tendsto_zero_of_budget_ratio` and `source_tube_tendsto_zero` — the
  asymptotic statement: if the budget decays faster than the taper scale grows,
  `E(T)/L(T)⁶ → 0`, the tube closes, `α(T) → 0`.

The budget is an explicit hypothesis of every statement; nothing here produces
one for the zeros of `ζ`.
-/
import RiemannAnalytic.TraceInterface
import RiemannAnalytic.WeightedGramTarget

namespace RiemannAnalytic

open Filter Topology Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The assembled family -/

/-- The two vectors of every zero pair, assembled into a single family indexed
by `ι × Bool`. -/
def pairFamily {ι : Type*} (a b : ι → E) : ι × Bool → E :=
  fun p => if p.2 then b p.1 else a p.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem pairFamily_false {ι : Type*} (a b : ι → E) (ρ : ι) :
    pairFamily a b (ρ, false) = a ρ := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem pairFamily_true {ι : Type*} (a b : ι → E) (ρ : ι) :
    pairFamily a b (ρ, true) = b ρ := rfl

/-- The Gram defect of a single zero pair. -/
def pairDefect {ι : Type*} (a b : ι → E) (ρ : ι) : ℝ :=
  ‖a ρ‖ ^ 2 * ‖b ρ‖ ^ 2 - ⟪a ρ, b ρ⟫_ℝ ^ 2

theorem pairDefect_nonneg {ι : Type*} (a b : ι → E) (ρ : ι) : 0 ≤ pairDefect a b ρ := by
  have := sq_real_inner_le (a ρ) (b ρ)
  unfold pairDefect
  linarith

/-! ### Q2: the zero-pair total is dominated by `e₂` -/

/-- **The indexing comparison.**  The total zero-pair Gram defect is at most the
total pairwise exterior area `e₂(G)` of the assembled family. -/
theorem sum_pairDefect_le_e2 {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → E) :
    ∑ ρ : ι, pairDefect a b ρ
      ≤ e2OfTraces (Matrix.gram ℝ (pairFamily a b)).trace
          ((Matrix.gram ℝ (pairFamily a b) * Matrix.gram ℝ (pairFamily a b)).trace) := by
  classical
  set v := pairFamily a b with hv
  set D : ι × Bool → ι × Bool → ℝ :=
    fun p q => ‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2 with hD
  have hDnn : ∀ p q, 0 ≤ D p q := by
    intro p q
    have := sq_real_inner_le (v p) (v q)
    simp only [hD]
    linarith
  rw [e2OfTraces_gram_eq v]
  -- it suffices to bound twice the left side by the ordered double sum
  have hkey : ∑ ρ : ι, 2 * pairDefect a b ρ ≤ ∑ p : ι × Bool, ∑ q : ι × Bool, D p q := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun ρ _ => ?_
    have hrow : ∀ (β : Bool), D (ρ, β) (ρ, !β) ≤ ∑ q : ι × Bool, D (ρ, β) q := by
      intro β
      exact Finset.single_le_sum (f := fun q => D (ρ, β) q)
        (fun q _ => hDnn _ q) (Finset.mem_univ _)
    have hsum : ∑ β : Bool, ∑ q : ι × Bool, D (ρ, β) q
        = (∑ q : ι × Bool, D (ρ, true) q) + ∑ q : ι × Bool, D (ρ, false) q :=
      Fintype.sum_bool _
    have h1 := hrow false
    have h2 := hrow true
    have e1 : D (ρ, false) (ρ, true) = pairDefect a b ρ := by
      simp [hD, hv, pairDefect]
    have e2' : D (ρ, true) (ρ, false) = pairDefect a b ρ := by
      simp [hD, hv, pairDefect]
      rw [real_inner_comm (b ρ) (a ρ)]
      ring
    simp only [Bool.not_false, Bool.not_true] at h1 h2
    rw [e1] at h1
    rw [e2'] at h2
    rw [hsum]
    linarith
  have hDsum : ∑ p : ι × Bool, ∑ q : ι × Bool, D p q
      = ∑ p : ι × Bool, ∑ q : ι × Bool, (‖v p‖ ^ 2 * ‖v q‖ ^ 2 - ⟪v p, v q⟫_ℝ ^ 2) := rfl
  have hlhs : ∑ ρ : ι, 2 * pairDefect a b ρ = 2 * ∑ ρ : ι, pairDefect a b ρ := by
    rw [Finset.mul_sum]
  rw [hlhs, hDsum] at hkey
  linarith

/-- **Q2 with multiplicities.**  If every squared multiplicity is at most `M`,
the weighted zero-pair budget is at most `M · e₂(G)`. -/
theorem weightedGramSum_le_e2 {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → E)
    (s : Finset ι) (m : ι → ℝ) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ ρ ∈ s, m ρ ^ 2 ≤ M) :
    weightedGramSum s m (pairDefect a b)
      ≤ M * e2OfTraces (Matrix.gram ℝ (pairFamily a b)).trace
          ((Matrix.gram ℝ (pairFamily a b) * Matrix.gram ℝ (pairFamily a b)).trace) := by
  classical
  have h1 : weightedGramSum s m (pairDefect a b) ≤ ∑ ρ ∈ s, M * pairDefect a b ρ := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    exact mul_le_mul_of_nonneg_right (hm ρ hρ) (pairDefect_nonneg a b ρ)
  have h2 : ∑ ρ ∈ s, M * pairDefect a b ρ ≤ ∑ ρ : ι, M * pairDefect a b ρ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun ρ _ _ => mul_nonneg hM (pairDefect_nonneg a b ρ))
  have h3 : ∑ ρ : ι, M * pairDefect a b ρ = M * ∑ ρ : ι, pairDefect a b ρ := by
    rw [Finset.mul_sum]
  have h4 := mul_le_mul_of_nonneg_left (sum_pairDefect_le_e2 a b) hM
  linarith [h1, h2, h3 ▸ h4]

/-- **The localized form of Q2.**  For a sub-family `s` of zeros, the weighted
budget over `s` is bounded by `M` times the exterior area of the *restricted*
family alone — the windowed quantity a bounded-height prime-side estimate would
have to supply, rather than the total area of the whole evaluation family. -/
theorem weightedGramSum_le_e2_restrict {ι : Type*} [DecidableEq ι] (a b : ι → E)
    (s : Finset ι) (m : ι → ℝ) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ ρ ∈ s, m ρ ^ 2 ≤ M) :
    weightedGramSum s m (pairDefect a b)
      ≤ M * e2OfTraces
          (Matrix.gram ℝ (pairFamily (fun ρ : {x // x ∈ s} => a ρ)
            (fun ρ : {x // x ∈ s} => b ρ))).trace
          ((Matrix.gram ℝ (pairFamily (fun ρ : {x // x ∈ s} => a ρ)
              (fun ρ : {x // x ∈ s} => b ρ))
            * Matrix.gram ℝ (pairFamily (fun ρ : {x // x ∈ s} => a ρ)
              (fun ρ : {x // x ∈ s} => b ρ))).trace) := by
  classical
  set a' : {x // x ∈ s} → E := fun ρ => a ρ with ha'
  set b' : {x // x ∈ s} → E := fun ρ => b ρ with hb'
  have hsum : weightedGramSum s m (pairDefect a b)
      = weightedGramSum Finset.univ (fun ρ : {x // x ∈ s} => m ρ) (pairDefect a' b') := by
    unfold weightedGramSum
    rw [← Finset.sum_coe_sort s (fun ρ => m ρ ^ 2 * pairDefect a b ρ)]
    rfl
  rw [hsum]
  refine weightedGramSum_le_e2 a' b' Finset.univ (fun ρ : {x // x ∈ s} => m ρ) hM ?_
  intro ρ _
  exact hm ρ.1 ρ.2

/-! ### Q3: transport of `e₂` between two families -/

/-- **Transport of the exterior observable.**  For two families with Gram
matrices `A` and `G`, the exterior observable of `A` is at most that of `G` plus
the explicit tail built from the two trace discrepancies.  This is `G = A + E`
in the only form the observable sees: its two traces. -/
theorem e2_gram_le_e2_gram_add_tail (trA trA2 trG trG2 : ℝ) :
    e2OfTraces trA trA2
      ≤ e2OfTraces trG trG2
        + (|trA - trG| * (|trA| + |trG|) + |trA2 - trG2|) / 2 :=
  e2OfTraces_le_add_tail trA trA2 trG trG2

/-! ### The capstone: budget to tube -/

/-- **A budget for `M · e₂(G)` is a tube for every offset.**

If every zero pair obeys the quadratic floor `c α_ρ² ≤ Δ_ρ` with `c > 0`, every
multiplicity satisfies `1 ≤ m_ρ² ≤ M`, and the exterior observable obeys the
budget `M · e₂(G) ≤ Ebudget`, then every transverse offset satisfies

    |α_ρ| ≤ √(Ebudget / c).

This is the chain Q2 → tube: the trace side enters only through `e₂(G)`. -/
theorem abs_offset_le_of_e2_budget {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → E)
    {s : Finset ι} {m offset : ι → ℝ} {c M Ebudget : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hfloor : ∀ ρ ∈ s, c * offset ρ ^ 2 ≤ pairDefect a b ρ)
    (hm1 : ∀ ρ ∈ s, 1 ≤ m ρ ^ 2) (hm : ∀ ρ ∈ s, m ρ ^ 2 ≤ M)
    (hbudget : M * e2OfTraces (Matrix.gram ℝ (pairFamily a b)).trace
        ((Matrix.gram ℝ (pairFamily a b) * Matrix.gram ℝ (pairFamily a b)).trace) ≤ Ebudget)
    {ρ : ι} (hρ : ρ ∈ s) :
    |offset ρ| ≤ Real.sqrt (Ebudget / c) := by
  have hle : weightedGramSum s m (pairDefect a b) ≤ Ebudget :=
    le_trans (weightedGramSum_le_e2 a b s m hM hm) hbudget
  exact abs_offset_le_of_budget hc hfloor hm1 hle hρ

/-! ### Q5: the tube closes -/

/-- Division by a positive constant times a variable. -/
theorem div_const_mul (x y : ℝ) {c : ℝ} (hc : c ≠ 0) : x / (c * y) = c⁻¹ * (x / y) := by
  field_simp

/-- **The shrinking tube.**  If the budget decays relative to the sixth power of
the taper scale, `E(T)/L(T)⁶ → 0`, then the tube radius
`√(E(T)/(c L(T)⁶))` tends to zero, and so does any offset confined by it. -/
theorem tendsto_zero_of_budget_ratio {Ebud L α : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hratio : Tendsto (fun T => Ebud T / L T ^ 6) atTop (𝓝 0))
    (htube : ∀ᶠ T in atTop, |α T| ≤ Real.sqrt (Ebud T / (c * L T ^ 6))) :
    Tendsto α atTop (𝓝 0) := by
  have hrw : ∀ T, Ebud T / (c * L T ^ 6) = c⁻¹ * (Ebud T / L T ^ 6) := fun T =>
    div_const_mul _ _ hc.ne'
  have hzero : Tendsto (fun T => Real.sqrt (Ebud T / (c * L T ^ 6))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => c⁻¹ * (Ebud T / L T ^ 6)) atTop (𝓝 0) := by
      have := hratio.const_mul c⁻¹
      simpa using this
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simp only [Real.sqrt_zero] at h2
    refine h2.congr fun T => ?_
    simp [Function.comp, hrw T]
  refine tendsto_zero_iff_abs_tendsto_zero α |>.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun T => abs_nonneg _) htube hzero

/-- **The source-strength shrinking tube.**  With the source floor constant
`c = 81/16384` of `OneSidedGram.lean`, a budget with `E(T)/L(T)⁶ → 0` forces the
transverse offset of the tracked zero to zero. -/
theorem source_tube_tendsto_zero {Ebud L α : ℝ → ℝ}
    (hratio : Tendsto (fun T => Ebud T / L T ^ 6) atTop (𝓝 0))
    (htube : ∀ᶠ T in atTop, |α T| ≤ Real.sqrt (Ebud T / (81 / 16384 * L T ^ 6))) :
    Tendsto α atTop (𝓝 0) :=
  tendsto_zero_of_budget_ratio (by norm_num) hratio htube

end RiemannAnalytic
