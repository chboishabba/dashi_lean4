/-
**Lane B — the anchored short-window prime target, and the exponent it needs.**

Two things are settled here, both on the zero side, so that the arithmetic
obligation is stated in its *smallest sufficient* form and its required
strength is computed before any short-interval mean-value theorem is attempted.

**1. The anchored observable is already sufficient.**  The exterior observable
`e₂(G_H)` sums all `O(q²)` pair minors of the window block.  The coercivity
argument uses only the `q − 1` minors through the anchor coordinate — the
central grid point, where the sample of a real even taper is real, so the
transverse coordinate vanishes there.  This file defines that observable for the
actual source window,

    `finiteGridAnchorMinorSum φ h α m = ∑_{k ≠ 0} (a₀ b_k − a_k b₀)²`,

proves it equals `a₀² ‖b‖²` (`finiteGridAnchorMinorSum_eq`), that it is
dominated by the full window Gram defect
(`finiteGridAnchorMinorSum_le_gramDefect`), and — the point — that it carries
the *entire* source floor by itself:

    `(81/16384) L⁶ α² ≤ finiteGridAnchorMinorSum`   (`anchoredMinorSum_source_floor`),

so a prime-side budget for the anchored form alone already yields the tube
(`anchored_budget_tube`).  The arithmetic side therefore never has to reconstruct
the whole local `e₂`.

**2. What cancellation exponent in the window length `H` is needed.**  With a
mesoscopic window of height `H`, the local zero count is `≍ H L`, and the true
per-vector energy is `≍ L²` (`LocalTraceScale.lean`), so the generic
norm-and-count budget is

    `2 A² Cb² H² L⁶`,

*worse* as `H` grows.  Writing an arithmetic saving as a power `H^θ`, the
normalized budget is `2A²Cb² H^{2−θ}` (`mesoBudget_ratio_eq`).  Hence:

* `meso_no_gain_of_exponent_le_two` — for `θ ≤ 2` and any window with `H ≥ 1`
  the normalized budget stays `≥ 2A²Cb²`: no gain, whatever the window;
* `meso_gain_of_exponent_gt_two` — for `θ > 2` and `H → ∞` it tends to `0`;
* `meso_bounded_window_no_gain` — for a *fixed* window height the normalized
  budget is a nonzero constant, so bounded height by itself never produces the
  required `o(L⁶)`.

The conclusion is quantitative and negative for the cheap routes: a
short-interval mean-value input is useful for this programme only if it beats
the trivial count by *more than the square* of the window height.  Nothing here
asserts such an input; the budget is always an explicit hypothesis.

Nothing in this file refers to `ζ`.
-/
import RiemannAnalytic.AnchoredMinorConsumer
import RiemannAnalytic.WeightedGramTarget
import RiemannAnalytic.LocalBudgetScale

namespace RiemannAnalytic

open Finset Filter Topology

/-! ### The anchored observable of the source window -/

/-- The anchored coordinate observable of the one-sided source window: the
`m` squared `2 × 2` coordinate minors through the central grid point. -/
noncomputable def finiteGridAnchorMinorSum (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) : ℝ :=
  coordAnchorMinorSum (reOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1)))
    (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))) 0

theorem finiteGridAnchorMinorSum_nonneg (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) :
    0 ≤ finiteGridAnchorMinorSum φ h α m :=
  coordAnchorMinorSum_nonneg _ _ 0

/-- **The anchored observable is exactly the target signal.**  At the central
grid point the sample of a real even taper is real, so the anchored sum equals
`a₀² ‖b‖²`: the longitudinal weight of the anchor times the whole retained
transverse energy. -/
theorem finiteGridAnchorMinorSum_eq (φ : ℝ → ℝ) (hev : ∀ t, φ (-t) = φ t) (h α : ℝ) (m : ℕ) :
    finiteGridAnchorMinorSum φ h α m
      = (gridSample φ h α 0).re ^ 2
        * (imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
            ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))) := by
  unfold finiteGridAnchorMinorSum
  rw [coordAnchorMinorSum_eq_of_anchor _ _ 0 (imOf_gridVec_head φ hev h α m),
    reOf_gridVec_head φ h α m]

/-- **The anchored observable is dominated by the full window Gram defect** — so
any budget for the window's exterior area is a budget for it. -/
theorem finiteGridAnchorMinorSum_le_gramDefect (φ : ℝ → ℝ) (h α : ℝ) (m : ℕ) :
    finiteGridAnchorMinorSum φ h α m ≤ finiteGridGramDefect φ h α (m + 1) :=
  coordAnchorMinorSum_le_gramDefect _ _ 0

/-- **The anchored observable carries the whole source floor.**

For a `C¹`, nonnegative, real even taper with plateau half-width `a ≥ 3L/8`,
grid spacing `h = 2π/L` and window length `m ≥ 1`,

    `(9/16) L² ((9/512) L⁴ α² − C_φ(α)²/(h² m)) ≤ ∑_{k ≠ 0} (a₀ b_k)²`.

The zero-side detector therefore needs only the anchored minors: the reduction
from `O(q²)` pair minors to `q − 1` is lossless. -/
theorem anchoredMinorSum_source_floor {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m))
      ≤ finiteGridAnchorMinorSum φ (2 * Real.pi / L) α m := by
  set h := 2 * Real.pi / L with hh
  have ha0 : 0 ≤ a := by linarith
  set B := imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1))
      ⬝ᵥ imOf (gridVec φ h (-(Complex.I * (α : ℂ))) (m + 1)) with hB
  have hval := finiteGridAnchorMinorSum_eq φ hev h α m
  have hhead : 9 / 16 * L ^ 2 ≤ (gridSample φ h α 0).re ^ 2 := by
    have h4 := gridRealEnergyLower hφ.toCompactTaper hnn ha0 hplat h α
    nlinarith [ha, hL.le]
  have hBlow : 9 / 512 * L ^ 4 * α ^ 2
      - derivMass φ α ^ 2 / (h ^ 2 * m) ≤ B := by
    have hwin : L / 4 * taperExcess φ α
        - derivMass φ α ^ 2 / (h ^ 2 * m) ≤ B := imOf_gridVec_lower hφ hev hL h2R α hm
    have hexc := taperExcess_ge_plateau_quadratic hφ.toCompactTaper ha0 hplat α
    have hcube : (3 * L / 8) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by positivity) ha 3
    have hkey : 9 / 128 * L ^ 3 * α ^ 2 ≤ taperExcess φ α := by
      have hstep : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 ≤ 4 / 3 * a ^ 3 * α ^ 2 := by
        nlinarith [sq_nonneg α, hcube]
      have hvaleq : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 = 9 / 128 * L ^ 3 * α ^ 2 := by ring
      linarith
    have hfloor : 9 / 512 * L ^ 4 * α ^ 2 ≤ L / 4 * taperExcess φ α := by
      nlinarith [hkey, hL.le]
    linarith
  have hBnn : 0 ≤ B := by
    rw [hB, imOf_dotProduct_self]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hval, ← hB]
  nlinarith [hhead, hBlow, hBnn, sq_nonneg L, sq_nonneg (gridSample φ h α 0).re]

/-! ### The anchored budget and the tube it buys -/

/-- The anchored form of `source_floor_family`: the anchored observable of each
member of a family obeys the quadratic floor at the constant `(81/16384) L⁶`. -/
theorem anchored_floor_family {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {m : ℕ} (hm : 1 ≤ m)
    {ι : Type*} {s : Finset ι} (offset : ι → ℝ)
    (htail : ∀ i ∈ s, derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * offset i ^ 2) :
    ∀ i ∈ s, 81 / 16384 * L ^ 6 * offset i ^ 2
      ≤ finiteGridAnchorMinorSum φ (2 * Real.pi / L) (offset i) m := by
  intro i hi
  have hfloor := anchoredMinorSum_source_floor hφ hev hnn hL h2R ha hplat (offset i) hm
  have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
  have hstep : 81 / 16384 * L ^ 6 * offset i ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * offset i ^ 2
        - derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    nlinarith [htail i hi, hL2]
  linarith

/-- **The tube from an anchored budget.**  A prime-side bound on the *anchored*
weighted sum — the `O(q)` minors through the central grid point, not the `O(q²)`
of the full exterior observable — already confines every member of the family:

    `∑_ρ m_ρ² · a₀(ρ)² ‖b_ρ‖² ≤ E   ⟹   |α_ρ| ≤ √(E / ((81/16384) L⁶))`.

This is the exact shape the short-window arithmetic theorem should target. -/
theorem anchored_budget_tube {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {m : ℕ} (hm : 1 ≤ m)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (offset mult : ι → ℝ)
    (htail : ∀ i ∈ s, derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * offset i ^ 2)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2) {E : ℝ}
    (hbudget : weightedGramSum s mult
        (fun i => finiteGridAnchorMinorSum φ (2 * Real.pi / L) (offset i) m) ≤ E)
    {i : ι} (hi : i ∈ s) :
    |offset i| ≤ Real.sqrt (E / (81 / 16384 * L ^ 6)) := by
  have hc : (0 : ℝ) < 81 / 16384 * L ^ 6 := by positivity
  exact abs_offset_le_of_budget hc
    (anchored_floor_family hφ hev hnn hL h2R ha hplat hm offset htail) hmult hbudget hi

/-! ### The window-height scaling calculus -/

/-- The generic local budget for a mesoscopic window of height `H`: local count
`A·H·L`, per-vector energy `Cb·L²`, with an arithmetic saving `H^θ`. -/
noncomputable def mesoBudget (A Cb L H θ : ℝ) : ℝ :=
  localNormCountBudget (A * (H * L)) (Cb * L ^ 2) / H ^ θ

/-- **The normalized mesoscopic budget.**  `mesoBudget / L⁶ = 2A²Cb²·H^{2−θ}`:
the window height enters with the *positive* exponent `2` from the zero count,
against the arithmetic saving `θ`. -/
theorem mesoBudget_ratio_eq {A Cb L H θ : ℝ} (hL : L ≠ 0) (hH : 0 < H) :
    mesoBudget A Cb L H θ / L ^ 6 = 2 * A ^ 2 * Cb ^ 2 * H ^ ((2 : ℝ) - θ) := by
  have hsub : H ^ ((2 : ℝ) - θ) = H ^ (2 : ℝ) / H ^ θ := Real.rpow_sub hH 2 θ
  have hnat : H ^ (2 : ℝ) = H ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hHθ : H ^ θ ≠ 0 := (Real.rpow_pos_of_pos hH θ).ne'
  unfold mesoBudget localNormCountBudget
  rw [hsub, hnat]
  field_simp

/-- **No gain below the critical exponent.**  If the arithmetic saving is at most
the square of the window height, then for every window with `H ≥ 1` the
normalized budget stays at least `2A²Cb²`: it is never `o(L⁶)`. -/
theorem meso_no_gain_of_exponent_le_two {A Cb L H θ : ℝ} (hL : L ≠ 0) (hH : 1 ≤ H)
    (hθ : θ ≤ 2) :
    2 * A ^ 2 * Cb ^ 2 ≤ mesoBudget A Cb L H θ / L ^ 6 := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  rw [mesoBudget_ratio_eq hL hH0]
  have hpow : (1 : ℝ) ≤ H ^ ((2 : ℝ) - θ) := Real.one_le_rpow hH (by linarith)
  nlinarith [sq_nonneg A, sq_nonneg Cb, sq_nonneg (A * Cb)]

/-- **A bounded window height gives no gain at all.**  For a fixed height the
normalized budget is a nonzero constant, so it does not tend to zero: the
required `o(L⁶)` cannot come from the choice of window. -/
theorem meso_bounded_window_no_gain {A Cb H θ : ℝ} (hA : A ≠ 0) (hCb : Cb ≠ 0) (hH : 0 < H)
    {L : ℝ → ℝ} (hL : ∀ᶠ T in atTop, L T ≠ 0) :
    ¬ Tendsto (fun T => mesoBudget A Cb (L T) H θ / L T ^ 6) atTop (𝓝 0) := by
  intro hten
  have hconst : Tendsto (fun _ : ℝ => 2 * A ^ 2 * Cb ^ 2 * H ^ ((2 : ℝ) - θ)) atTop (𝓝 0) := by
    refine hten.congr' ?_
    filter_upwards [hL] with T hT
    exact mesoBudget_ratio_eq hT hH
  have hlim : (0 : ℝ) = 2 * A ^ 2 * Cb ^ 2 * H ^ ((2 : ℝ) - θ) :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  have hpos : (0 : ℝ) < 2 * A ^ 2 * Cb ^ 2 * H ^ ((2 : ℝ) - θ) := by
    have h1 : (0 : ℝ) < A ^ 2 := by positivity
    have h2 : (0 : ℝ) < Cb ^ 2 := by positivity
    have h3 : (0 : ℝ) < H ^ ((2 : ℝ) - θ) := Real.rpow_pos_of_pos hH _
    positivity
  linarith

/-- **Above the critical exponent the window does give the gain.**  If the
arithmetic saving beats the square of the window height, `θ > 2`, and the window
height grows, the normalized budget tends to zero — the criterion the tube
theorem consumes. -/
theorem meso_gain_of_exponent_gt_two {A Cb θ : ℝ} (hθ : 2 < θ) {L H : ℝ → ℝ}
    (hL : ∀ᶠ T in atTop, L T ≠ 0) (hHpos : ∀ᶠ T in atTop, 0 < H T)
    (hH : Tendsto H atTop atTop) :
    Tendsto (fun T => mesoBudget A Cb (L T) (H T) θ / L T ^ 6) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T => 2 * A ^ 2 * Cb ^ 2 * H T ^ ((2 : ℝ) - θ)) atTop (𝓝 0) := by
    have hrpow : Tendsto (fun T => H T ^ ((2 : ℝ) - θ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x ^ (-(θ - 2))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have heq : (fun x : ℝ => x ^ (-(θ - 2))) = fun x : ℝ => x ^ ((2 : ℝ) - θ) := by
        funext x
        rw [show -(θ - 2) = (2 : ℝ) - θ by ring]
      rw [heq] at h1
      exact h1.comp hH
    simpa using hrpow.const_mul (2 * A ^ 2 * Cb ^ 2)
  refine hbase.congr' ?_
  filter_upwards [hL, hHpos] with T hT hHT
  exact (mesoBudget_ratio_eq hT hHT).symm

end RiemannAnalytic
