/-
**G9.1 / G9.2 — the anchored determinant sees only the *transverse* motion.**

G8 left the translated-taper lane hanging on a single exponent: the ledger of
`AnchoredShiftLedger.lean` closes the anchored observable at `o(L⁶)` as soon as
the translate family obeys a shift bound `‖v_j − v₀‖ ≤ Mc·L^k·|jh|` with
`k ≤ 1`, and is useless for `k ≥ 2`.  The point of this file is that `k` is the
wrong exponent to be asking about: the anchored determinant is blind to motion
*parallel* to the anchor, so the quantity that actually enters the ledger is the
displacement **modulo the anchor line**.

Exact algebra, no estimates:

* `wedgeSq x w = ‖x‖²‖w‖² − ⟪x,w⟫²` — the two-vector anchored determinant;
* `wedgeSq_eq_normSq_mul_transverseSq` — `wedgeSq x w = ‖x‖²‖P_{x^⊥}w‖²`, with
  `transverseComp x w = w − (⟪x,w⟫/‖x‖²)·x` the literal orthogonal component;
* `anchorMinor_eq_normSq_mul_transverseSq` — hence, for a family,

      `Δ(v i₀, v j) = ‖v i₀‖² ‖P_{v i₀^⊥}(v j − v i₀)‖²`   (an identity),

  which is the sharp form of the displacement bound of `AnchoredRowVariance`:
  the parallel part of the displacement contributes exactly nothing;
* `differentialAnchorMinor` — the differential form asked for in G9:

      `lim_{s→0} Δ(v₀, v s)/s² = ‖v₀‖² ‖P_{v₀^⊥}v'₀‖²`,

  for any family differentiable at `0`; and `differentialAnchorMinor_exact`,
  the exact statement `Δ(x, x + s•w) = s²·‖x‖²‖P_{x^⊥}w‖²` with no remainder at
  all for a linear family.

Consequences for the ledger:

* `anchorMinorSum_le_transverse_budget`, `anchorMinorSum_grid_transverse_budget`,
  `anchoredMinorSum_source_transverse_budget` — the whole `AnchoredShiftLedger`
  chain, but driven by the transverse constant `M⊥` instead of the raw shift
  constant `M`.  Since `transverseComp_norm_le` gives `M⊥ ≤ M` always, this
  ledger is never worse and is the one that must be evaluated.
* `transverse_exponent_ge_of_wedge_fraction` — and the decision rule in the
  negative direction: if the family retains a *fixed fraction* `κ > 0` of its
  derivative energy transversally, then `‖P_{v₀^⊥}v'₀‖ ≥ √κ‖v'₀‖`, so no power
  of `L` is saved by passing from `k` to `k⊥`.  This is the criterion that
  `TransverseGridVariance.lean` then evaluates for the actual grid family.

Nothing here refers to `ζ`; nothing here is assumed.
-/
import RiemannAnalytic.AnchoredShiftLedger

namespace RiemannAnalytic

open Finset

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The wedge of a pair and its transverse form -/

/-- The two-vector anchored determinant `‖x‖²‖w‖² − ⟪x,w⟫²`. -/
def wedgeSq (x w : E) : ℝ := ‖x‖ ^ 2 * ‖w‖ ^ 2 - ⟪x, w⟫_ℝ ^ 2

theorem wedgeSq_nonneg (x w : E) : 0 ≤ wedgeSq x w := by
  have := sq_real_inner_le x w
  unfold wedgeSq
  linarith

@[simp] theorem wedgeSq_zero_right (x : E) : wedgeSq x 0 = 0 := by simp [wedgeSq]

/-- The wedge is quadratically homogeneous in its second slot. -/
theorem wedgeSq_smul_right (x w : E) (c : ℝ) : wedgeSq x (c • w) = c ^ 2 * wedgeSq x w := by
  unfold wedgeSq
  rw [norm_smul, real_inner_smul_right]
  simp [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The component of `w` orthogonal to the anchor `x`. -/
noncomputable def transverseComp (x w : E) : E := w - (⟪x, w⟫_ℝ / ‖x‖ ^ 2) • x

/-- The transverse component is genuinely orthogonal to the anchor. -/
theorem inner_transverseComp (x w : E) (hx : x ≠ 0) : ⟪x, transverseComp x w⟫_ℝ = 0 := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  unfold transverseComp
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **The wedge is the transverse energy.**  `‖x‖²‖w‖² − ⟪x,w⟫² = ‖x‖²‖P_{x^⊥}w‖²`. -/
theorem wedgeSq_eq_normSq_mul_transverseSq (x w : E) (hx : x ≠ 0) :
    wedgeSq x w = ‖x‖ ^ 2 * ‖transverseComp x w‖ ^ 2 := by
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by
    have : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
    positivity
  have hnorm : ‖transverseComp x w‖ ^ 2
      = ‖w‖ ^ 2 - 2 * (⟪x, w⟫_ℝ / ‖x‖ ^ 2) * ⟪x, w⟫_ℝ
        + (⟪x, w⟫_ℝ / ‖x‖ ^ 2) ^ 2 * ‖x‖ ^ 2 := by
    unfold transverseComp
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm w x]
    ring
  rw [hnorm]
  unfold wedgeSq
  field_simp
  ring

/-- The transverse component never exceeds the vector itself. -/
theorem transverseComp_norm_le (x w : E) : ‖transverseComp x w‖ ≤ ‖w‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [transverseComp, hx]
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by
      have : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
      positivity
    have hw := wedgeSq_eq_normSq_mul_transverseSq x w hx
    have hle : ‖x‖ ^ 2 * ‖transverseComp x w‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [← hw]
      unfold wedgeSq
      nlinarith [sq_nonneg (⟪x, w⟫_ℝ)]
    have : ‖transverseComp x w‖ ^ 2 ≤ ‖w‖ ^ 2 := le_of_mul_le_mul_left hle hx2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-! ### The anchored minor of a family, in transverse form -/

/-- The anchored minor is the wedge of the anchor against the displacement. -/
theorem anchorMinor_eq_wedgeSq_shift {n : Type*} (v : n → E) (i₀ j : n) :
    anchorMinor v i₀ j = wedgeSq (v i₀) (v j - v i₀) :=
  anchorMinor_eq_shift v i₀ j

/-- **The exact transverse form of the anchored minor.**  Only the component of
the displacement orthogonal to the anchor contributes:

    `Δ(v i₀, v j) = ‖v i₀‖² ‖P_{v i₀^⊥}(v j − v i₀)‖²`. -/
theorem anchorMinor_eq_normSq_mul_transverseSq {n : Type*} (v : n → E) (i₀ j : n)
    (h0 : v i₀ ≠ 0) :
    anchorMinor v i₀ j
      = ‖v i₀‖ ^ 2 * ‖transverseComp (v i₀) (v j - v i₀)‖ ^ 2 := by
  rw [anchorMinor_eq_wedgeSq_shift, wedgeSq_eq_normSq_mul_transverseSq _ _ h0]

/-! ### The differential form -/

/-- **The exact differential anchored minor for a linear family.**  Along the
straight family `s ↦ x + s•w` the anchored determinant is *exactly* quadratic,
with coefficient the transverse energy — there is no `O(s³)` remainder. -/
theorem differentialAnchorMinor_exact (x w : E) (s : ℝ) :
    ‖x‖ ^ 2 * ‖x + s • w‖ ^ 2 - ⟪x, x + s • w⟫_ℝ ^ 2 = s ^ 2 * wedgeSq x w := by
  rw [anchorMinorPair_shift x (s • w)]
  show wedgeSq x (s • w) = s ^ 2 * wedgeSq x w
  exact wedgeSq_smul_right x w s

/-- **`DifferentialAnchorMinor`.**  For any family differentiable at the anchor,

    `lim_{s→0} Δ(v₀, v s)/s² = ‖v₀‖²‖P_{v₀^⊥}v'₀‖²`.

This is sharper than `Δ(s) ≤ ‖v₀‖²‖v s − v₀‖²`: the parallel part of the motion
is removed exactly, not estimated. -/
theorem differentialAnchorMinor (V : ℝ → E) (w : E) (hV : HasDerivAt V w 0) :
    Filter.Tendsto (fun s : ℝ => (‖V 0‖ ^ 2 * ‖V s‖ ^ 2 - ⟪V 0, V s⟫_ℝ ^ 2) / s ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (wedgeSq (V 0) w)) := by
  have hslope : Filter.Tendsto (fun s : ℝ => s⁻¹ • (V s - V 0))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds w) := by
    have hs := hasDerivAt_iff_tendsto_slope.1 hV
    have heq : (slope V 0) = fun s : ℝ => s⁻¹ • (V s - V 0) := by
      funext s; simp [slope]
    rwa [heq] at hs
  have hcont : Continuous fun u : E => wedgeSq (V 0) u := by
    unfold wedgeSq
    fun_prop
  have hcomp := (hcont.tendsto w).comp hslope
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  have hstep : V s = V 0 + s • (s⁻¹ • (V s - V 0)) := by
    rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    abel
  have := differentialAnchorMinor_exact (V 0) (s⁻¹ • (V s - V 0)) s
  rw [← hstep] at this
  simp only [Function.comp_apply]
  rw [this]
  field_simp

/-! ### The transverse ledger -/

/-- **The anchored budget driven by the transverse displacement.**  Replacing the
raw shift constant by the transverse one is legitimate because the anchored
minor is *equal* to the transverse energy. -/
theorem anchorMinorSum_le_transverse_budget {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → E) (i₀ : n) {Mp : ℝ} {σ : n → ℝ}
    (hshift : ∀ j, ‖transverseComp (v i₀) (v j - v i₀)‖ ≤ Mp * |σ j|) :
    anchorMinorSum v i₀ ≤ ‖v i₀‖ ^ 2 * (Mp ^ 2 * ∑ j, σ j ^ 2) := by
  classical
  have hterm : ∀ j, anchorMinor v i₀ j ≤ ‖v i₀‖ ^ 2 * (Mp ^ 2 * σ j ^ 2) := by
    intro j
    rcases eq_or_ne (v i₀) 0 with h0 | h0
    · have hz : anchorMinor v i₀ j = 0 := by simp [anchorMinor, h0]
      rw [hz, h0]
      simp
    · rw [anchorMinor_eq_normSq_mul_transverseSq v i₀ j h0]
      have hsq : ‖transverseComp (v i₀) (v j - v i₀)‖ ^ 2 ≤ Mp ^ 2 * σ j ^ 2 := by
        have := hshift j
        nlinarith [norm_nonneg (transverseComp (v i₀) (v j - v i₀)), sq_abs (σ j)]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hsum : anchorMinorSum v i₀ ≤ ∑ j, ‖v i₀‖ ^ 2 * (Mp ^ 2 * σ j ^ 2) := by
    unfold anchorMinorSum
    refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
    intro j _ _
    positivity
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]

/-- The transverse budget on a shift grid of spacing `h` and `q` nodes. -/
theorem anchorMinorSum_grid_transverse_budget {q : ℕ} (v : Fin q → E) (i₀ : Fin q) {Mp h : ℝ}
    (hshift : ∀ j : Fin q,
      ‖transverseComp (v i₀) (v j - v i₀)‖ ≤ Mp * |h * ((j : ℕ) : ℝ)|) :
    anchorMinorSum v i₀ ≤ ‖v i₀‖ ^ 2 * (Mp ^ 2 * (h ^ 2 * (q : ℝ) ^ 3)) := by
  classical
  have hb := anchorMinorSum_le_transverse_budget v i₀
    (σ := fun j : Fin q => h * ((j : ℕ) : ℝ)) hshift
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
  have : Mp ^ 2 * ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ Mp ^ 2 * (h ^ 2 * (q : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hcount (by positivity)
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **`transverseShiftMinorBound`.**  The source-scaled ledger with the
transverse exponent: anchor energy `Cv L²`, transverse constant `Mp·L^k`,
spacing `2π/L`, count `≤ A₀HL`, giving `shiftBudgetScale Cv Mp A₀ k L H`.  The
hypothesis is now on `P_{v₀^⊥}(v j − v₀)`, which is what the determinant sees. -/
theorem anchoredMinorSum_source_transverse_budget {q : ℕ} (v : Fin q → E) (i₀ : Fin q)
    {Cv Mp A0 L H : ℝ} {k : ℕ} (hL : 0 < L)
    (hv : ‖v i₀‖ ^ 2 ≤ Cv * L ^ 2)
    (hshift : ∀ j : Fin q, ‖transverseComp (v i₀) (v j - v i₀)‖
      ≤ Mp * L ^ k * |2 * Real.pi / L * ((j : ℕ) : ℝ)|)
    (hq : (q : ℝ) ≤ A0 * H * L) :
    anchorMinorSum v i₀ ≤ shiftBudgetScale Cv Mp A0 k L H := by
  have hbase := anchorMinorSum_grid_transverse_budget v i₀ hshift
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hcube : (q : ℝ) ^ 3 ≤ (A0 * H * L) ^ 3 := pow_le_pow_left₀ hq0 hq 3
  have hsp : (2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3
      ≤ (2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have hstep : ‖v i₀‖ ^ 2 * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3))
      ≤ (Cv * L ^ 2) * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := by
    have hinner : (Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)
        ≤ (Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3) :=
      mul_le_mul_of_nonneg_left hsp (by positivity)
    have hnn : (0 : ℝ) ≤ (Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3) := by
      positivity
    have hv0 : (0 : ℝ) ≤ ‖v i₀‖ ^ 2 := by positivity
    calc ‖v i₀‖ ^ 2 * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3))
        ≤ (Cv * L ^ 2) * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_right hv hnn
      _ ≤ (Cv * L ^ 2) * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := by
          refine mul_le_mul_of_nonneg_left hinner ?_
          nlinarith [hv0, hv]
  have hfinal : (Cv * L ^ 2) * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3))
      = shiftBudgetScale Cv Mp A0 k L H := by
    unfold shiftBudgetScale
    have hLne : L ≠ 0 := ne_of_gt hL
    field_simp
    ring
  calc anchorMinorSum v i₀
      ≤ ‖v i₀‖ ^ 2 * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)) := hbase
    _ ≤ (Cv * L ^ 2) * ((Mp * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := hstep
    _ = shiftBudgetScale Cv Mp A0 k L H := hfinal

/-! ### Reading the transverse exponent -/

/-- **The transverse ledger is never worse than the raw one.**  A raw
shift-Lipschitz hypothesis implies the transverse one with the same constant, so
`k⊥ ≤ k` always. -/
theorem transverse_shift_le_of_shift {n : Type*} (v : n → E) (i₀ j : n) {M s : ℝ}
    (h : ‖v j - v i₀‖ ≤ M * |s|) :
    ‖transverseComp (v i₀) (v j - v i₀)‖ ≤ M * |s| :=
  le_trans (transverseComp_norm_le _ _) h

/-- **The decision rule, negative direction.**  If the family keeps a fixed
fraction `κ > 0` of its derivative energy transverse to the anchor, then the
transverse derivative is comparable to the full derivative, so the transverse
exponent equals the raw one: `‖P_{x^⊥}w‖ ≥ √κ ‖w‖`.  In that case the passage
`k ↦ k⊥` saves no power of `L`, and the `k ≤ 1` branch of the ledger is
unavailable. -/
theorem transverse_exponent_ge_of_wedge_fraction (x w : E) (hx : x ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ)
    (hfrac : κ * (‖x‖ ^ 2 * ‖w‖ ^ 2) ≤ wedgeSq x w) :
    Real.sqrt κ * ‖w‖ ≤ ‖transverseComp x w‖ := by
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by
    have : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
    positivity
  rw [wedgeSq_eq_normSq_mul_transverseSq x w hx] at hfrac
  have hsq : κ * ‖w‖ ^ 2 ≤ ‖transverseComp x w‖ ^ 2 :=
    le_of_mul_le_mul_left (by linarith : ‖x‖ ^ 2 * (κ * ‖w‖ ^ 2)
      ≤ ‖x‖ ^ 2 * ‖transverseComp x w‖ ^ 2) hx2
  have hnn : 0 ≤ Real.sqrt κ * ‖w‖ := by positivity
  have : (Real.sqrt κ * ‖w‖) ^ 2 ≤ ‖transverseComp x w‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hκ]
    exact hsq
  exact (pow_le_pow_iff_left₀ hnn (norm_nonneg _) two_ne_zero).1 this

/-- **The decision rule, positive direction.**  Conversely a transverse fraction
bound `‖P_{x^⊥}w‖ ≤ ε‖w‖` is exactly a wedge bound `wedgeSq x w ≤ ε²‖x‖²‖w‖²`:
the anchored determinant is small precisely when the motion is nearly parallel
to the anchor. -/
theorem wedgeSq_le_of_transverse_fraction (x w : E) {ε : ℝ}
    (h : ‖transverseComp x w‖ ≤ ε * ‖w‖) :
    wedgeSq x w ≤ ε ^ 2 * (‖x‖ ^ 2 * ‖w‖ ^ 2) := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [wedgeSq, hx]
  · rw [wedgeSq_eq_normSq_mul_transverseSq x w hx]
    have hsq : ‖transverseComp x w‖ ^ 2 ≤ ε ^ 2 * ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg (transverseComp x w), norm_nonneg w]
    nlinarith [sq_nonneg ‖x‖, norm_nonneg x]

end RiemannAnalytic
