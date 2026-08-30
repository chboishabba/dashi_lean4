/-
**The exterior observable `e₂` and its transport from trace data.**

`HigherTraceMinors.lean` proves that the total pairwise transverse area of a
family is `(tr G)² − tr G²`, so the second Frobenius moment alone carries it
with the wrong sign.  The positive object is therefore the elementary symmetric
combination

    e₂(G) = ½ ((tr G)² − tr G²) = ∑_{i<j} ‖vᵢ ∧ vⱼ‖²  ≥ 0,

which is *baseline-free*: no critical configuration has to be invented and
subtracted by hand, the cancellation happens inside the trace combination.

This file develops `e₂` as a scalar functional of a pair of trace values and
proves the transport theorems that turn asymptotic information about `tr G` and
`tr G²` into asymptotic information about `e₂(G)`:

* `e2OfTraces t₁ t₂ = (t₁² − t₂)/2`, with `e2OfTraces_gram_eq` identifying it
  with the total (unordered) pairwise exterior area of a Gram family and
  `e2OfTraces_gram_nonneg` proving it nonnegative there;
* `EvBound`, the explicit `O(·)`-with-named-constants interface
  (`∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |f T| ≤ C · g T`);
* `evBound_e2_of_traces`: **the adapter.**  From a first-trace bound
  `tr G = m₁(1 + O(𝓔))` and a second-trace bound `tr G² = m₂(1 + O(𝓔))` — the
  two shapes in which a prime-side trace theorem delivers its conclusions — it
  produces `e₂ = (m₁² − m₂)/2 + O(𝓔 (m₁² + m₂))`.  No prime input is assumed:
  the two trace bounds are hypotheses of the theorem;
* `evBound_e2_of_ratio`: the same in the ratio normalisation
  `(tr G)²/tr G² = F·N(1 + O(𝓔))`, giving
  `e₂ = ½ tr G² (F·N − 1) + O(𝓔 · tr G² · F·N)`;
* `e2OfTraces_sub_le` / `e2OfTraces_le_add_tail`: the exact perturbation
  estimate for `e₂` under a change of the two traces — the transport of `e₂`
  along `G = A + E`.

Every statement is an implication from explicitly stated trace hypotheses.
Nothing here asserts a trace bound for the zeros of `ζ`.
-/
import RiemannAnalytic.HigherTraceMinors

namespace RiemannAnalytic

open Filter Topology

/-! ### The exterior observable -/

/-- The second elementary symmetric function of the eigenvalues, written in the
first two power traces: `e₂ = ½ ((tr G)² − tr G²)`. -/
noncomputable def e2OfTraces (t₁ t₂ : ℝ) : ℝ := (t₁ ^ 2 - t₂) / 2

theorem e2OfTraces_def (t₁ t₂ : ℝ) : e2OfTraces t₁ t₂ = (t₁ ^ 2 - t₂) / 2 := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped InnerProductSpace

/-- Cauchy–Schwarz in squared form. -/
theorem sq_real_inner_le (x y : E) : ⟪x, y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := abs_real_inner_le_norm x y
  have h0 : 0 ≤ |⟪x, y⟫_ℝ| := abs_nonneg _
  have hn : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  calc ⟪x, y⟫_ℝ ^ 2 = |⟪x, y⟫_ℝ| ^ 2 := (sq_abs _).symm
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := by nlinarith
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring

/-- **`e₂` of a Gram matrix is the total pairwise exterior area.**

`e₂(G) = ½ ∑_{i,j} (‖vᵢ‖²‖vⱼ‖² − ⟪vᵢ,vⱼ⟫²)`, i.e. the sum over unordered pairs
of the squared areas `‖vᵢ ∧ vⱼ‖²`. -/
theorem e2OfTraces_gram_eq {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    e2OfTraces (Matrix.gram ℝ v).trace ((Matrix.gram ℝ v * Matrix.gram ℝ v).trace)
      = (∑ i, ∑ j, (‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2)) / 2 := by
  rw [e2OfTraces_def, sum_pair_gramDefect_eq v]

/-- `e₂` of a Gram matrix is nonnegative: it is a sum of squared areas. -/
theorem e2OfTraces_gram_nonneg {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    0 ≤ e2OfTraces (Matrix.gram ℝ v).trace ((Matrix.gram ℝ v * Matrix.gram ℝ v).trace) := by
  rw [e2OfTraces_gram_eq v]
  have : 0 ≤ ∑ i, ∑ j, (‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      have := sq_real_inner_le (v i) (v j); linarith
  linarith

/-- The ratio normalisation: `e₂ = ½ t₂ ((t₁²/t₂) − 1)`. -/
theorem e2OfTraces_eq_half_mul_ratio_sub_one {t₁ t₂ : ℝ} (h : t₂ ≠ 0) :
    e2OfTraces t₁ t₂ = t₂ * (t₁ ^ 2 / t₂ - 1) / 2 := by
  rw [e2OfTraces_def]
  field_simp

/-! ### The explicit `O(·)` interface -/

/-- Explicit big-`O` on a neighbourhood of `+∞` with a positive named constant:
`EvBound f g ↔ ∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |f T| ≤ C · g T`.  This is the shape in
which quantitative trace theorems state their error terms. -/
def EvBound (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → |f T| ≤ C * g T

theorem EvBound.mono {f g h : ℝ → ℝ} (hb : EvBound f g)
    (hgh : ∀ T, g T ≤ h T) : EvBound f h := by
  obtain ⟨C, hC, T₀, hT⟩ := hb
  refine ⟨C, hC, T₀, fun T hTT => le_trans (hT T hTT) ?_⟩
  exact mul_le_mul_of_nonneg_left (hgh T) hC.le

/-- An `EvBound` against an error that tends to zero forces the bounded
quantity to tend to zero. -/
theorem EvBound.tendsto_zero {f g : ℝ → ℝ} (hb : EvBound f g)
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨C, hC, T₀, hT⟩ := hb
  have habs : Tendsto (fun T => |f T|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun T => C * g T)
      (Eventually.of_forall fun T => abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop T₀] with T hTT using hT T hTT
    · have := hg.const_mul C
      simpa using this
  exact tendsto_zero_iff_abs_tendsto_zero f |>.2 habs

/-! ### The adapter: trace data to `e₂` -/

/-- **The `e₂` adapter.**

Suppose the two traces of a family obey relative bounds against main terms
`m₁, m₂ ≥ 0` with a common relative error `𝓔 = err`, eventually in `[0,1]`:

    |tr G  − m₁| ≤ C₁ · 𝓔 · m₁,       |tr G² − m₂| ≤ C₂ · 𝓔 · m₂.

Then the exterior observable obeys

    |e₂(tr G, tr G²) − e₂(m₁, m₂)| ≤ C · 𝓔 · (m₁² + m₂),

with `C = (C₁² + 2C₁ + C₂)/2`.  This is the whole content of transporting a
trace theorem to the positive exterior-area observable: no baseline is invented,
and the main term `(m₁² − m₂)/2` is whatever the trace main terms give. -/
theorem evBound_e2_of_traces {tr1 tr2 m1 m2 err : ℝ → ℝ}
    (h1 : EvBound (fun T => tr1 T - m1 T) (fun T => err T * m1 T))
    (h2 : EvBound (fun T => tr2 T - m2 T) (fun T => err T * m2 T))
    (hev : ∀ᶠ T in atTop, 0 ≤ m1 T ∧ 0 ≤ m2 T ∧ 0 ≤ err T ∧ err T ≤ 1) :
    EvBound (fun T => e2OfTraces (tr1 T) (tr2 T) - e2OfTraces (m1 T) (m2 T))
      (fun T => err T * (m1 T ^ 2 + m2 T)) := by
  obtain ⟨C₁, hC₁, T₁, hT₁⟩ := h1
  obtain ⟨C₂, hC₂, T₂, hT₂⟩ := h2
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp hev
  refine ⟨(C₁ ^ 2 + 2 * C₁ + C₂) / 2, by positivity, max (max T₁ T₂) T₃, fun T hT => ?_⟩
  have hb1 := hT₁ T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)
  have hb2 := hT₂ T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
  obtain ⟨hm1T, hm2T, herr0T, herr1T⟩ := hT₃ T (le_trans (le_max_right _ _) hT)
  simp only at hb1 hb2 ⊢
  set x := tr1 T - m1 T with hx
  set y := tr2 T - m2 T with hy
  set a := m1 T with ha
  set b := m2 T with hb
  set e := err T with he
  have ha0 : 0 ≤ a := hm1T
  have hb0 : 0 ≤ b := hm2T
  have he0 : 0 ≤ e := herr0T
  have he1 : e ≤ 1 := herr1T
  obtain ⟨hx1, hx2⟩ := abs_le.mp hb1
  obtain ⟨hy1, hy2⟩ := abs_le.mp hb2
  have hxsq : x ^ 2 ≤ (C₁ * e * a) ^ 2 := by nlinarith [sq_nonneg x, abs_nonneg x, sq_abs x]
  have hesq : e ^ 2 ≤ e := by nlinarith
  have hkey : x ^ 2 ≤ C₁ ^ 2 * e * a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg (C₁ * a)]
  have hxa : x * a ≤ C₁ * e * a ^ 2 := by nlinarith
  have hxa' : -(x * a) ≤ C₁ * e * a ^ 2 := by nlinarith
  have hgoal : e2OfTraces (tr1 T) (tr2 T) - e2OfTraces (m1 T) (m2 T)
      = (x ^ 2 + 2 * (x * a) - y) / 2 := by
    rw [e2OfTraces_def, e2OfTraces_def, hx, hy, ha, hb]
    ring
  rw [hgoal]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [mul_nonneg he0 (sq_nonneg a), mul_nonneg he0 hb0, sq_nonneg x,
      mul_nonneg (mul_nonneg hC₂.le he0) hb0, mul_nonneg (mul_nonneg hC₁.le he0) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg C₁) he0) (sq_nonneg a)]
  · nlinarith [mul_nonneg he0 (sq_nonneg a), mul_nonneg he0 hb0, sq_nonneg x,
      mul_nonneg (mul_nonneg hC₂.le he0) hb0, mul_nonneg (mul_nonneg hC₁.le he0) (sq_nonneg a),
      mul_nonneg (mul_nonneg (sq_nonneg C₁) he0) (sq_nonneg a)]

/-- **The `e₂` adapter in ratio form.**

If the trace ratio obeys `|(tr G)²/tr G² − R| ≤ C · 𝓔 · R` with `R = F·N` the
ratio main term, and `tr G² ≥ 0`, then

    |e₂ − ½ tr G² (R − 1)| ≤ (C/2) · 𝓔 · (tr G² · R).

This is the normalisation in which a trace theorem that controls the *ratio*
`(tr G)²/tr G²` — rather than the two traces separately — delivers the exterior
observable. -/
theorem evBound_e2_of_ratio {tr1 tr2 R err : ℝ → ℝ}
    (h : EvBound (fun T => tr1 T ^ 2 / tr2 T - R T) (fun T => err T * R T))
    (h2pos : ∀ᶠ T in atTop, 0 < tr2 T) :
    EvBound (fun T => e2OfTraces (tr1 T) (tr2 T) - tr2 T * (R T - 1) / 2)
      (fun T => err T * (tr2 T * R T)) := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp h2pos
  refine ⟨C / 2, by positivity, max T₀ T₁, fun T hTT => ?_⟩
  have hb := hT T (le_trans (le_max_left _ _) hTT)
  simp only at hb ⊢
  have hpos := hT₁ T (le_trans (le_max_right _ _) hTT)
  have hid : e2OfTraces (tr1 T) (tr2 T) - tr2 T * (R T - 1) / 2
      = tr2 T / 2 * (tr1 T ^ 2 / tr2 T - R T) := by
    rw [e2OfTraces_def]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ tr2 T / 2)]
  calc tr2 T / 2 * |tr1 T ^ 2 / tr2 T - R T|
      ≤ tr2 T / 2 * (C * (err T * R T)) := by
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C / 2 * (err T * (tr2 T * R T)) := by ring

/-! ### Perturbation of `e₂` -/

/-- **Exact perturbation estimate for `e₂`.**  A change of the two traces moves
`e₂` by at most

    ½ (|t₁ − s₁| (|t₁| + |s₁|) + |t₂ − s₂|).

This is the transport of the exterior observable along a perturbation
`G = A + E` of the underlying matrix, expressed purely in the trace data. -/
theorem e2OfTraces_sub_le (t₁ t₂ s₁ s₂ : ℝ) :
    |e2OfTraces t₁ t₂ - e2OfTraces s₁ s₂|
      ≤ (|t₁ - s₁| * (|t₁| + |s₁|) + |t₂ - s₂|) / 2 := by
  have hid : e2OfTraces t₁ t₂ - e2OfTraces s₁ s₂
      = ((t₁ - s₁) * (t₁ + s₁) - (t₂ - s₂)) / 2 := by
    rw [e2OfTraces_def, e2OfTraces_def]; ring
  rw [hid, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have h1 : |(t₁ - s₁) * (t₁ + s₁) - (t₂ - s₂)|
      ≤ |(t₁ - s₁) * (t₁ + s₁)| + |t₂ - s₂| := abs_sub _ _
  have h2 : |(t₁ - s₁) * (t₁ + s₁)| ≤ |t₁ - s₁| * (|t₁| + |s₁|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_add_le t₁ s₁) (abs_nonneg _)
  have : |(t₁ - s₁) * (t₁ + s₁) - (t₂ - s₂)| ≤ |t₁ - s₁| * (|t₁| + |s₁|) + |t₂ - s₂| := by
    linarith
  linarith

/-- One-sided form: `e₂` of one trace pair is at most `e₂` of another plus the
explicit tail. -/
theorem e2OfTraces_le_add_tail (t₁ t₂ s₁ s₂ : ℝ) :
    e2OfTraces t₁ t₂ ≤ e2OfTraces s₁ s₂ + (|t₁ - s₁| * (|t₁| + |s₁|) + |t₂ - s₂|) / 2 := by
  have h := e2OfTraces_sub_le t₁ t₂ s₁ s₂
  have := (abs_le.mp h).2
  linarith

end RiemannAnalytic
