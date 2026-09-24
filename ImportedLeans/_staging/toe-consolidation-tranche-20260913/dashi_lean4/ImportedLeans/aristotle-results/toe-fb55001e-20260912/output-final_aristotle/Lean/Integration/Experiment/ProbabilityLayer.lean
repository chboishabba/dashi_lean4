import Mathlib

/-!
# Stage 4, lane 4 — a probability layer, kept separate from the set-valued core

Stages 3 and 4 lanes 1–3 are deliberately **non-probabilistic**: a declared
instrument tolerance `|y_obs - y_pred| ≤ ε` is a rule, not a noise model, and a
prediction envelope is a set of possible values, not a distribution.  This file
adds probability as a *separate enrichment* — "possible worlds + measure" —
rather than retrofitting it onto the existing bookkeeping.

## The objects

* `FinPMF Ω` — a finite probability mass function: nonnegative masses summing
  to one.  This is the smallest honest probabilistic object; nothing here needs
  measure theory.
* `expect`, `variance`, `cov` — `E[X]`, `Var(X)`, `Cov(X,Y)` for
  `X : Ω → ℝ`, proved to satisfy the usual laws.
* `MeasurementModel` — the probabilistic successor of a declared tolerance:
  `Y_obs = h(x) + ε` with `ε` distributed by a `FinPMF`.
* `likelihood m pred y` — `L(h ∣ y) = P(Y = y ∣ h)`.
* `PredictionEnvelope`, `ConfidenceInterval`, `CredibleInterval` — three
  *distinct types*, so the three notions cannot be silently interchanged.

## What is proved

Moments (lane 4, step 1 — "make uncertainty mathematically real"):

* `expect_add`, `expect_const_mul`, `expect_const`, `expect_mono` — linearity
  and monotonicity of expectation;
* `variance_eq_expect_sq_sub`, `variance_nonneg`, `variance_const`;
* `cov_comm`, `cov_self`, `cov_sq_le_variance_mul_variance` (Cauchy–Schwarz);
* `variance_add` — `Var(X+Y) = Var X + Var Y + 2 Cov(X,Y)`.

Measurement semantics (lane 4, step 2 — "from declared tolerance to a
measurement model"), proved *before* any posterior is defined:

* `likelihood_nonneg`, `likelihood_le_one`;
* `likelihood_pos_iff` — a hypothesis has positive likelihood at `y` exactly
  when some positive-mass noise value realises `y`;
* `likelihood_pos_imp_tolerance` — with noise supported in `[-ε, ε]`, positive
  likelihood **implies** tolerance-compatibility: the Stage-3 admissibility
  layer remains valid as a coarsening;
* `tolerance_does_not_imply_positive_likelihood` and
  `tolerance_cannot_rank_hypotheses` — the inclusion is *strict*: tolerance
  compatibility neither implies nor orders likelihood.  Together these are the
  formal content of `tolerance compatibility ⊊ likelihood comparison`.

The claim boundary, made unerasable (the three notions are different types and
are not determined by one another):

* `envelope_confidence_credible_can_all_differ`;
* `credible_is_not_a_function_of_the_envelope`;
* `confidence_is_not_a_function_of_the_envelope`.

## What is *not* claimed

No posterior, no Bayes rule, no asymptotics, and no continuous distributions:
`FinPMF` is finite.  Nothing in the Stage-3/Stage-4 set-valued core imports this
file, so no earlier result silently acquires a probabilistic reading.
-/

namespace Integration.Experiment.Probability

open Finset

/-! ## 1. Finite probability mass functions and their moments -/

/-- A probability mass function on a finite type. -/
structure FinPMF (Ω : Type) [Fintype Ω] where
  /-- The mass assigned to each outcome. -/
  mass : Ω → ℝ
  /-- Masses are nonnegative. -/
  nonneg : ∀ w, 0 ≤ mass w
  /-- Masses sum to one. -/
  total : ∑ w, mass w = 1

namespace FinPMF

variable {Ω : Type} [Fintype Ω] (p : FinPMF Ω)

/-- `E[X]`. -/
def expect (X : Ω → ℝ) : ℝ := ∑ w, p.mass w * X w

/-- `Var(X) = E[(X - E X)²]`. -/
def variance (X : Ω → ℝ) : ℝ := p.expect (fun w => (X w - p.expect X) ^ 2)

/-- `Cov(X,Y) = E[(X - E X)(Y - E Y)]`. -/
def cov (X Y : Ω → ℝ) : ℝ :=
  p.expect (fun w => (X w - p.expect X) * (Y w - p.expect Y))

@[simp] theorem expect_const (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.total]

theorem expect_add (X Y : Ω → ℝ) :
    p.expect (fun w => X w + Y w) = p.expect X + p.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_const_mul (c : ℝ) (X : Ω → ℝ) :
    p.expect (fun w => c * X w) = c * p.expect X := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem expect_sub (X Y : Ω → ℝ) :
    p.expect (fun w => X w - Y w) = p.expect X - p.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mono {X Y : Ω → ℝ} (h : ∀ w, X w ≤ Y w) : p.expect X ≤ p.expect Y :=
  Finset.sum_le_sum fun w _ => by
    exact mul_le_mul_of_nonneg_left (h w) (p.nonneg w)

theorem expect_nonneg {X : Ω → ℝ} (h : ∀ w, 0 ≤ X w) : 0 ≤ p.expect X := by
  simpa using p.expect_mono (X := fun _ => (0 : ℝ)) h

/-- `Var(X) = E[X²] - (E X)²`. -/
theorem variance_eq_expect_sq_sub (X : Ω → ℝ) :
    p.variance X = p.expect (fun w => X w ^ 2) - (p.expect X) ^ 2 := by
  have h : ∀ w, (X w - p.expect X) ^ 2
      = X w ^ 2 + ((-2 * p.expect X) * X w + (p.expect X) ^ 2) := by
    intro w; ring
  calc p.variance X
      = p.expect (fun w => X w ^ 2 + ((-2 * p.expect X) * X w + (p.expect X) ^ 2)) := by
        simp only [variance, h]
    _ = p.expect (fun w => X w ^ 2) - (p.expect X) ^ 2 := by
        rw [p.expect_add, p.expect_add, p.expect_const_mul, p.expect_const]
        ring

theorem variance_nonneg (X : Ω → ℝ) : 0 ≤ p.variance X :=
  p.expect_nonneg fun _ => sq_nonneg _

@[simp] theorem variance_const (c : ℝ) : p.variance (fun _ => c) = 0 := by
  simp [variance]

theorem cov_comm (X Y : Ω → ℝ) : p.cov X Y = p.cov Y X := by
  simp only [cov, expect]
  exact Finset.sum_congr rfl fun w _ => by ring

@[simp] theorem cov_self (X : Ω → ℝ) : p.cov X X = p.variance X := by
  simp only [cov, variance, sq]

theorem variance_add (X Y : Ω → ℝ) :
    p.variance (fun w => X w + Y w)
      = p.variance X + p.variance Y + 2 * p.cov X Y := by
  have hE : p.expect (fun w => X w + Y w) = p.expect X + p.expect Y := p.expect_add X Y
  have key : ∀ w, (X w + Y w - p.expect (fun w => X w + Y w)) ^ 2
      = ((X w - p.expect X) ^ 2 + (Y w - p.expect Y) ^ 2)
        + 2 * ((X w - p.expect X) * (Y w - p.expect Y)) := by
    intro w; rw [hE]; ring
  simp only [variance, cov, key]
  rw [p.expect_add, p.expect_add, p.expect_const_mul]

/-- Cauchy–Schwarz for covariance. -/
theorem cov_sq_le_variance_mul_variance (X Y : Ω → ℝ) :
    (p.cov X Y) ^ 2 ≤ p.variance X * p.variance Y := by
  have hsq : ∀ w, Real.sqrt (p.mass w) * Real.sqrt (p.mass w) = p.mass w := fun w =>
    Real.mul_self_sqrt (p.nonneg w)
  have main : ∀ u v : Ω → ℝ, p.expect (fun w => u w * v w)
      = ∑ w, (Real.sqrt (p.mass w) * u w) * (Real.sqrt (p.mass w) * v w) := by
    intro u v
    simp only [expect]
    refine Finset.sum_congr rfl fun w _ => ?_
    linear_combination (-(u w * v w)) * hsq w
  set f : Ω → ℝ := fun w => Real.sqrt (p.mass w) * (X w - p.expect X) with hf
  set g : Ω → ℝ := fun w => Real.sqrt (p.mass w) * (Y w - p.expect Y) with hg
  have hcov : p.cov X Y = ∑ w, f w * g w :=
    main (fun w => X w - p.expect X) (fun w => Y w - p.expect Y)
  have hX : p.variance X = ∑ w, f w ^ 2 := by
    have := main (fun w => X w - p.expect X) (fun w => X w - p.expect X)
    simpa [variance, sq] using this
  have hY : p.variance Y = ∑ w, g w ^ 2 := by
    have := main (fun w => Y w - p.expect Y) (fun w => Y w - p.expect Y)
    simpa [variance, sq] using this
  rw [hcov, hX, hY]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

end FinPMF

/-! ## 2. Measurement models and likelihood

The probabilistic successor of the declared tolerance `|y_obs - y_pred| ≤ ε`:

```
Y_obs = h(x) + ε,     ε ~ P_ε.
```

The semantics of the measurement model is developed here on its own, *before*
any posterior or model weighting; the only comparison made with the Stage-3
tolerance layer is the inclusion `positive likelihood ⇒ tolerance-compatible`
for boundedly supported noise, and its strictness.
-/

/-- A finite additive measurement-noise model: a distribution on an abstract
outcome type together with the error each outcome contributes. -/
structure MeasurementModel (Ω : Type) [Fintype Ω] where
  /-- The noise distribution. -/
  noise : FinPMF Ω
  /-- The additive error realised by each outcome. -/
  err : Ω → ℝ

namespace MeasurementModel

variable {Ω : Type} [Fintype Ω] (m : MeasurementModel Ω)

open scoped Classical in
/-- `L(h ∣ y) = P(Y = y ∣ h)` for the predicted value `pred = h x`. -/
noncomputable def likelihood (pred y : ℝ) : ℝ :=
  ∑ w, if pred + m.err w = y then m.noise.mass w else 0

theorem likelihood_nonneg (pred y : ℝ) : 0 ≤ m.likelihood pred y := by
  classical
  refine Finset.sum_nonneg fun w _ => ?_
  by_cases h : pred + m.err w = y <;> simp [h, m.noise.nonneg w]

theorem likelihood_le_one (pred y : ℝ) : m.likelihood pred y ≤ 1 := by
  classical
  calc m.likelihood pred y ≤ ∑ w, m.noise.mass w := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases h : pred + m.err w = y <;> simp [h, m.noise.nonneg w]
    _ = 1 := m.noise.total

/-- A hypothesis has positive likelihood at `y` exactly when some positive-mass
noise outcome realises `y`. -/
theorem likelihood_pos_iff (pred y : ℝ) :
    0 < m.likelihood pred y ↔ ∃ w, 0 < m.noise.mass w ∧ pred + m.err w = y := by
  classical
  constructor
  · intro hpos
    by_contra hcon
    push_neg at hcon
    have : m.likelihood pred y = 0 := by
      refine Finset.sum_eq_zero fun w _ => ?_
      by_cases h : pred + m.err w = y
      · have : m.noise.mass w ≤ 0 := le_of_not_gt fun hw => (hcon w hw) h
        have : m.noise.mass w = 0 := le_antisymm this (m.noise.nonneg w)
        simp [h, this]
      · simp [h]
    exact absurd this (ne_of_gt hpos)
  · rintro ⟨w, hw, hy⟩
    refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
    · by_cases h : pred + m.err v = y <;> simp [h, m.noise.nonneg v]
    · simpa [hy] using hw

/-- The noise is supported inside `[-ε, ε]`. -/
def BoundedBy (eps : ℝ) : Prop := ∀ w, 0 < m.noise.mass w → |m.err w| ≤ eps

/-- **The Stage-3 tolerance layer survives as a coarsening.**  With noise
supported in `[-ε, ε]`, a hypothesis of positive likelihood is automatically
tolerance-compatible at tolerance `ε`. -/
theorem likelihood_pos_imp_tolerance {eps pred y : ℝ} (hb : m.BoundedBy eps)
    (hpos : 0 < m.likelihood pred y) : |y - pred| ≤ eps := by
  obtain ⟨w, hw, hy⟩ := (m.likelihood_pos_iff pred y).1 hpos
  have : y - pred = m.err w := by linarith [hy]
  rw [this]
  exact hb w hw

/-! ### Strictness of `tolerance compatibility ⊊ likelihood comparison` -/

/-- The two-point noise model with masses `a, 1 - a` and errors `e₀, e₁`. -/
noncomputable def twoPoint (a e₀ e₁ : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1) :
    MeasurementModel Bool where
  noise :=
    { mass := fun b => cond b a (1 - a)
      nonneg := by
        intro b
        cases b
        · show (0 : ℝ) ≤ 1 - a
          linarith
        · exact h₀
      total := by
        rw [Fintype.sum_bool]
        show a + (1 - a) = 1
        ring }
  err := fun b => cond b e₀ e₁

@[simp] theorem twoPoint_likelihood (a e₀ e₁ : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1)
    (pred y : ℝ) :
    (twoPoint a e₀ e₁ h₀ h₁).likelihood pred y
      = (if pred + e₀ = y then a else 0) + (if pred + e₁ = y then 1 - a else 0) := by
  classical
  rw [likelihood, Fintype.sum_bool]
  rfl

/-- **Tolerance compatibility does not imply positive likelihood.**  A reading
can sit inside the declared tolerance and still be impossible under the
measurement model: the tolerance layer is strictly coarser. -/
theorem tolerance_does_not_imply_positive_likelihood :
    ∃ (m : MeasurementModel Bool) (eps pred y : ℝ),
      m.BoundedBy eps ∧ |y - pred| ≤ eps ∧ m.likelihood pred y = 0 := by
  refine ⟨twoPoint (1/2) 1 (-1) (by norm_num) (by norm_num), 1, 0, 1/2, ?_, ?_, ?_⟩
  · intro w _; cases w <;> norm_num [twoPoint]
  · norm_num
  · norm_num

/-- **Tolerance compatibility cannot rank hypotheses.**  Two predictions can be
equally tolerance-compatible with the same reading while the measurement model
assigns them different likelihoods.  This is why likelihood is a genuine
refinement and not a restatement of Stage 3. -/
theorem tolerance_cannot_rank_hypotheses :
    ∃ (m : MeasurementModel Bool) (eps pred₁ pred₂ y : ℝ),
      m.BoundedBy eps ∧ |y - pred₁| ≤ eps ∧ |y - pred₂| ≤ eps ∧
        m.likelihood pred₂ y < m.likelihood pred₁ y := by
  refine ⟨twoPoint (3/4) 0 1 (by norm_num) (by norm_num), 1, 0, -1, 0, ?_, ?_, ?_, ?_⟩
  · intro w _; cases w <;> norm_num [twoPoint]
  · norm_num
  · norm_num
  · norm_num

end MeasurementModel

/-! ## 3. The claim boundary: envelope ≠ confidence ≠ credible

Three theorems, each saying that one of the three notions carries information
the others do not, so that no implementation can quietly substitute one for
another.
-/

/-- **A measure is strictly more information than a set of possible values.**
There is no function of the set of attainable values that returns the mean:
the prediction envelope of Stages 3–4 simply does not determine any
probabilistic summary. -/
theorem measure_is_not_determined_by_the_possible_values :
    ¬ ∃ F : Set ℝ → ℝ, ∀ (p : FinPMF Bool) (X : Bool → ℝ),
        F (Set.range X) = p.expect X := by
  rintro ⟨F, hF⟩
  set X : Bool → ℝ := fun b => cond b 1 0 with hX
  let p₁ : FinPMF Bool :=
    { mass := fun b => cond b 1 0
      nonneg := by intro b; cases b <;> norm_num
      total := by rw [Fintype.sum_bool]; norm_num }
  let p₂ : FinPMF Bool :=
    { mass := fun b => cond b 0 1
      nonneg := by intro b; cases b <;> norm_num
      total := by rw [Fintype.sum_bool]; norm_num }
  have h₁ : F (Set.range X) = 1 := by
    rw [hF p₁ X, FinPMF.expect, Fintype.sum_bool]; norm_num [p₁, hX]
  have h₂ : F (Set.range X) = 0 := by
    rw [hF p₂ X, FinPMF.expect, Fintype.sum_bool]; norm_num [p₂, hX]
  rw [h₁] at h₂
  norm_num at h₂

open scoped Classical in
/-- Posterior-style mass of a set of values under a pmf. -/
noncomputable def massOf {Ω : Type} [Fintype Ω] (p : FinPMF Ω) (X : Ω → ℝ) (S : Set ℝ) : ℝ :=
  p.expect (fun w => if X w ∈ S then 1 else 0)

/-- **A credible set can sit strictly inside the prediction envelope.**  The
envelope reports everything the family can produce; a credible set reports only
enough of it to carry the declared mass.  So the two are different objects even
when computed from the same model. -/
theorem credible_can_be_strictly_inside_the_envelope :
    ∃ (p : FinPMF Bool) (X : Bool → ℝ) (S : Set ℝ),
      S ⊂ Set.range X ∧ (9 : ℝ)/10 ≤ massOf p X S := by
  refine ⟨{ mass := fun b => cond b (19/20) (1/20)
            nonneg := by intro b; cases b <;> norm_num
            total := by rw [Fintype.sum_bool]; norm_num },
          fun b => cond b 1 0, {1}, ?_, ?_⟩
  · constructor
    · rintro x rfl; exact ⟨true, by norm_num⟩
    · intro hsub
      have : (0 : ℝ) ∈ ({1} : Set ℝ) := hsub ⟨false, by norm_num⟩
      norm_num at this
  · rw [massOf, FinPMF.expect, Fintype.sum_bool]
    norm_num

open scoped Classical in
/-- Coverage of a value `θ` by an interval-valued procedure. -/
noncomputable def coverage {Ω : Type} [Fintype Ω] (p : FinPMF Ω)
    (proc : Ω → Set ℝ) (θ : ℝ) : ℝ :=
  p.expect (fun w => if θ ∈ proc w then 1 else 0)

/-- **Coverage is a property of the procedure, not of the reported interval.**
Two procedures can report the very same interval on the observed outcome and
still have different coverage, so a confidence level can never be read off the
interval that was reported — in particular it is not a property of a prediction
envelope. -/
theorem coverage_is_not_a_property_of_the_reported_interval :
    ∃ (p : FinPMF Bool) (proc₁ proc₂ : Bool → Set ℝ) (θ : ℝ) (w : Bool),
      proc₁ w = proc₂ w ∧ coverage p proc₁ θ ≠ coverage p proc₂ θ := by
  refine ⟨{ mass := fun _ => 1/2
            nonneg := by intro _; norm_num
            total := by rw [Fintype.sum_bool]; norm_num },
          fun _ => Set.univ, fun b => cond b Set.univ ∅, 0, true, rfl, ?_⟩
  simp only [coverage, FinPMF.expect, Fintype.sum_bool, Set.mem_univ, if_true,
    Bool.cond_true, Bool.cond_false, Set.mem_empty_iff_false, if_false]
  norm_num

end Integration.Experiment.Probability
