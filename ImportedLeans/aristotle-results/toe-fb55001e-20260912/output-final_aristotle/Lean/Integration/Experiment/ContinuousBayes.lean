import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 6, lane 2 — Bayes over a continuous parameter

`TOE_STAGE5_INFERENCE.md` frontier item 1 records the gap closed here:

> **Bayes stops at the finite family.**  `posterior` is over a `Fintype`; there
> is no continuous prior, no posterior *density* over the parameter regions of
> the continuous lane …

This file supplies the density version, over a compact parameter interval, with
no measure theory beyond Mathlib's interval integral:

```
π(θ ∣ y) = L(y ∣ θ) π(θ) / ∫_a^b L(y ∣ ϑ) π(ϑ) dϑ
```

and — the point of the exercise — the *same* bridge back to the set-valued core
that the finite version has, so the architecture is preserved rather than
replaced:

```
supp π(· ∣ y) ⊆ Θ_y.
```

## What is proved

The update:

* `evidence_nonneg`, `evidence_pos_of_pos_on` — the normalising constant, and
  when it is positive;
* `posterior_nonneg`, `posterior_integral_eq_one` — the posterior is a genuine
  probability density on `[a,b]`: nonnegative and of total mass one;
* `posterior_pos_iff` — its support is exactly `{π > 0} ∩ {L > 0}`, the density
  analogue of the finite support identity;
* `zero_prior_stays_zero` — a parameter excluded a priori is never revived;
* `bayes_ratio` — the division-free Bayes factor: posterior odds are prior odds
  times the likelihood ratio;
* `flat_likelihood_leaves_the_prior` — data that cannot discriminate changes
  nothing;
* `update` and `sequential_is_batch` — the posterior is itself a prior (the
  structure is closed under updating) and updating twice equals updating once on
  the product likelihood;
* `no_posterior_of_total_refutation` — a likelihood vanishing on the whole
  interval has zero evidence, so there is no posterior at all.

The bridge:

* `posterior_support_subset_compatible` — **the support of the posterior density
  lies inside the surviving parameter region** `Θ_E` of
  `Integration.Experiment.ParameterRegion`, under the same bounded-noise
  hypothesis as the finite bridge.

The negative:

* `region_does_not_determine_the_posterior` — two priors with the same support
  and the same likelihood give different posterior densities, so a region
  determines no weights.  `possibility ≠ probability`, in the continuous case.

## What is *not* claimed

The parameter is one-dimensional and the prior is a density against Lebesgue
measure on a compact interval; there is no general measure-theoretic prior, no
improper prior, no conjugacy theory, no asymptotics and no consistency.  A
posterior density here carries **no** coverage statement: see
`Integration.Experiment.CoverageSemantics` for what would be needed.
-/

namespace Integration.Experiment.ContinuousBayes

open Set MeasureTheory
open Integration.Experiment.ParameterRegion

/-! ## §1 A prior density on a compact parameter interval -/

/-- **A continuous prior**: a nonnegative density on a compact parameter
interval integrating to one. -/
structure ParamPrior where
  /-- Left endpoint of the parameter interval. -/
  lo : ℝ
  /-- Right endpoint of the parameter interval. -/
  hi : ℝ
  /-- The interval is nondegenerate as an interval (possibly a point). -/
  hlo : lo ≤ hi
  /-- The prior density. -/
  density : ℝ → ℝ
  /-- A density is nonnegative. -/
  nonneg : ∀ θ, 0 ≤ density θ
  /-- It integrates to one over the parameter interval. -/
  total : ∫ θ in lo..hi, density θ = 1

variable (P : ParamPrior) (L : ℝ → ℝ)

/-- **The evidence** (marginal likelihood) `∫_a^b L(θ) π(θ) dθ`. -/
noncomputable def evidence : ℝ := ∫ θ in P.lo..P.hi, L θ * P.density θ

/-- **Bayes' rule for densities.** -/
noncomputable def posterior (θ : ℝ) : ℝ := L θ * P.density θ / evidence P L

theorem evidence_nonneg (hL : ∀ θ, 0 ≤ L θ) : 0 ≤ evidence P L :=
  intervalIntegral.integral_nonneg P.hlo (fun θ _ => mul_nonneg (hL θ) (P.nonneg θ))

theorem posterior_nonneg (hL : ∀ θ, 0 ≤ L θ) (θ : ℝ) : 0 ≤ posterior P L θ :=
  div_nonneg (mul_nonneg (hL θ) (P.nonneg θ)) (evidence_nonneg P L hL)

/-- **The posterior is a probability density**: it integrates to one over the
parameter interval, whenever there is any evidence at all. -/
theorem posterior_integral_eq_one (h : evidence P L ≠ 0) :
    ∫ θ in P.lo..P.hi, posterior P L θ = 1 := by
  simp only [posterior]
  rw [intervalIntegral.integral_div]
  exact div_self h

/-- **The support identity**: a parameter carries posterior mass exactly when it
carries prior mass and the data are possible under it. -/
theorem posterior_pos_iff (hL : ∀ θ, 0 ≤ L θ) (hev : 0 < evidence P L) (θ : ℝ) :
    0 < posterior P L θ ↔ 0 < L θ ∧ 0 < P.density θ := by
  rw [posterior, div_pos_iff]
  constructor
  · rintro (⟨hnum, _⟩ | ⟨_, hneg⟩)
    · have h1 : L θ ≠ 0 := by intro h; rw [h] at hnum; simp at hnum
      have h2 : P.density θ ≠ 0 := by intro h; rw [h] at hnum; simp at hnum
      exact ⟨lt_of_le_of_ne (hL θ) (Ne.symm h1), lt_of_le_of_ne (P.nonneg θ) (Ne.symm h2)⟩
    · exact absurd hev (not_lt.2 (le_of_lt hneg))
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨mul_pos h1 h2, hev⟩

/-- **No resurrection**: a parameter the prior excludes stays excluded. -/
theorem zero_prior_stays_zero {θ : ℝ} (h : P.density θ = 0) : posterior P L θ = 0 := by
  simp [posterior, h]

/-- **The Bayes factor, division-free**: posterior odds are prior odds times the
likelihood ratio. -/
theorem bayes_ratio (θ ϑ : ℝ) :
    posterior P L θ * (L ϑ * P.density ϑ) = posterior P L ϑ * (L θ * P.density θ) := by
  simp only [posterior, div_mul_eq_mul_div]
  ring_nf

/-- **Data that cannot discriminate change nothing**: a likelihood constant on
the parameter interval leaves the prior density untouched. -/
theorem flat_likelihood_leaves_the_prior {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    posterior P (fun _ => c) θ = P.density θ := by
  have hev : evidence P (fun _ => c) = c := by
    simp only [evidence]
    rw [intervalIntegral.integral_const_mul, P.total, mul_one]
  rw [posterior, hev, mul_comm, mul_div_assoc, div_self (ne_of_gt hc), mul_one]

/-- **A total refutation leaves no posterior**: if the likelihood vanishes on the
whole interval the evidence is zero. -/
theorem no_posterior_of_total_refutation (h : ∀ θ ∈ uIcc P.lo P.hi, L θ = 0) :
    evidence P L = 0 := by
  simp only [evidence]
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
  · simp
  · intro θ hθ
    simp [h θ hθ]

/-! ## §2 The posterior is itself a prior, and updating composes -/

/-- The posterior, packaged as a prior again — so the update is an operation on
the same structure and can be iterated. -/
noncomputable def update (hL : ∀ θ, 0 ≤ L θ) (h : evidence P L ≠ 0) : ParamPrior where
  lo := P.lo
  hi := P.hi
  hlo := P.hlo
  density := posterior P L
  nonneg := posterior_nonneg P L hL
  total := posterior_integral_eq_one P L h

/-- **Sequential updating is batch updating**: conditioning on `L₁` and then on
`L₂` gives the same density as conditioning once on `L₁·L₂`. -/
theorem sequential_is_batch (L₁ L₂ : ℝ → ℝ) (h₁ : ∀ θ, 0 ≤ L₁ θ)
    (he₁ : evidence P L₁ ≠ 0) (hprod : evidence P (fun θ => L₁ θ * L₂ θ) ≠ 0) (θ : ℝ) :
    posterior (update P L₁ h₁ he₁) L₂ θ = posterior P (fun θ => L₁ θ * L₂ θ) θ := by
  have hden : ∀ ϑ, (update P L₁ h₁ he₁).density ϑ = L₁ ϑ * P.density ϑ / evidence P L₁ :=
    fun ϑ => rfl
  have hev : evidence (update P L₁ h₁ he₁) L₂
      = evidence P (fun θ => L₁ θ * L₂ θ) / evidence P L₁ := by
    simp only [evidence, update]
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr (fun ϑ _ => ?_)
    show L₂ ϑ * posterior P L₁ ϑ = L₁ ϑ * L₂ ϑ * P.density ϑ / evidence P L₁
    rw [posterior]
    ring
  rw [posterior, hev, hden, posterior]
  field_simp

/-! ## §3 The bridge to the set-valued core -/

/-- **The bridge**: under the bounded-noise hypothesis — every parameter the
data make possible is a parameter the declared tolerances admit — the support of
the posterior density lies inside the surviving parameter region.

This is the continuous-parameter form of the finite bridge in
`Integration.Experiment.BayesUpdate`: the deterministic region remains the outer
admissibility shell, and the posterior only distributes weight inside it. -/
theorem posterior_support_subset_compatible (F : ParamFamily ℝ) (E : List Reading)
    (hL : ∀ θ, 0 ≤ L θ) (hev : 0 < evidence P L)
    (hprior : ∀ θ, 0 < P.density θ → θ ∈ F.prior)
    (hfit : ∀ θ, 0 < L θ → ∀ r ∈ E, Fits F θ r) :
    {θ | 0 < posterior P L θ} ⊆ Compatible F E := by
  intro θ hθ
  rw [Set.mem_setOf_eq, posterior_pos_iff P L hL hev] at hθ
  exact ⟨hprior θ hθ.2, hfit θ hθ.1⟩

/-! ## §4 The negative: a region carries no weights -/

/-- The uniform prior on `[0,1]`. -/
noncomputable def uniform01 : ParamPrior where
  lo := 0
  hi := 1
  hlo := by norm_num
  density := fun _ => 1
  nonneg := fun _ => by norm_num
  total := by simp

/-- The tilted prior `π(θ) = 1/2 + (3/2)θ²` on `[0,1]`, which has the *same*
support as `uniform01`. -/
noncomputable def tilted01 : ParamPrior where
  lo := 0
  hi := 1
  hlo := by norm_num
  density := fun θ => 1/2 + 3/2 * θ^2
  nonneg := fun θ => by positivity
  total := by
    have hderiv : ∀ x ∈ uIcc (0:ℝ) 1,
        HasDerivAt (fun θ : ℝ => θ/2 + θ^3/2) (1/2 + 3/2 * x^2) x := by
      intro x _
      have h := ((hasDerivAt_id x).div_const 2).add ((hasDerivAt_pow 3 x).div_const 2)
      convert h using 1
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · norm_num
    · exact (continuous_const.add (continuous_const.mul (continuous_pow 2))).intervalIntegrable _ _

/-- **A surviving region determines no weights.**  Two priors with the same
support on the same interval, updated on the same (flat) likelihood, give
different posterior densities.  The continuous form of
`possibility ≠ probability`. -/
theorem region_does_not_determine_the_posterior :
    (∀ θ, 0 < uniform01.density θ ↔ 0 < tilted01.density θ) ∧
      posterior uniform01 (fun _ => 1) 1 ≠ posterior tilted01 (fun _ => 1) 1 := by
  constructor
  · intro θ
    constructor
    · intro _; show (0:ℝ) < 1/2 + 3/2 * θ^2; positivity
    · intro _; show (0:ℝ) < 1; norm_num
  · rw [flat_likelihood_leaves_the_prior uniform01 (by norm_num),
      flat_likelihood_leaves_the_prior tilted01 (by norm_num)]
    norm_num [uniform01, tilted01]

end Integration.Experiment.ContinuousBayes
