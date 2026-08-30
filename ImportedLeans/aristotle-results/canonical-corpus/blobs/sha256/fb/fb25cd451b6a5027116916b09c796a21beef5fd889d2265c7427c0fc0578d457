import Mathlib
import Integration.Experiment.ProbabilityLayer
import Integration.Experiment.ParameterRegion

/-!
# Stage 5, lane 1 — Bayes update, and the bridge to the set-valued core

`TOE_STAGE4_INFERENCE.md` frontier item 1 records exactly two gaps in the
probability layer:

> There is no prior, no posterior, no Bayes rule, no model weighting … Nothing
> connects the likelihood to the parameter regions of lane 1 (there is no
> probabilistic analogue of `Compatible`).

This file closes both, and keeps the two layers honestly apart.

## The update

For a finite hypothesis family `H`:

* `evidence p lik` — the normalising constant `∑_h π(h) L(h)`;
* `posterior p lik hnn hpos` — Bayes' rule, `π(h)L(h) / ∑ π L`, returned as a
  genuine `FinPMF` (its masses are proved nonnegative and proved to sum to one,
  so no result below depends on an unnormalised weight).

Proved about it:

| Theorem | Content |
|---|---|
| `posterior_mass` | the update formula |
| `evidence_pos_iff` | an update is possible exactly when some hypothesis has both positive prior and positive likelihood |
| `posterior_pos_iff` | the posterior support is exactly `prior support ∩ likelihood support` |
| `zero_prior_stays_zero` | a hypothesis excluded a priori is never revived by data |
| `bayes_factor` | the posterior odds are the prior odds times the likelihood ratio (division-free form) |
| `posterior_mono` | equal priors and ordered likelihoods give ordered posteriors |
| `sequential_is_batch` | updating on `L₁` then `L₂` equals updating once on `L₁·L₂` |
| `flat_likelihood_leaves_the_prior` | data that cannot discriminate changes nothing — the probabilistic form of the Stage-3 negative `data_cannot_separate_identical_traces` |
| `posterior_concentrates` | if exactly one hypothesis survives, the posterior is its point mass |
| `no_posterior_of_total_refutation` | if every likelihood vanishes there is no posterior at all: `refutation_is_total`, probabilistically |

## The bridge

`jointLikelihood` is the product of the per-reading likelihoods of
`Integration.Experiment.Probability.MeasurementModel`, evaluated along the
predictions of a `ParamFamily` (`Integration.Experiment.ParameterRegion`).

| Theorem | Content |
|---|---|
| `jointLikelihood_pos_iff_all_pos` | a positive joint likelihood is positive on every reading |
| `positive_joint_likelihood_fits` | with noise bounded by each reading's declared tolerance, positive likelihood implies the reading is *fitted* in the Stage-4 sense |
| `posterior_support_subset_compatible` | **the bridge**: the posterior's support is contained in the surviving parameter region `Θ_E` |
| `posterior_support_subset_compatible_cons` | the same, reading by reading |
| `falsified_family_has_no_posterior` | if the family is falsified the evidence is zero, so no posterior exists |

and the two negatives that stop the bridge being read as an identification of
the layers:

| Theorem | Content |
|---|---|
| `compatible_does_not_determine_the_posterior` | two priors with the same surviving region and the same likelihood give different posteriors: a region carries no weight |
| `posterior_support_can_be_strictly_smaller` | a parameter can be tolerance-compatible and still have zero posterior mass, so the inclusion is strict |

## What is still not claimed

No asymptotics, no consistency, no continuous prior (the update is over a
`Fintype`), no decision theory, and no coverage statement: a posterior is not a
confidence procedure, and the three separation theorems of
`Integration.Experiment.ProbabilityLayer` are untouched.  Nothing in the
set-valued core imports this file, so no earlier region acquires a
probabilistic reading.
-/

namespace Integration.Experiment.Bayes

open Finset
open Integration.Experiment.Probability
open Integration.Experiment.ParameterRegion

/-! ## §1 The update -/

variable {H : Type} [Fintype H]

/-- The **evidence** (marginal likelihood) `∑_h π(h) L(h)`. -/
def evidence (p : FinPMF H) (lik : H → ℝ) : ℝ := ∑ h, p.mass h * lik h

theorem evidence_nonneg (p : FinPMF H) {lik : H → ℝ} (hnn : ∀ h, 0 ≤ lik h) :
    0 ≤ evidence p lik :=
  Finset.sum_nonneg fun h _ => mul_nonneg (p.nonneg h) (hnn h)

/-- An update is possible exactly when some hypothesis has both positive prior
mass and positive likelihood. -/
theorem evidence_pos_iff (p : FinPMF H) {lik : H → ℝ} (hnn : ∀ h, 0 ≤ lik h) :
    0 < evidence p lik ↔ ∃ h, 0 < p.mass h ∧ 0 < lik h := by
  constructor
  · intro hpos
    by_contra hcon
    push_neg at hcon
    have : evidence p lik = 0 := by
      refine Finset.sum_eq_zero fun h _ => ?_
      rcases lt_or_eq_of_le (p.nonneg h) with hp | hp
      · have : lik h ≤ 0 := hcon h hp
        have : lik h = 0 := le_antisymm this (hnn h)
        simp [this]
      · simp [← hp]
    exact absurd this (ne_of_gt hpos)
  · rintro ⟨h, hp, hl⟩
    refine Finset.sum_pos' (fun v _ => mul_nonneg (p.nonneg v) (hnn v))
      ⟨h, Finset.mem_univ h, mul_pos hp hl⟩

/-- **Bayes' rule.**  The posterior is a genuine probability mass function. -/
noncomputable def posterior (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) : FinPMF H where
  mass := fun h => p.mass h * lik h / evidence p lik
  nonneg := fun h => div_nonneg (mul_nonneg (p.nonneg h) (hnn h)) (le_of_lt hpos)
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

@[simp] theorem posterior_mass (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) (h : H) :
    (posterior p lik hnn hpos).mass h = p.mass h * lik h / evidence p lik := rfl

/-- **The posterior support is exactly the intersection of the two supports.** -/
theorem posterior_pos_iff (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) (h : H) :
    0 < (posterior p lik hnn hpos).mass h ↔ 0 < p.mass h ∧ 0 < lik h := by
  rw [posterior_mass, div_pos_iff_of_pos_right hpos]
  constructor
  · intro hm
    rcases lt_or_eq_of_le (p.nonneg h) with hp | hp
    · refine ⟨hp, lt_of_le_of_ne (hnn h) fun heq => ?_⟩
      rw [← heq, mul_zero] at hm
      exact lt_irrefl 0 hm
    · exact absurd hm (by simp [← hp])
  · rintro ⟨h1, h2⟩; exact mul_pos h1 h2

/-- **No resurrection.**  A hypothesis given zero prior mass has zero posterior
mass, whatever the data say. -/
theorem zero_prior_stays_zero (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) {h : H} (hz : p.mass h = 0) :
    (posterior p lik hnn hpos).mass h = 0 := by
  simp [hz]

/-- **Posterior odds = prior odds × likelihood ratio**, in division-free form. -/
theorem bayes_factor (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) (h₁ h₂ : H) :
    (posterior p lik hnn hpos).mass h₁ * (p.mass h₂ * lik h₂)
      = (posterior p lik hnn hpos).mass h₂ * (p.mass h₁ * lik h₁) := by
  simp only [posterior_mass]
  field_simp

/-- Equal priors and ordered likelihoods give ordered posteriors. -/
theorem posterior_mono (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) {h₁ h₂ : H}
    (hp : p.mass h₁ = p.mass h₂) (hl : lik h₁ ≤ lik h₂) :
    (posterior p lik hnn hpos).mass h₁ ≤ (posterior p lik hnn hpos).mass h₂ := by
  have hnum : p.mass h₁ * lik h₁ ≤ p.mass h₂ * lik h₂ := by
    rw [hp]; exact mul_le_mul_of_nonneg_left hl (p.nonneg h₂)
  simp only [posterior_mass]
  gcongr

/-- **Sequential updating is batch updating.**  Conditioning on `L₁` and then on
`L₂` gives the same posterior as conditioning once on the product `L₁·L₂`. -/
theorem sequential_is_batch (p : FinPMF H) (l₁ l₂ : H → ℝ)
    (h₁ : ∀ h, 0 ≤ l₁ h) (h₂ : ∀ h, 0 ≤ l₂ h)
    (hp₁ : 0 < evidence p l₁)
    (hp₂ : 0 < evidence (posterior p l₁ h₁ hp₁) l₂)
    (hp₁₂ : 0 < evidence p (fun h => l₁ h * l₂ h)) :
    (posterior (posterior p l₁ h₁ hp₁) l₂ h₂ hp₂).mass
      = (posterior p (fun h => l₁ h * l₂ h)
          (fun h => mul_nonneg (h₁ h) (h₂ h)) hp₁₂).mass := by
  have hZ : evidence (posterior p l₁ h₁ hp₁) l₂
      = evidence p (fun h => l₁ h * l₂ h) / evidence p l₁ := by
    simp only [evidence, posterior_mass, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun h _ => by ring
  funext h
  simp only [posterior_mass, hZ]
  field_simp

/-- **Data that cannot discriminate changes nothing.**  A likelihood constant
across the family leaves the prior exactly as it was — the probabilistic form of
the Stage-3 negative `data_cannot_separate_identical_traces`. -/
theorem flat_likelihood_leaves_the_prior (p : FinPMF H) {c : ℝ} (hc : 0 < c)
    (hnn : ∀ h, 0 ≤ (fun _ : H => c) h) (hpos : 0 < evidence p (fun _ => c)) :
    (posterior p (fun _ => c) hnn hpos).mass = p.mass := by
  have hZ : evidence p (fun _ : H => c) = c := by
    simp only [evidence, ← Finset.sum_mul, p.total, one_mul]
  funext h
  rw [posterior_mass, hZ]
  field_simp

/-- **The posterior concentrates.**  If a single hypothesis carries all the
surviving weight, the posterior is its point mass. -/
theorem posterior_concentrates [DecidableEq H] (p : FinPMF H) (lik : H → ℝ)
    (hnn : ∀ h, 0 ≤ lik h) (hpos : 0 < evidence p lik) {h₀ : H}
    (hsole : ∀ h, h ≠ h₀ → p.mass h * lik h = 0) :
    (posterior p lik hnn hpos).mass = fun h => if h = h₀ then 1 else 0 := by
  have hZ : evidence p lik = p.mass h₀ * lik h₀ := by
    rw [evidence, Finset.sum_eq_single h₀ (fun h _ hne => hsole h hne)]
    intro hcon
    exact absurd (Finset.mem_univ h₀) hcon
  funext h
  by_cases hh : h = h₀
  · subst hh
    rw [posterior_mass, hZ, div_self (by rw [← hZ]; exact ne_of_gt hpos), if_pos rfl]
  · rw [posterior_mass, hsole h hh, if_neg hh, zero_div]

/-- **Refutation is total, probabilistically.**  If every hypothesis has zero
likelihood there is no posterior at all: the evidence vanishes and Bayes' rule
is undefined.  The failure is at the level of the model family. -/
theorem no_posterior_of_total_refutation (p : FinPMF H) {lik : H → ℝ}
    (hzero : ∀ h, lik h = 0) : evidence p lik = 0 := by
  simp [evidence, hzero]

/-! ## §2 The bridge to the surviving parameter region

The set-valued core admits a parameter when its prediction sits inside every
reading's declared tolerance.  The probabilistic layer weights a parameter by
the product of its per-reading likelihoods.  The two are related — in one
direction, and strictly.
-/

variable {Ω : Type} [Fintype Ω]

/-- The **joint likelihood** of a parameter: the product of the per-reading
likelihoods of the observed values under the family's predictions. -/
noncomputable def jointLikelihood {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (E : List Reading) (θ : Θ) : ℝ :=
  (E.map (fun r => m.likelihood (F.predict θ r.time) r.value)).prod

theorem jointLikelihood_nonneg {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (E : List Reading) (θ : Θ) :
    0 ≤ jointLikelihood m F E θ := by
  refine List.prod_nonneg ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨r, _, rfl⟩ := hx
  exact m.likelihood_nonneg _ _

@[simp] theorem jointLikelihood_nil {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (θ : Θ) : jointLikelihood m F [] θ = 1 := by
  simp [jointLikelihood]

@[simp] theorem jointLikelihood_cons {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (r : Reading) (E : List Reading) (θ : Θ) :
    jointLikelihood m F (r :: E) θ
      = m.likelihood (F.predict θ r.time) r.value * jointLikelihood m F E θ := by
  simp [jointLikelihood]

/-- A positive joint likelihood is positive on every reading. -/
theorem jointLikelihood_pos_iff_all_pos {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (E : List Reading) (θ : Θ) :
    0 < jointLikelihood m F E θ ↔
      ∀ r ∈ E, 0 < m.likelihood (F.predict θ r.time) r.value := by
  induction E with
  | nil => simp
  | cons r E ih =>
      rw [jointLikelihood_cons]
      constructor
      · intro hpos s hs
        have hl : 0 < m.likelihood (F.predict θ r.time) r.value := by
          rcases lt_or_eq_of_le (m.likelihood_nonneg (F.predict θ r.time) r.value) with h | h
          · exact h
          · rw [← h] at hpos; simp at hpos
        have hrest : 0 < jointLikelihood m F E θ := by
          by_contra hcon
          push_neg at hcon
          have : jointLikelihood m F E θ = 0 :=
            le_antisymm hcon (jointLikelihood_nonneg m F E θ)
          rw [this, mul_zero] at hpos
          exact absurd rfl (ne_of_gt hpos)
        rcases List.mem_cons.1 hs with rfl | hs'
        · exact hl
        · exact (ih.1 hrest) s hs'
      · intro hall
        exact mul_pos (hall r (List.mem_cons_self ..))
          (ih.2 fun s hs => hall s (List.mem_cons_of_mem _ hs))

/-- **Positive likelihood implies the reading is fitted.**  With the noise
supported inside each reading's declared tolerance, a parameter of positive
likelihood is admissible in the Stage-4 set-valued sense. -/
theorem positive_joint_likelihood_fits {Θ : Type} (m : MeasurementModel Ω)
    (F : ParamFamily Θ) (E : List Reading) (θ : Θ)
    (hb : ∀ r ∈ E, m.BoundedBy r.tol)
    (hpos : 0 < jointLikelihood m F E θ) :
    ∀ r ∈ E, Fits F θ r := by
  intro r hr
  exact m.likelihood_pos_imp_tolerance (hb r hr)
    ((jointLikelihood_pos_iff_all_pos m F E θ).1 hpos r hr)

/-- **The bridge.**  The posterior's support sits inside the surviving parameter
region: every parameter with positive posterior mass is compatible with all the
evidence, provided the prior is supported in the declared prior region and the
noise is bounded by each reading's declared tolerance. -/
theorem posterior_support_subset_compatible {Θ : Type} [Fintype Θ]
    (m : MeasurementModel Ω) (F : ParamFamily Θ) (E : List Reading)
    (p : FinPMF Θ) (hprior : ∀ θ, 0 < p.mass θ → θ ∈ F.prior)
    (hb : ∀ r ∈ E, m.BoundedBy r.tol)
    (hpos : 0 < evidence p (jointLikelihood m F E)) (θ : Θ)
    (hmass : 0 < (posterior p (jointLikelihood m F E)
      (jointLikelihood_nonneg m F E) hpos).mass θ) :
    θ ∈ Compatible F E := by
  obtain ⟨hp, hl⟩ := (posterior_pos_iff p _ (jointLikelihood_nonneg m F E) hpos θ).1 hmass
  exact ⟨hprior θ hp, positive_joint_likelihood_fits m F E θ hb hl⟩

/-- The bridge, reading by reading: adding a reading can only remove posterior
support, and what it removes is exactly what the tolerance test removes. -/
theorem posterior_support_subset_compatible_cons {Θ : Type} [Fintype Θ]
    (m : MeasurementModel Ω) (F : ParamFamily Θ) (r : Reading) (E : List Reading)
    (θ : Θ) (hb : m.BoundedBy r.tol)
    (hpos : 0 < jointLikelihood m F (r :: E) θ) :
    Fits F θ r ∧ 0 < jointLikelihood m F E θ := by
  refine ⟨m.likelihood_pos_imp_tolerance hb
      ((jointLikelihood_pos_iff_all_pos m F (r :: E) θ).1 hpos r (List.mem_cons_self ..)), ?_⟩
  exact (jointLikelihood_pos_iff_all_pos m F E θ).2 fun s hs =>
    (jointLikelihood_pos_iff_all_pos m F (r :: E) θ).1 hpos s (List.mem_cons_of_mem _ hs)

/-- **A falsified family has no posterior.**  If no parameter of the prior
region survives the evidence, the marginal likelihood is zero and Bayes' rule
does not apply: the probabilistic layer inherits the set-valued layer's typed
model-family failure rather than silently renormalising. -/
theorem falsified_family_has_no_posterior {Θ : Type} [Fintype Θ]
    (m : MeasurementModel Ω) (F : ParamFamily Θ) (E : List Reading)
    (p : FinPMF Θ) (hprior : ∀ θ, 0 < p.mass θ → θ ∈ F.prior)
    (hb : ∀ r ∈ E, m.BoundedBy r.tol)
    (hfals : FamilyFalsified F E) :
    evidence p (jointLikelihood m F E) = 0 := by
  refine Finset.sum_eq_zero fun θ _ => ?_
  rcases lt_or_eq_of_le (p.nonneg θ) with hp | hp
  · have hl : jointLikelihood m F E θ = 0 := by
      by_contra hne
      have hlpos : 0 < jointLikelihood m F E θ :=
        lt_of_le_of_ne (jointLikelihood_nonneg m F E θ) (Ne.symm hne)
      have : θ ∈ Compatible F E :=
        ⟨hprior θ hp, positive_joint_likelihood_fits m F E θ hb hlpos⟩
      rw [hfals] at this
      exact this
    simp [hl]
  · simp [← hp]

/-! ## §3 The two negatives: the layers do not collapse -/

/-- A trivial one-parameter family whose prediction is constant, used as a
carrier on which the surviving region is the whole prior. -/
def flatFamily (c : ℝ) : ParamFamily Bool where
  prior := Set.univ
  predict := fun _ _ => c

/-- **A surviving region carries no weight.**  Two priors with the *same*
surviving parameter region and the *same* likelihood have different posteriors,
so the set-valued layer does not determine the probabilistic one. -/
theorem compatible_does_not_determine_the_posterior :
    ∃ (F : ParamFamily Bool) (E : List Reading) (p q : FinPMF Bool)
      (lik : Bool → ℝ) (hnn : ∀ b, 0 ≤ lik b)
      (hp : 0 < evidence p lik) (hq : 0 < evidence q lik),
      Compatible F E = Set.univ ∧
      (∀ b, 0 < p.mass b ↔ 0 < q.mass b) ∧
      (posterior p lik hnn hp).mass ≠ (posterior q lik hnn hq).mass := by
  classical
  refine ⟨flatFamily 0, [],
    ⟨fun b => cond b (1/2) (1/2), ?_, ?_⟩,
    ⟨fun b => cond b (1/4) (3/4), ?_, ?_⟩,
    fun _ => 1, fun _ => zero_le_one, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> norm_num
  · rw [Fintype.sum_bool]; norm_num
  · intro b; cases b <;> norm_num
  · rw [Fintype.sum_bool]; norm_num
  · rw [evidence, Fintype.sum_bool]; norm_num
  · rw [evidence, Fintype.sum_bool]; norm_num
  · ext θ; simp [Compatible, flatFamily]
  · intro b; cases b <;> norm_num
  · intro hcon
    have h := congrFun hcon true
    simp only [posterior_mass, evidence, Fintype.sum_bool] at h
    norm_num at h

/-- **The inclusion is strict.**  A parameter can sit inside the declared
tolerance — hence survive in the set-valued region — and still have zero
likelihood, hence zero posterior mass.  The probabilistic layer is genuinely
finer than the tolerance layer. -/
theorem posterior_support_can_be_strictly_smaller :
    ∃ (m : MeasurementModel Bool) (F : ParamFamily Bool) (r : Reading) (θ : Bool),
      m.BoundedBy r.tol ∧ Fits F θ r ∧ jointLikelihood m F [r] θ = 0 := by
  refine ⟨MeasurementModel.twoPoint (1/2) 1 (-1) (by norm_num) (by norm_num),
    flatFamily 0, ⟨0, 1/2, 1, by norm_num⟩, true, ?_, ?_, ?_⟩
  · intro w _; cases w <;> norm_num [MeasurementModel.twoPoint]
  · show |(1/2 : ℝ) - 0| ≤ 1
    rw [sub_zero, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  · rw [jointLikelihood]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    show (MeasurementModel.twoPoint (1/2) 1 (-1) _ _).likelihood
      (flatFamily 0 |>.predict true 0) (1/2) = 0
    rw [MeasurementModel.twoPoint_likelihood]
    norm_num [flatFamily]

end Integration.Experiment.Bayes
