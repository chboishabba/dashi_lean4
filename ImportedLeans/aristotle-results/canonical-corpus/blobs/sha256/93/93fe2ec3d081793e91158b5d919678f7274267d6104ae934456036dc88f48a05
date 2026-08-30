import Mathlib
import Integration.Experiment.ProbabilityLayer
import Integration.Experiment.ParameterRegion

/-!
# Stage 6, lane 1 — coverage: what turns an interval into a confidence statement

`TOE_STAGE5_INFERENCE.md` frontier item 2 records the gap closed here:

> **No coverage statement.**  Nothing here attaches a probability to a reported
> interval, and the three separation theorems of the probability layer
> (`envelope ≠ confidence ≠ credible`) still stand unweakened.

This file supplies the missing semantics — a *sampling* model `θ ↦ law θ`, a
set-valued *procedure* `C : Ω → Set Θ`, and the coverage probability

```
coverageProb S C θ  =  P_θ(θ ∈ C(Y))
```

— and keeps the three interval notions apart, as the frontier demands: coverage
is defined for a **procedure**, credible mass for a **posterior**, and an
envelope is a set of possible values.  None of the three is derived from
another, and three negatives below prove that none *can* be.

## What is proved

Basic semantics:

* `coverageProb_nonneg`, `coverageProb_le_one`, `coverageProb_eq_one_iff` — a
  coverage probability is a probability, and equals one exactly when the
  procedure catches `θ` on every outcome the sampling law gives positive mass;
* `coverageProb_mono` — a larger procedure covers at least as often;
* `HasLevel` — the confidence statement `∀ θ, 1 - α ≤ P_θ(θ ∈ C(Y))`, with
  `hasLevel_mono` and `hasLevel_of_le`;
* `coverage_inter_ge` — the Bonferroni bound: intersecting a `1-α` and a `1-β`
  procedure yields level `1-(α+β)`, so two certified procedures compose.

The bridge to the set-valued core — the result that gives the deterministic
admissible region a genuine frequentist reading:

* `toleranceProcedure` — the Stage-4 surviving region `Θ_E` read as a procedure;
* `tolerance_procedure_has_full_coverage` — **under bounded noise the
  deterministic admissible region is a coverage-one procedure**, so
  `possibility ⊆ confidence` in the only direction that is sound;
* `tolerance_procedure_hasLevel` — hence it meets every declared level.

The honest negatives, which stop coverage being read as informativeness or as a
property of the reported set:

* `full_coverage_is_free` — the constant procedure `fun _ => univ` has coverage
  one at every parameter: a level certificate alone says nothing, it must be
  paired with a size statement;
* `credible_mass_is_not_coverage` — a set carrying 95% posterior mass can have
  coverage `0` at a parameter the prior disfavoured;
* `coverage_is_not_credible_mass` — and conversely, a coverage-one procedure can
  report a set of arbitrarily small posterior mass;
* `no_function_from_envelope_to_level` — no function of the reported set returns
  the level, strengthening
  `Probability.coverage_is_not_a_property_of_the_reported_interval` from *two
  procedures* to *no rule whatsoever*.

## What is *not* claimed

No asymptotic coverage, no exact (`= 1-α`) construction, no optimality, no
pivotal quantity, and no continuous sample space: `Ω` is a `Fintype` and the
sampling law is a `FinPMF`.  Coverage here is a finite sum, and no result in
this file licenses reading a Stage-3/4/5 envelope as a confidence set.
-/

namespace Integration.Experiment.CoverageSemantics

open Finset
open Integration.Experiment.Probability
open Integration.Experiment.ParameterRegion

/-! ## §1 Sampling models, procedures and coverage -/

/-- **A sampling model**: for each parameter value, the law of the observation.
This is the object a frequentist statement quantifies over; it is *not* a prior,
and no distribution on `Θ` appears anywhere in this section. -/
structure SamplingModel (Θ Ω : Type) [Fintype Ω] where
  /-- The law of the observation when the parameter is `θ`. -/
  law : Θ → FinPMF Ω

variable {Θ Ω : Type} [Fintype Ω]

open scoped Classical in
/-- **The coverage probability** `P_θ(θ ∈ C(Y))` of a set-valued procedure `C`
at the parameter `θ`. -/
noncomputable def coverageProb (S : SamplingModel Θ Ω) (C : Ω → Set Θ) (θ : Θ) : ℝ :=
  (S.law θ).expect (fun w => if θ ∈ C w then 1 else 0)

theorem coverageProb_nonneg (S : SamplingModel Θ Ω) (C : Ω → Set Θ) (θ : Θ) :
    0 ≤ coverageProb S C θ := by
  classical
  refine FinPMF.expect_nonneg _ (fun w => ?_)
  by_cases h : θ ∈ C w <;> simp [h]

theorem coverageProb_le_one (S : SamplingModel Θ Ω) (C : Ω → Set Θ) (θ : Θ) :
    coverageProb S C θ ≤ 1 := by
  classical
  have h : coverageProb S C θ ≤ (S.law θ).expect (fun _ => 1) := by
    refine FinPMF.expect_mono _ (fun w => ?_)
    by_cases h : θ ∈ C w <;> simp [h]
  simpa [FinPMF.expect, ← Finset.sum_mul, (S.law θ).total] using h

/-- Coverage is one exactly when the procedure catches `θ` on every outcome the
sampling law makes possible. -/
theorem coverageProb_eq_one_iff (S : SamplingModel Θ Ω) (C : Ω → Set Θ) (θ : Θ) :
    coverageProb S C θ = 1 ↔ ∀ w, 0 < (S.law θ).mass w → θ ∈ C w := by
  classical
  constructor
  · intro h w hw
    by_contra hmem
    have hlt : coverageProb S C θ < 1 := by
      have key : ∑ v, (S.law θ).mass v * (if θ ∈ C v then (1:ℝ) else 0)
          < ∑ v, (S.law θ).mass v * 1 := by
        refine Finset.sum_lt_sum (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
        · by_cases hv : θ ∈ C v
          · simp [hv]
          · simp [hv, (S.law θ).nonneg v]
        · simp [hmem, hw]
      simpa [coverageProb, FinPMF.expect, ← Finset.sum_mul, (S.law θ).total] using key
    exact absurd h (ne_of_lt hlt)
  · intro h
    have : ∀ v ∈ (Finset.univ : Finset Ω),
        (S.law θ).mass v * (if θ ∈ C v then (1:ℝ) else 0) = (S.law θ).mass v := by
      intro v _
      rcases lt_or_eq_of_le ((S.law θ).nonneg v) with hv | hv
      · simp [h v hv]
      · simp [← hv]
    simp only [coverageProb, FinPMF.expect]
    rw [Finset.sum_congr rfl this, (S.law θ).total]

/-- A procedure that always reports a larger set covers at least as often. -/
theorem coverageProb_mono (S : SamplingModel Θ Ω) {C D : Ω → Set Θ}
    (h : ∀ w, C w ⊆ D w) (θ : Θ) :
    coverageProb S C θ ≤ coverageProb S D θ := by
  classical
  refine FinPMF.expect_mono _ (fun w => ?_)
  by_cases hc : θ ∈ C w
  · simp [hc, h w hc]
  · by_cases hd : θ ∈ D w <;> simp [hc, hd]

/-! ## §2 The confidence statement -/

/-- **A confidence statement**: the procedure catches the true parameter with
probability at least `level`, *whatever the true parameter is*.  This is the
frequentist quantifier order, and it is what distinguishes a confidence region
from a credible region. -/
def HasLevel (S : SamplingModel Θ Ω) (C : Ω → Set Θ) (level : ℝ) : Prop :=
  ∀ θ, level ≤ coverageProb S C θ

/-- Enlarging a procedure preserves its level. -/
theorem hasLevel_mono {S : SamplingModel Θ Ω} {C D : Ω → Set Θ} {level : ℝ}
    (h : ∀ w, C w ⊆ D w) (hC : HasLevel S C level) : HasLevel S D level :=
  fun θ => le_trans (hC θ) (coverageProb_mono S h θ)

/-- A level may always be weakened. -/
theorem hasLevel_of_le {S : SamplingModel Θ Ω} {C : Ω → Set Θ} {l l' : ℝ}
    (hll : l' ≤ l) (hC : HasLevel S C l) : HasLevel S C l' :=
  fun θ => le_trans hll (hC θ)

/-- Every procedure has level `0`, and the largest level any procedure can have
is `1`. -/
theorem hasLevel_zero (S : SamplingModel Θ Ω) (C : Ω → Set Θ) : HasLevel S C 0 :=
  fun θ => coverageProb_nonneg S C θ

theorem level_le_one {S : SamplingModel Θ Ω} {C : Ω → Set Θ} {level : ℝ}
    (hC : HasLevel S C level) (θ : Θ) : level ≤ 1 :=
  le_trans (hC θ) (coverageProb_le_one S C θ)

open scoped Classical in
/-- **Bonferroni**: two certified procedures may be intersected, at the cost of
adding their error budgets.  This is what makes levels compositional — a
simultaneous statement about two quantities is available without re-deriving
either procedure. -/
theorem coverage_inter_ge (S : SamplingModel Θ Ω) (C D : Ω → Set Θ) (θ : Θ) :
    coverageProb S C θ + coverageProb S D θ - 1 ≤ coverageProb S (fun w => C w ∩ D w) θ := by
  classical
  have hsum : coverageProb S C θ + coverageProb S D θ
      = (S.law θ).expect (fun w => (if θ ∈ C w then (1:ℝ) else 0)
          + (if θ ∈ D w then (1:ℝ) else 0)) := by
    simp only [coverageProb, FinPMF.expect_add]
  have hle : (S.law θ).expect (fun w => (if θ ∈ C w then (1:ℝ) else 0)
        + (if θ ∈ D w then (1:ℝ) else 0))
      ≤ (S.law θ).expect (fun w => (if θ ∈ C w ∩ D w then (1:ℝ) else 0) + 1) := by
    refine FinPMF.expect_mono _ (fun w => ?_)
    by_cases hc : θ ∈ C w <;> by_cases hd : θ ∈ D w <;>
      simp [hc, hd, Set.mem_inter_iff]
  have hone : (S.law θ).expect (fun w => (if θ ∈ C w ∩ D w then (1:ℝ) else 0) + 1)
      = coverageProb S (fun w => C w ∩ D w) θ + 1 := by
    rw [FinPMF.expect_add]
    simp [coverageProb, FinPMF.expect, (S.law θ).total]
  have := hsum ▸ hle
  rw [hone] at this
  linarith

/-- The intersection of a level-`1-α` and a level-`1-β` procedure has level
`1-(α+β)`. -/
theorem hasLevel_inter {S : SamplingModel Θ Ω} {C D : Ω → Set Θ} {a b : ℝ}
    (hC : HasLevel S C (1 - a)) (hD : HasLevel S D (1 - b)) :
    HasLevel S (fun w => C w ∩ D w) (1 - (a + b)) := by
  intro θ
  have := coverage_inter_ge S C D θ
  have h1 := hC θ
  have h2 := hD θ
  linarith

/-! ## §3 The bridge: bounded noise makes the admissible region a confidence
procedure

The Stage-4 surviving region is a *possibility* set.  Given a measurement model
whose noise is bounded by the declared tolerance, the region is also a coverage-
one procedure — the one sound direction of `possibility → confidence`. -/

/-- The Stage-4 admissible region, read as a procedure: the observation
determines the reading, and the reported set is the region compatible with it.
`obs w` is the value the instrument reports on outcome `w`. -/
def toleranceProcedure (F : ParamFamily Θ) (time tol : ℝ) (htol : 0 ≤ tol)
    (obs : Ω → ℝ) : Ω → Set Θ :=
  fun w => Compatible F [⟨time, obs w, tol, htol⟩]

/-- **The deterministic admissible region is a coverage-one confidence
procedure**, provided (i) every parameter of interest is in the prior region and
(ii) the observation is the prediction of the true parameter perturbed by noise
bounded by the declared tolerance.

This is the exact sense in which the set-valued semantics of the earlier stages
is the outer shell of the probabilistic one: it never fails to contain the
truth, at the price of saying nothing about weights inside itself. -/
theorem tolerance_procedure_has_full_coverage (S : SamplingModel Θ Ω)
    (F : ParamFamily Θ) (time tol : ℝ) (htol : 0 ≤ tol) (obs : Ω → ℝ) (θ : Θ)
    (hprior : θ ∈ F.prior)
    (hnoise : ∀ w, 0 < (S.law θ).mass w → |obs w - F.predict θ time| ≤ tol) :
    coverageProb S (toleranceProcedure F time tol htol obs) θ = 1 := by
  rw [coverageProb_eq_one_iff]
  intro w hw
  refine ⟨hprior, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hnoise w hw

theorem tolerance_procedure_hasLevel (S : SamplingModel Θ Ω)
    (F : ParamFamily Θ) (time tol : ℝ) (htol : 0 ≤ tol) (obs : Ω → ℝ)
    (hprior : ∀ θ, θ ∈ F.prior)
    (hnoise : ∀ θ, ∀ w, 0 < (S.law θ).mass w → |obs w - F.predict θ time| ≤ tol)
    {level : ℝ} (hlevel : level ≤ 1) :
    HasLevel S (toleranceProcedure F time tol htol obs) level := by
  intro θ
  rw [tolerance_procedure_has_full_coverage S F time tol htol obs θ (hprior θ) (hnoise θ)]
  exact hlevel

/-! ## §4 Negatives: a level is not informativeness, and not a credible mass -/

/-- **A coverage guarantee alone is worthless.**  The procedure that always
reports the whole parameter space has coverage one at every parameter, so a
level certificate carries information only in conjunction with a statement about
the size of the reported set. -/
theorem full_coverage_is_free (S : SamplingModel Θ Ω) (θ : Θ) :
    coverageProb S (fun _ => (Set.univ : Set Θ)) θ = 1 := by
  rw [coverageProb_eq_one_iff]
  intro w _
  exact Set.mem_univ θ

/-- The trivial procedure meets every declared level. -/
theorem trivial_procedure_hasLevel (S : SamplingModel Θ Ω) {level : ℝ}
    (hlevel : level ≤ 1) : HasLevel S (fun _ => (Set.univ : Set Θ)) level :=
  fun θ => by rw [full_coverage_is_free]; exact hlevel

/-- The uninformative sampling model on `Bool`: whatever the parameter, the
instrument reports `true`.  Used for the credible/confidence separation. -/
noncomputable def blindModel : SamplingModel Bool Bool where
  law := fun _ =>
    { mass := fun w => if w then 1 else 0
      nonneg := by intro w; cases w <;> norm_num
      total := by rw [Fintype.sum_bool]; norm_num }

/-- A prior putting mass `19/20` on `false`. -/
noncomputable def skewedPrior : FinPMF Bool where
  mass := fun w => if w then 1/20 else 19/20
  nonneg := by intro w; cases w <;> norm_num
  total := by rw [Fintype.sum_bool]; norm_num

open scoped Classical in
/-- **A 95% credible set need not have 95% coverage.**  Under an observation
that carries no information, the set `{false}` holds 19/20 of the posterior
(= prior) mass, yet its coverage at the parameter `true` is `0`.  So a credible
region may not be reported as a confidence region. -/
theorem credible_mass_is_not_coverage :
    massOf skewedPrior (fun b => if b then (1:ℝ) else 0) {0} = 19/20 ∧
      coverageProb blindModel (fun _ => ({false} : Set Bool)) true = 0 := by
  constructor
  · simp only [massOf, FinPMF.expect, Fintype.sum_bool, skewedPrior]
    norm_num
  · simp only [coverageProb, FinPMF.expect, Fintype.sum_bool, blindModel]
    norm_num

open scoped Classical in
/-- **And a coverage-one procedure need not carry posterior mass.**  The
procedure reporting `{true}` covers the parameter `true` with probability one,
while `{true}` holds only `1/20` of the posterior mass.  Together with the
previous theorem this shows the two numbers are independent in both
directions. -/
theorem coverage_is_not_credible_mass :
    coverageProb blindModel (fun _ => ({true} : Set Bool)) true = 1 ∧
      massOf skewedPrior (fun b => if b then (1:ℝ) else 0) {1} = 1/20 := by
  constructor
  · rw [coverageProb_eq_one_iff]
    intro w _
    rfl
  · simp only [massOf, FinPMF.expect, Fintype.sum_bool, skewedPrior]
    norm_num

/-- **No rule reads a level off the reported set.**  There is no function from
reported sets to levels that is correct for every procedure: two procedures
reporting the same set on the observed outcome can have any two coverages.  This
is the strongest form of the `envelope ≠ confidence` boundary — not merely that
the existing coercion is unsound, but that no coercion exists. -/
theorem no_function_from_envelope_to_level :
    ¬ ∃ f : Set Bool → ℝ, ∀ (S : SamplingModel Bool Bool) (C : Bool → Set Bool) (θ : Bool),
        f (C true) = coverageProb S C θ := by
  rintro ⟨f, hf⟩
  have h1 : f ({true} : Set Bool) = 1 := by
    rw [hf blindModel (fun _ => ({true} : Set Bool)) true]
    exact (coverage_is_not_credible_mass).1
  have hcov : coverageProb blindModel (fun w => cond w ({true} : Set Bool) ∅) false = 0 := by
    simp only [coverageProb, FinPMF.expect, Fintype.sum_bool, blindModel]
    norm_num
  have h2 : f ({true} : Set Bool) = 0 :=
    (hf blindModel (fun w => cond w ({true} : Set Bool) ∅) false).trans hcov
  rw [h1] at h2
  norm_num at h2

end Integration.Experiment.CoverageSemantics
