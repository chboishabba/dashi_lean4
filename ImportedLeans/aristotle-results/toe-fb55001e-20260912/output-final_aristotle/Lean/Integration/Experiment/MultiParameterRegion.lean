import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 5, lane 2 — surviving regions in more than one parameter

`TOE_STAGE4_INFERENCE.md` frontier item 8 records:

> Both instances have a single real parameter.  The generic lane-1 theorems are
> stated for an arbitrary parameter type, but the interval-shape results
> (`compatible_ordConnected`, `envelope_eq_Icc`) are one-dimensional.

This file supplies the multi-parameter shape theory, over an arbitrary real
normed space of parameters, and — more importantly — the identifiability
dichotomy that has no one-dimensional analogue.

## Shape of the surviving region

For a family whose prediction is *affine* in the parameter,
`predict θ t = base t + ⟪grad t, θ⟫`:

| Theorem | Content |
|---|---|
| `affineConstraint_convex` | one reading cuts out a convex slab |
| `affineCompatible_convex` | hence the surviving region is convex whenever the declared prior region is |
| `affineConstraint_isClosed`, `affineCompatible_isClosed` | and closed |
| `affineCompatible_ordConnected` | in the one-dimensional case this recovers the Stage-4 interval result |

and for an arbitrary (not necessarily affine) family:

| Theorem | Content |
|---|---|
| `envelope_ordConnected_of_isPreconnected` | a continuous consumer over a connected surviving region has an *interval* envelope: reporting `[lo, hi]` loses nothing |
| `envelope_eq_Icc_of_isCompact` | over a nonempty compact connected region the envelope is exactly `[min, max]`, both attained |

## Identifiability — the genuinely multi-dimensional result

| Theorem | Content |
|---|---|
| `unidentified_direction_survives` | if a direction is invisible to every reading, the surviving region is invariant under translation along it: data cannot resolve it |
| `few_readings_do_not_identify` | **fewer readings than parameters never identify**: with `k < d` readings of a `d`-parameter affine family there is always a nonzero invisible direction, so the surviving region contains a whole line through each of its points |
| `envelope_not_a_point_of_unidentified_direction` | and a consumer that sees that direction has a non-point envelope, however small the tolerances |
| `exact_readings_identify` | the positive converse: if the readings' gradients are jointly injective and are read exactly, the surviving region is the single true parameter |

The two together are the honest statement of what data can and cannot do in
several parameters: the obstruction is the kernel of the joint gradient map, and
it is a *rank* condition, not a matter of tolerance size.

## Claim boundary

Everything is a statement about `ParamFamily`s over a real normed space; no
probability, no coverage, and no claim about any physical system.  Tolerances
are declared comparison bounds, exactly as in
`Integration.Experiment.ParameterRegion`.
-/

namespace Integration.Experiment.MultiParameterRegion

open Integration.Experiment.ParameterRegion
open Set

/-! ## §1 Affine families in several parameters -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A family whose prediction depends **affinely** on the parameter: at each
time the prediction is a declared base value plus a continuous linear functional
of the parameter (its gradient at that time). -/
def affineFamily (prior : Set E) (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) :
    ParamFamily E where
  prior := prior
  predict := fun θ t => base t + grad t θ

@[simp] theorem affineFamily_predict (prior : Set E) (base : ℝ → ℝ)
    (grad : ℝ → E →L[ℝ] ℝ) (θ : E) (t : ℝ) :
    (affineFamily prior base grad).predict θ t = base t + grad t θ := rfl

@[simp] theorem affineFamily_prior (prior : Set E) (base : ℝ → ℝ)
    (grad : ℝ → E →L[ℝ] ℝ) : (affineFamily prior base grad).prior = prior := rfl

/-- The set of parameters fitting a single reading of an affine family. -/
def affineSlab (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) (r : Reading) : Set E :=
  {θ | |r.value - (base r.time + grad r.time θ)| ≤ r.tol}

theorem mem_affineSlab {base : ℝ → ℝ} {grad : ℝ → E →L[ℝ] ℝ} {r : Reading} {θ : E} :
    θ ∈ affineSlab base grad r ↔ |r.value - (base r.time + grad r.time θ)| ≤ r.tol :=
  Iff.rfl

theorem fits_affine_iff {prior : Set E} {base : ℝ → ℝ} {grad : ℝ → E →L[ℝ] ℝ}
    {r : Reading} {θ : E} :
    Fits (affineFamily prior base grad) θ r ↔ θ ∈ affineSlab base grad r := Iff.rfl

/-- **One reading cuts out a convex slab.** -/
theorem affineConstraint_convex (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) (r : Reading) :
    Convex ℝ (affineSlab base grad r) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_affineSlab] at hx hy ⊢
  have hlin : grad r.time (a • x + b • y) = a * grad r.time x + b * grad r.time y := by
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have hsplit : r.value - (base r.time + grad r.time (a • x + b • y))
      = a * (r.value - (base r.time + grad r.time x))
        + b * (r.value - (base r.time + grad r.time y)) := by
    have ha' : a = 1 - b := by linarith
    rw [hlin, ha']
    ring
  calc |r.value - (base r.time + grad r.time (a • x + b • y))|
      ≤ |a * (r.value - (base r.time + grad r.time x))|
        + |b * (r.value - (base r.time + grad r.time y))| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ a * r.tol + b * r.tol := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        exact add_le_add (mul_le_mul_of_nonneg_left hx ha)
          (mul_le_mul_of_nonneg_left hy hb)
    _ = r.tol := by rw [← add_mul, hab, one_mul]

/-- The slab is closed. -/
theorem affineConstraint_isClosed (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) (r : Reading) :
    IsClosed (affineSlab base grad r) := by
  have hcont : Continuous fun θ : E => |r.value - (base r.time + grad r.time θ)| :=
    (continuous_const.sub (continuous_const.add (grad r.time).continuous)).abs
  simpa [affineSlab] using isClosed_le hcont continuous_const

theorem compatible_affine_eq (prior : Set E) (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ)
    (Ev : List Reading) :
    Compatible (affineFamily prior base grad) Ev
      = prior ∩ ⋂ r ∈ Ev, affineSlab base grad r := by
  ext θ
  simp [Compatible, Fits, affineSlab, affineFamily]

/-- **The surviving region of an affine family is convex** whenever the declared
prior region is. -/
theorem affineCompatible_convex {prior : Set E} (hprior : Convex ℝ prior)
    (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) (Ev : List Reading) :
    Convex ℝ (Compatible (affineFamily prior base grad) Ev) := by
  rw [compatible_affine_eq]
  exact hprior.inter (convex_iInter fun r =>
    convex_iInter fun _ => affineConstraint_convex base grad r)

/-- And closed. -/
theorem affineCompatible_isClosed {prior : Set E} (hprior : IsClosed prior)
    (base : ℝ → ℝ) (grad : ℝ → E →L[ℝ] ℝ) (Ev : List Reading) :
    IsClosed (Compatible (affineFamily prior base grad) Ev) := by
  rw [compatible_affine_eq]
  exact hprior.inter (isClosed_biInter fun r _ => affineConstraint_isClosed base grad r)

/-- In one parameter, convexity **is** order-connectedness: the Stage-4 interval
result is the one-dimensional case of `affineCompatible_convex`. -/
theorem affineCompatible_ordConnected {prior : Set ℝ} (hprior : Convex ℝ prior)
    (base : ℝ → ℝ) (grad : ℝ → ℝ →L[ℝ] ℝ) (Ev : List Reading) :
    (Compatible (affineFamily prior base grad) Ev).OrdConnected :=
  (affineCompatible_convex hprior base grad Ev).ordConnected

/-! ## §2 The shape of the envelope -/

variable {Θ : Type*} [TopologicalSpace Θ]

/-- **A connected surviving region has an interval envelope.**  Reporting a
continuous consumer's envelope as `[lo, hi]` then loses nothing: every
intermediate value is genuinely predicted by some surviving parameter. -/
theorem envelope_ordConnected_of_isPreconnected (F : ParamFamily Θ) (Ev : List Reading)
    (C : Θ → ℝ) (hconn : IsPreconnected (Compatible F Ev))
    (hC : ContinuousOn C (Compatible F Ev)) :
    (envelope F Ev C).OrdConnected :=
  (hconn.image C hC).ordConnected

/-- **Over a nonempty compact connected region the envelope is exactly
`[min, max]`**, and both ends are attained by surviving parameters. -/
theorem envelope_eq_Icc_of_isCompact (F : ParamFamily Θ) (Ev : List Reading)
    (C : Θ → ℝ) (hne : (Compatible F Ev).Nonempty)
    (hcomp : IsCompact (Compatible F Ev)) (hconn : IsPreconnected (Compatible F Ev))
    (hC : ContinuousOn C (Compatible F Ev)) :
    ∃ lo hi, lo ∈ envelope F Ev C ∧ hi ∈ envelope F Ev C ∧
      envelope F Ev C = Icc lo hi := by
  have himg : IsCompact (C '' Compatible F Ev) := hcomp.image_of_continuousOn hC
  have hne' : (C '' Compatible F Ev).Nonempty := hne.image C
  obtain ⟨lo, hlo, hlomin⟩ := himg.exists_isLeast hne'
  obtain ⟨hi, hhi, himax⟩ := himg.exists_isGreatest hne'
  refine ⟨lo, hi, hlo, hhi, ?_⟩
  have hord : (envelope F Ev C).OrdConnected :=
    envelope_ordConnected_of_isPreconnected F Ev C hconn hC
  apply Subset.antisymm
  · intro y hy
    exact ⟨hlomin hy, himax hy⟩
  · intro y hy
    exact hord.out hlo hhi hy

/-! ## §3 Identifiability: the rank obstruction -/

/-- A direction is **invisible** to a list of readings when it changes no
prediction at any of their times. -/
def Invisible (grad : ℝ → E →L[ℝ] ℝ) (Ev : List Reading) (v : E) : Prop :=
  ∀ r ∈ Ev, grad r.time v = 0

/-- **An invisible direction is never resolved.**  If `v` is invisible to the
evidence and the declared prior region is invariant under translation along it,
the whole surviving region is: no amount of data of this kind separates `θ` from
`θ + c • v`. -/
theorem unidentified_direction_survives {prior : Set E} {base : ℝ → ℝ}
    {grad : ℝ → E →L[ℝ] ℝ} {Ev : List Reading} {v : E} (hv : Invisible grad Ev v)
    (hprior : ∀ θ ∈ prior, ∀ c : ℝ, θ + c • v ∈ prior)
    {θ : E} (hθ : θ ∈ Compatible (affineFamily prior base grad) Ev) (c : ℝ) :
    θ + c • v ∈ Compatible (affineFamily prior base grad) Ev := by
  obtain ⟨hp, hf⟩ := hθ
  refine ⟨hprior θ hp c, fun r hr => ?_⟩
  have hlin : grad r.time (θ + c • v) = grad r.time θ := by
    rw [map_add, map_smul, hv r hr]
    simp
  have := hf r hr
  simpa [Fits, affineFamily, hlin] using this

/-- **A consumer that sees an unidentified direction has a non-point
envelope.**  This is a rank obstruction: it does not shrink when the tolerances
do. -/
theorem envelope_not_a_point_of_unidentified_direction {prior : Set E} {base : ℝ → ℝ}
    {grad : ℝ → E →L[ℝ] ℝ} {Ev : List Reading} {v : E} (hv : Invisible grad Ev v)
    (hprior : ∀ θ ∈ prior, ∀ c : ℝ, θ + c • v ∈ prior)
    {θ : E} (hθ : θ ∈ Compatible (affineFamily prior base grad) Ev)
    (C : E →L[ℝ] ℝ) (hCv : C v ≠ 0) :
    ¬ (envelope (affineFamily prior base grad) Ev C).Subsingleton := by
  intro hsub
  have h1 : C θ ∈ envelope (affineFamily prior base grad) Ev C := ⟨θ, hθ, rfl⟩
  have h2 : C (θ + (1 : ℝ) • v) ∈ envelope (affineFamily prior base grad) Ev C :=
    ⟨θ + (1 : ℝ) • v, unidentified_direction_survives hv hprior hθ 1, rfl⟩
  have := hsub h1 h2
  rw [map_add, map_smul] at this
  simp only [one_smul] at this
  exact hCv (by linarith [this])

/-- The **joint gradient map** of a list of readings: the linear map sending a
parameter to the vector of its predicted deviations. -/
noncomputable def jointGrad {d k : ℕ} (grad : ℝ → (Fin d → ℝ) →L[ℝ] ℝ)
    (rs : Fin k → Reading) : (Fin d → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun := fun θ i => grad (rs i).time θ
  map_add' := by intro x y; funext i; simp
  map_smul' := by intro c x; funext i; simp

/-- **Fewer readings than parameters never identify.**  With `k < d` readings of
a `d`-parameter affine family there is a nonzero direction invisible to all of
them, so the surviving region is translation-invariant along a line — whatever
the observed values and however tight the declared tolerances. -/
theorem few_readings_do_not_identify {d k : ℕ} (hk : k < d)
    (grad : ℝ → (Fin d → ℝ) →L[ℝ] ℝ) (rs : Fin k → Reading) :
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ ∀ i, grad (rs i).time v = 0 := by
  have hrank : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin d → ℝ) := by
    simpa using hk
  have hker : (jointGrad grad rs).ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv0, fun i => ?_⟩
  have : jointGrad grad rs v = 0 := hv
  exact congrFun this i

/-- **Exact readings identify, provided the gradients are jointly injective.**
The positive converse of the rank obstruction: it is injectivity of the joint
gradient map, not the number of readings as such, that does the work. -/
theorem exact_readings_identify {prior : Set E} {base : ℝ → ℝ}
    {grad : ℝ → E →L[ℝ] ℝ} {Ev : List Reading}
    (hinj : ∀ v : E, (∀ r ∈ Ev, grad r.time v = 0) → v = 0)
    (htol : ∀ r ∈ Ev, r.tol = 0)
    {θstar : E} (hstar : θstar ∈ Compatible (affineFamily prior base grad) Ev) :
    Compatible (affineFamily prior base grad) Ev = {θstar} := by
  apply Subset.antisymm
  · intro θ hθ
    have hdiff : ∀ r ∈ Ev, grad r.time (θ - θstar) = 0 := by
      intro r hr
      have h1 : |r.value - (base r.time + grad r.time θ)| ≤ 0 := by
        have := hθ.2 r hr
        simp only [Fits, affineFamily_predict, htol r hr] at this
        exact this
      have h2 : |r.value - (base r.time + grad r.time θstar)| ≤ 0 := by
        have := hstar.2 r hr
        simp only [Fits, affineFamily_predict, htol r hr] at this
        exact this
      have e1 : r.value - (base r.time + grad r.time θ) = 0 :=
        abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _))
      have e2 : r.value - (base r.time + grad r.time θstar) = 0 :=
        abs_eq_zero.1 (le_antisymm h2 (abs_nonneg _))
      rw [map_sub]
      linarith [e1, e2]
    have := hinj _ hdiff
    have : θ = θstar := by
      have := sub_eq_zero.1 this
      exact this
    simpa using this
  · intro θ hθ
    rw [mem_singleton_iff] at hθ
    subst hθ
    exact hstar

/-! ## §4 A two-parameter instance: the hypotheses are satisfiable

Data only — the two theorems below are instances of `few_readings_do_not_identify`
and `exact_readings_identify`, and exist to show that neither statement is
vacuous.  The family is the two-parameter affine model

```
y(t) = a + t · b,     θ = (a, b),
```

with the true parameter `θ* = (1, 2)`.
-/

/-- The gradient of the two-parameter line model at time `t`: `θ ↦ θ₀ + t·θ₁`. -/
noncomputable def lineGrad (t : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 + t • ContinuousLinearMap.proj 1

@[simp] theorem lineGrad_apply (t : ℝ) (θ : Fin 2 → ℝ) :
    lineGrad t θ = θ 0 + t * θ 1 := by
  simp [lineGrad]

/-- The true parameter of the instance. -/
def lineTruth : Fin 2 → ℝ := ![1, 2]

/-- A reading at time `t` of the exact prediction of `lineTruth`, with tolerance
zero. -/
noncomputable def exactReading (t : ℝ) : Reading where
  time := t
  value := lineGrad t lineTruth
  tol := 0
  tol_nonneg := le_refl 0

/-- **One reading cannot fix two parameters.**  With a single reading of the
two-parameter line model there is a nonzero invisible direction, so the
surviving region contains a whole line through the truth — with tolerance
`0`. -/
theorem line_one_reading_does_not_identify :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      ∀ c : ℝ, lineTruth + c • v ∈
        Compatible (affineFamily (Set.univ : Set (Fin 2 → ℝ)) (fun _ => 0) lineGrad)
          [exactReading 0] := by
  refine ⟨![0, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 1
    norm_num at this
  · intro c
    refine unidentified_direction_survives (v := ![0, 1]) ?_ (fun θ _ c => Set.mem_univ _) ?_ c
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      simp [exactReading]
    · refine ⟨Set.mem_univ _, fun r hr => ?_⟩
      rw [List.mem_singleton] at hr
      subst hr
      simp [Fits, affineFamily, exactReading]

/-- **Two exact readings do fix them.**  The same model read at two distinct
times has a jointly injective gradient pair, so the surviving region is exactly
the true parameter. -/
theorem line_two_exact_readings_identify :
    Compatible (affineFamily (Set.univ : Set (Fin 2 → ℝ)) (fun _ => 0) lineGrad)
        [exactReading 0, exactReading 1] = {lineTruth} := by
  refine exact_readings_identify (fun v hv => ?_) (fun r hr => ?_) ?_
  · have h0 : v 0 = 0 := by
      simpa [exactReading] using hv (exactReading 0) (by simp)
    have h1 : v 0 + v 1 = 0 := by
      simpa [exactReading] using hv (exactReading 1) (by simp)
    funext i
    fin_cases i
    · simpa using h0
    · simpa using (by linarith : v 1 = 0)
  · rcases List.mem_cons.1 hr with rfl | hr'
    · rfl
    · rw [List.mem_singleton] at hr'; subst hr'; rfl
  · refine ⟨Set.mem_univ _, fun r hr => ?_⟩
    rcases List.mem_cons.1 hr with rfl | hr'
    · simp [Fits, affineFamily, exactReading]
    · rw [List.mem_singleton] at hr'
      subst hr'
      simp [Fits, affineFamily, exactReading]

end Integration.Experiment.MultiParameterRegion
