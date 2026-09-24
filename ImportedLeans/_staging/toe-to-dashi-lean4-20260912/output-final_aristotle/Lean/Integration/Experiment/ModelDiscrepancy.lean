import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 7, lane 1 — model discrepancy

`TOE_STAGE6_INFERENCE.md` frontier item 5 records the gap closed here:

> **Model discrepancy is still undeclared.**  `derived_budget_ignores_model_discrepancy`
> proves the budget cannot see it; no term in any structure represents it.

Everything in Stages 4–6 works with

```
y  =  f_θ(x)  +  (measurement tolerance)
```

whereas a scientific model needs

```
y  =  f_θ(x)  +  δ(x)  +  (measurement tolerance)
```

with `δ` the **model discrepancy** — the part of reality the declared family
cannot represent at *any* parameter value.  This file introduces `δ` as a named
object and proves the four facts that make it worth naming.

## The objects

* `discrepancy F θ truth` — the function `t ↦ truth t − F.predict θ t`;
* `AdequateOn F θ truth T η` — the discrepancy is at most `η` throughout `T`;
* `Generates truth E` — every reading in `E` is the truth read exactly;
* `inflate d r`, `inflateAll d E` — widening every declared tolerance by `d`.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `fit_is_not_adequacy` | theorem | a worked family/dataset where the surviving region is the **single point** `{2}` and yet the discrepancy at an unmeasured time is `12` |
| `fit_precise_yet_arbitrarily_inadequate` | theorem | the same, with the inadequacy driven above **any** declared bound `η`: parameter fit ⇏ model adequacy |
| `silent_coverage_failure` | theorem | unmodelled discrepancy can leave the region **nonempty** (no refutation is signalled) and **exclude the true parameter** |
| `discrepancy_destroys_nominal_containment` | theorem | the generic version: whenever some reading's discrepancy exceeds its tolerance, the data-generating parameter is not in the surviving region |
| `inflated_tolerance_contains_the_truth` | theorem | the repair: if `‖δ‖ ≤ d` uniformly, inflating every tolerance by `d` puts the generating parameter back inside |
| `inflation_widens_the_region`, `inflation_strictly_widens` | theorem | and the price is real — the inflated region contains the old one and, in the worked instance, strictly more |
| `every_parameter_is_consistent_with_some_discrepancy` | negative | `θ` and `δ` are not jointly identifiable from data alone: *every* parameter admits a discrepancy explaining the truth exactly |
| `bounded_discrepancy_is_still_not_identified` | negative | and this stays true after a bound on `δ` is declared, provided the bound is large enough |

## Claim boundary

`truth` here is a declared function of time, not a physical system; a
"discrepancy" is the difference of two declared functions.  Nothing estimates
`δ`, and no theorem says any declared `δ` is the discrepancy of a real
experiment.  The point of the file is the *negative* structure: what parameter
fitting cannot tell you once `δ` is allowed to be nonzero.
-/

namespace Integration.Experiment.ModelDiscrepancy

open Set
open Integration.Experiment.ParameterRegion

variable {Θ : Type*}

/-! ## §1 The discrepancy term -/

/-- **Model discrepancy**: what the family member `θ` fails to explain about
`truth`.  This is the term `δ` in `y = f_θ(t) + δ(t) + ε`. -/
def discrepancy (F : ParamFamily Θ) (θ : Θ) (truth : ℝ → ℝ) : ℝ → ℝ :=
  fun t => truth t - F.predict θ t

@[simp] theorem discrepancy_apply (F : ParamFamily Θ) (θ : Θ) (truth : ℝ → ℝ) (t : ℝ) :
    discrepancy F θ truth t = truth t - F.predict θ t := rfl

/-- The truth decomposes as model plus discrepancy — the identity that makes the
term well defined. -/
theorem truth_eq_model_add_discrepancy (F : ParamFamily Θ) (θ : Θ) (truth : ℝ → ℝ) (t : ℝ) :
    truth t = F.predict θ t + discrepancy F θ truth t := by
  simp

/-- A member of the family has zero discrepancy against its own prediction. -/
@[simp] theorem discrepancy_self (F : ParamFamily Θ) (θ : Θ) :
    discrepancy F θ (F.predict θ) = 0 := by
  funext t; simp

/-- **Model adequacy at level `η` on a set of times**: the discrepancy is
uniformly small there.  This is a statement about *all* times in `T`, not only
the measured ones — which is exactly why fitting cannot establish it. -/
def AdequateOn (F : ParamFamily Θ) (θ : Θ) (truth : ℝ → ℝ) (T : Set ℝ) (η : ℝ) : Prop :=
  ∀ t ∈ T, |discrepancy F θ truth t| ≤ η

/-- Adequacy on a larger set is a stronger statement. -/
theorem adequateOn_mono {F : ParamFamily Θ} {θ : Θ} {truth : ℝ → ℝ} {T T' : Set ℝ} {η : ℝ}
    (hT : T ⊆ T') (h : AdequateOn F θ truth T' η) : AdequateOn F θ truth T η :=
  fun t ht => h t (hT ht)

/-- **The data-generating relation**: each reading is the truth, read exactly. -/
def Generates (truth : ℝ → ℝ) (E : List Reading) : Prop :=
  ∀ r ∈ E, r.value = truth r.time

/-! ## §2 Parameter fit is not model adequacy -/

/-- The straight-line-through-the-origin family `y = θ t`. -/
def linearFamily : ParamFamily ℝ where
  prior := univ
  predict := fun θ t => θ * t

@[simp] theorem linearFamily_predict (θ t : ℝ) : linearFamily.predict θ t = θ * t := rfl

/-- A truth **outside** the family: the parabola through `(1,2)` and `(2,4)`
with curvature `k`.  At the two measured times it is indistinguishable from the
line `y = 2t`; away from them it is not. -/
def bentTruth (k : ℝ) : ℝ → ℝ := fun t => 2 * t + k * ((t - 1) * (t - 2))

@[simp] theorem bentTruth_one (k : ℝ) : bentTruth k 1 = 2 := by simp [bentTruth]

@[simp] theorem bentTruth_two (k : ℝ) : bentTruth k 2 = 4 := by
  simp [bentTruth]; ring

theorem bentTruth_five (k : ℝ) : bentTruth k 5 = 10 + 12 * k := by
  simp [bentTruth]; ring

/-- Two exact readings, both explained perfectly by `θ = 2`. -/
def bentData : List Reading :=
  [⟨1, 2, 0, le_refl 0⟩, ⟨2, 4, 0, le_refl 0⟩]

theorem bentData_generated (k : ℝ) : Generates (bentTruth k) bentData := by
  intro r hr
  fin_cases hr <;> first | (simp [bentTruth]; ring) | simp [bentTruth]

/-- **The fit is exact and unique**: one parameter value, no tolerance slack.
Read naively this is a "precise measurement of `θ`". -/
theorem bentData_pins_down_two : Compatible linearFamily bentData = {(2 : ℝ)} := by
  ext θ
  constructor
  · rintro ⟨-, hf⟩
    have h1 : |(2 : ℝ) - θ * 1| ≤ 0 :=
      hf ⟨1, 2, 0, le_refl 0⟩ (List.mem_cons_self ..)
    have h2 : (2 : ℝ) - θ * 1 = 0 := abs_nonpos_iff.mp h1
    show θ = 2
    linarith
  · rintro rfl
    refine ⟨mem_univ _, ?_⟩
    intro r hr
    fin_cases hr <;> · show |_ - _| ≤ (0 : ℝ); norm_num

/-- **Parameter fit does not imply model adequacy.**  The unique surviving
parameter is wrong by `12` at `t = 5`, a time nobody measured. -/
theorem fit_is_not_adequacy :
    ∀ θ ∈ Compatible linearFamily bentData,
      ¬ AdequateOn linearFamily θ (bentTruth 1) univ 11 := by
  intro θ hθ hadq
  have hθ2 : θ = 2 := by
    rw [bentData_pins_down_two] at hθ; exact hθ
  have := hadq 5 (mem_univ _)
  rw [discrepancy_apply, hθ2, bentTruth_five] at this
  rw [linearFamily_predict] at this
  norm_num at this

/-- **The general antipattern**: for *any* declared adequacy level `η`, there is
a family, a dataset generated exactly by a truth, and a surviving region that is
a single point — while every surviving parameter is wrong by more than `η`
somewhere.

```
wrong model  +  flexible parameter  ⇒  apparently precise wrong inference
```
-/
theorem fit_precise_yet_arbitrarily_inadequate (η : ℝ) :
    ∃ (F : ParamFamily ℝ) (E : List Reading) (truth : ℝ → ℝ),
      Generates truth E ∧
      Compatible F E = {(2 : ℝ)} ∧
      ∀ θ ∈ Compatible F E, ∃ t, η < |truth t - F.predict θ t| := by
  refine ⟨linearFamily, bentData, bentTruth (|η| + 1), bentData_generated _,
    bentData_pins_down_two, ?_⟩
  intro θ hθ
  have hθ2 : θ = 2 := by rw [bentData_pins_down_two] at hθ; exact hθ
  refine ⟨5, ?_⟩
  rw [hθ2, bentTruth_five, linearFamily_predict]
  have h1 : |η| + 1 > 0 := by positivity
  have h2 : (10 : ℝ) + 12 * (|η| + 1) - 2 * 5 = 12 * (|η| + 1) := by ring
  rw [h2, abs_of_pos (by linarith)]
  have : η ≤ |η| := le_abs_self η
  linarith

/-! ## §3 Discrepancy destroys nominal containment -/

/-- **The generic statement.**  If the data are generated by `θ₀` *plus* a
discrepancy, and at some reading the discrepancy exceeds the declared tolerance,
then the generating parameter is not in the surviving region — the region's
nominal containment guarantee is void. -/
theorem discrepancy_destroys_nominal_containment {F : ParamFamily Θ} {θ₀ : Θ}
    {truth : ℝ → ℝ} {E : List Reading} (hgen : Generates truth E)
    {r : Reading} (hr : r ∈ E) (hbig : r.tol < |discrepancy F θ₀ truth r.time|) :
    θ₀ ∉ Compatible F E := by
  rintro ⟨-, hf⟩
  have := hf r hr
  rw [Fits, hgen r hr] at this
  exact absurd this (not_le.mpr hbig)

/-- The bounded-noise counterpart of Stage 6's coverage-one theorem: if the
discrepancy is within tolerance at every reading, containment survives. -/
theorem containment_of_small_discrepancy {F : ParamFamily Θ} {θ₀ : Θ}
    {truth : ℝ → ℝ} {E : List Reading} (hgen : Generates truth E) (hprior : θ₀ ∈ F.prior)
    (hsmall : ∀ r ∈ E, |discrepancy F θ₀ truth r.time| ≤ r.tol) :
    θ₀ ∈ Compatible F E := by
  refine ⟨hprior, fun r hr => ?_⟩
  rw [Fits, hgen r hr]
  exact hsmall r hr

/-- **Silent failure.**  Here the region is *nonempty* — nothing signals a
refutation, the analyst reports a precise parameter — and yet it excludes the
parameter that generated the data. -/
theorem silent_coverage_failure :
    ∃ (F : ParamFamily ℝ) (θ₀ : ℝ) (δ : ℝ → ℝ) (E : List Reading),
      Generates (fun t => F.predict θ₀ t + δ t) E ∧
      (Compatible F E).Nonempty ∧
      θ₀ ∉ Compatible F E := by
  refine ⟨linearFamily, 1, fun t => t, bentData, ?_, ⟨2, ?_⟩, ?_⟩
  · intro r hr
    fin_cases hr <;> · show (_ : ℝ) = _; norm_num
  · rw [bentData_pins_down_two]; rfl
  · rw [bentData_pins_down_two]
    intro h
    have : (1 : ℝ) = 2 := h
    norm_num at this

/-! ## §4 The repair, and its price -/

/-- Widen a declared tolerance by a discrepancy allowance `d`. -/
def inflate (d : ℝ) (hd : 0 ≤ d) (r : Reading) : Reading :=
  ⟨r.time, r.value, r.tol + d, by have := r.tol_nonneg; linarith⟩

@[simp] theorem inflate_time (d : ℝ) (hd : 0 ≤ d) (r : Reading) :
    (inflate d hd r).time = r.time := rfl

@[simp] theorem inflate_value (d : ℝ) (hd : 0 ≤ d) (r : Reading) :
    (inflate d hd r).value = r.value := rfl

@[simp] theorem inflate_tol (d : ℝ) (hd : 0 ≤ d) (r : Reading) :
    (inflate d hd r).tol = r.tol + d := rfl

/-- Widen every tolerance in a dataset. -/
def inflateAll (d : ℝ) (hd : 0 ≤ d) (E : List Reading) : List Reading :=
  E.map (inflate d hd)

/-- **A declared discrepancy bound restores containment.**  If `|δ| ≤ d`
everywhere, then inflating every tolerance by `d` puts the generating parameter
back in the surviving region.  This is the honest way to keep a coverage claim
in the presence of model error. -/
theorem inflated_tolerance_contains_the_truth {F : ParamFamily Θ} {θ₀ : Θ}
    {truth : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d) (hbound : ∀ t, |discrepancy F θ₀ truth t| ≤ d)
    {E : List Reading} (hgen : Generates truth E) (hprior : θ₀ ∈ F.prior) :
    θ₀ ∈ Compatible F (inflateAll d hd E) := by
  refine ⟨hprior, fun r hr => ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  show |(inflate d hd r₀).value - F.predict θ₀ (inflate d hd r₀).time| ≤ (inflate d hd r₀).tol
  rw [inflate_value, inflate_time, inflate_tol, hgen r₀ hr₀]
  have := hbound r₀.time
  rw [discrepancy_apply] at this
  have h0 := r₀.tol_nonneg
  linarith

/-- **The price, part one**: inflating never removes a parameter. -/
theorem inflation_widens_the_region {F : ParamFamily Θ} {d : ℝ} (hd : 0 ≤ d)
    (E : List Reading) : Compatible F E ⊆ Compatible F (inflateAll d hd E) := by
  rintro θ ⟨hp, hf⟩
  refine ⟨hp, fun r hr => ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  show |(inflate d hd r₀).value - F.predict θ (inflate d hd r₀).time| ≤ (inflate d hd r₀).tol
  rw [inflate_value, inflate_time, inflate_tol]
  have := hf r₀ hr₀
  rw [Fits] at this
  linarith

/-- **The price, part two**: in the worked instance the inflated region is
strictly larger, so the restored containment is paid for in precision. -/
theorem inflation_strictly_widens :
    Compatible linearFamily bentData ⊂
      Compatible linearFamily (inflateAll 1 zero_le_one bentData) := by
  refine ⟨inflation_widens_the_region zero_le_one bentData, ?_⟩
  intro hsub
  have h2 : (2.5 : ℝ) ∈ Compatible linearFamily (inflateAll 1 zero_le_one bentData) := by
    refine ⟨mem_univ _, fun r hr => ?_⟩
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    fin_cases hr₀ <;>
      · show |_ - (2.5 : ℝ) * _| ≤ (0 : ℝ) + 1
        norm_num
  have := hsub h2
  rw [bentData_pins_down_two] at this
  have : (2.5 : ℝ) = 2 := this
  norm_num at this

/-! ## §5 `θ` and `δ` are not jointly identified -/

/-- **The fundamental non-identifiability.**  Data alone never isolates the
discrepancy: *every* parameter value admits a discrepancy function reproducing
the truth exactly.  A discrepancy term is therefore only informative once its
size or shape is separately constrained. -/
theorem every_parameter_is_consistent_with_some_discrepancy (F : ParamFamily Θ)
    (truth : ℝ → ℝ) (θ : Θ) :
    ∃ δ : ℝ → ℝ, ∀ t, truth t = F.predict θ t + δ t :=
  ⟨discrepancy F θ truth, fun t => truth_eq_model_add_discrepancy F θ truth t⟩

/-- And a declared *bound* on the discrepancy does not restore identifiability
by itself: in the worked instance every parameter in `[1, 3]` explains the truth
with a discrepancy bounded by `12` on `[0, 5]`. -/
theorem bounded_discrepancy_is_still_not_identified (θ : ℝ) (h1 : 1 ≤ θ) (h3 : θ ≤ 3) :
    AdequateOn linearFamily θ (bentTruth 0) (Icc 0 5) 12 := by
  intro t ht
  obtain ⟨ht0, ht5⟩ := ht
  rw [discrepancy_apply, linearFamily_predict]
  have hb : bentTruth 0 t = 2 * t := by simp [bentTruth]
  rw [hb, abs_le]
  constructor <;> nlinarith

end Integration.Experiment.ModelDiscrepancy
