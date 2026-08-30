import Mathlib
import Integration.Experiment.JacobianSensitivity
import Integration.Experiment.ParameterRegion

/-!
# Stage 6, lane 4 — local identifiability from the Jacobian

`TOE_STAGE5_INFERENCE.md` frontier item 6 records the gap closed here:

> **Multi-parameter identifiability is proved for affine gradients.**  The rank
> obstruction is stated for families affine in the parameter; a nonlinear
> multi-parameter analogue (local injectivity of a Jacobian) is not proved.

This file proves the nonlinear analogue, in both directions, over
`Θ = Fin n → ℝ` with `m` measurement times:

```
rank J_h(θ) = n   ⟹  θ is locally identifiable
rank J_h(θ) < n   ⟹  there is a direction invisible to first order
m < n             ⟹  the rank is deficient, whatever the model
```

## The objects

* `measurementMap F ts` — the map `θ ↦ (predict θ t₁, …, predict θ t_m)` sending
  a parameter to the vector of predicted readings;
* `LocallyIdentifiable h θ` — `h` is injective on some neighbourhood of `θ`;
* `InvisibleDirection J v` — `v ≠ 0` and `J v = 0`.

## What is proved

* `locallyIdentifiable_of_injective_deriv` — **the positive result**: if the
  strict derivative at `θ` is injective (i.e. the Jacobian has full column rank
  `n`), the parameter is locally identifiable.  The proof is the usual
  antilipschitz argument: an injective linear map on a finite-dimensional space
  is bounded below, and the first-order remainder is eventually smaller than
  that bound;
* `exact_readings_pin_down_locally` — the consequence for the set-valued core:
  on a neighbourhood where the measurement map is injective, exact readings cut
  the surviving region down to the single true parameter.  This is the local
  analogue of `MultiParameterRegion.exact_readings_identify`;
* `invisible_direction_of_not_injective` — a deficient rank *is* an invisible
  direction;
* `invisible_direction_vanishes_to_first_order` — and along such a direction
  every predicted reading has vanishing derivative: the data cannot see the
  parameter move, to first order;
* `few_measurements_give_invisible_direction` — **the rank obstruction, without
  any affineness hypothesis**: fewer measurement times than parameters forces an
  invisible direction for *every* model;
* `tolerance_cannot_repair_missing_rank` — and the obstruction is not a
  tolerance issue: it holds for the derivative itself, so no instrument
  improvement removes it.

The honest negatives:

* `first_order_test_is_only_first_order` — a vanishing derivative does not imply
  unidentifiability (`θ ↦ θ³` at `0` is injective), so rank deficiency is a
  *first-order* obstruction and not a proof of non-identifiability;
* `local_identifiability_is_not_global` — local injectivity does not give global
  injectivity, so a full-rank Jacobian licenses no claim about the whole prior
  region.

## What is *not* claimed

No structural identifiability theory, no Fisher information, no genericity
statement, no algorithm for finding the invisible directions of a given model,
and nothing about identifiability from noisy data: `exact_readings_pin_down_locally`
uses tolerance-zero readings.
-/

namespace Integration.Experiment.LocalIdentifiability

open Set Filter Topology
open Integration.Experiment.ParameterRegion

variable {n m : ℕ}

/-! ## §1 The measurement map -/

/-- The **measurement map** of a parameterised family at a list of times: it
sends a parameter to the vector of predicted readings.  Identifiability is a
property of this map. -/
def measurementMap (F : ParamFamily (Fin n → ℝ)) (ts : Fin m → ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) :=
  fun θ i => F.predict θ (ts i)

/-- **Local identifiability**: the measurement map is injective near `θ`, so no
other nearby parameter produces the same data. -/
def LocallyIdentifiable (h : (Fin n → ℝ) → (Fin m → ℝ)) (θ : Fin n → ℝ) : Prop :=
  ∃ s ∈ 𝓝 θ, InjOn h s

/-- **An invisible direction**: a nonzero parameter direction the Jacobian kills. -/
def InvisibleDirection (J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ) : Prop :=
  v ≠ 0 ∧ J v = 0

/-! ## §2 Full rank gives local identifiability -/

/-- **Full column rank implies local identifiability.**  If the strict
derivative at `θ` is injective then the measurement map is injective on a
neighbourhood of `θ`.

This is the nonlinear successor of the affine rank theorem: there, injective
gradients pinned the parameter down globally; here, an injective Jacobian pins
it down locally. -/
theorem locallyIdentifiable_of_injective_deriv {h : (Fin n → ℝ) → (Fin m → ℝ)}
    {θ : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}
    (hd : HasStrictFDerivAt h J θ) (hinj : Function.Injective J) :
    LocallyIdentifiable h θ := by
  obtain ⟨K, hK, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (J : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))).1 hinj
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK
  set c : NNReal := (2 * K)⁻¹ with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact inv_pos.2 (by positivity)
  obtain ⟨s, hs, happ⟩ := hd.approximates_deriv_on_nhds (c := c) (Or.inr hcpos)
  refine ⟨s, hs, ?_⟩
  intro x hx y hy hxy
  have h1 : ‖h x - h y - J (x - y)‖ ≤ (c : ℝ) * ‖x - y‖ := happ x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖x - y‖ ≤ (K : ℝ) * ‖J (x - y)‖ :=
    ZeroHomClass.bound_of_antilipschitz (J : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) hanti (x - y)
  have h3 : (K : ℝ) * ‖J (x - y)‖ ≤ (K : ℝ) * ((c : ℝ) * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hK)
  have hKc : (K : ℝ) * (c : ℝ) = 1 / 2 := by
    rw [hc]
    push_cast
    field_simp
  have h4 : ‖x - y‖ ≤ (1/2) * ‖x - y‖ := by
    calc ‖x - y‖ ≤ (K : ℝ) * ‖J (x - y)‖ := h2
      _ ≤ (K : ℝ) * ((c : ℝ) * ‖x - y‖) := h3
      _ = ((K : ℝ) * (c : ℝ)) * ‖x - y‖ := by ring
      _ = (1/2) * ‖x - y‖ := by rw [hKc]
  have h5 : ‖x - y‖ ≤ 0 := by linarith
  have : x - y = 0 := norm_le_zero_iff.1 h5
  exact sub_eq_zero.1 this

/-- **What local identifiability buys the set-valued core**: on a neighbourhood
where the measurement map is injective, exact readings leave exactly one
parameter.  The local analogue of `MultiParameterRegion.exact_readings_identify`. -/
theorem exact_readings_pin_down_locally (F : ParamFamily (Fin n → ℝ)) (ts : Fin m → ℝ)
    {s : Set (Fin n → ℝ)} (hinj : InjOn (measurementMap F ts) s)
    (θ : Fin n → ℝ) (E : List Reading)
    (hE : ∀ i : Fin m, ∃ r ∈ E, r.time = ts i ∧ r.tol = 0 ∧ r.value = F.predict θ (ts i))
    {ϑ : Fin n → ℝ} (hϑs : ϑ ∈ s) (hθs : θ ∈ s) (hϑ : ϑ ∈ Compatible F E) :
    ϑ = θ := by
  refine hinj hϑs hθs ?_
  funext i
  obtain ⟨r, hrE, hrt, hrtol, hrv⟩ := hE i
  have hfit : |r.value - F.predict ϑ r.time| ≤ r.tol := hϑ.2 r hrE
  rw [hrtol] at hfit
  have : r.value - F.predict ϑ r.time = 0 := by
    have := abs_nonneg (r.value - F.predict ϑ r.time)
    have h0 : |r.value - F.predict ϑ r.time| = 0 := le_antisymm hfit this
    exact abs_eq_zero.1 h0
  simp only [measurementMap]
  have hval : r.value = F.predict ϑ r.time := by linarith
  rw [hrt] at hval
  rw [← hval]
  exact hrv

/-! ## §3 Deficient rank: invisible directions -/

/-- A non-injective Jacobian *is* an invisible direction. -/
theorem invisible_direction_of_not_injective (J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (hJ : ¬ Function.Injective J) : ∃ v, InvisibleDirection J v := by
  have hker : LinearMap.ker (J : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) ≠ ⊥ := by
    intro h
    exact hJ (LinearMap.ker_eq_bot.1 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, hv⟩

/-- **An invisible direction is invisible to the data, to first order**: moving
the parameter along it changes no predicted reading at first order. -/
theorem invisible_direction_vanishes_to_first_order {h : (Fin n → ℝ) → (Fin m → ℝ)}
    {θ v : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}
    (hd : HasFDerivAt h J θ) (hv : InvisibleDirection J v) :
    HasDerivAt (fun t : ℝ => h (θ + t • v)) 0 0 := by
  have hline : HasDerivAt (fun t : ℝ => θ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add θ
  have h0 : (fun t : ℝ => θ + t • v) 0 = θ := by simp
  have hd' : HasFDerivAt h J ((fun t : ℝ => θ + t • v) 0) := by rw [h0]; exact hd
  have hcomp := hd'.comp_hasDerivAt (0:ℝ) hline
  simpa [Function.comp, hv.2] using hcomp

/-- **The rank obstruction, with no affineness hypothesis.**  Fewer measurement
times than parameters forces an invisible direction, for *every* model and at
*every* operating point: this is a counting fact about the Jacobian, not a
property of a particular family. -/
theorem few_measurements_give_invisible_direction (hmn : m < n)
    (J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) : ∃ v, InvisibleDirection J v := by
  refine invisible_direction_of_not_injective J (fun hinj => ?_)
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (J : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))) hinj
  simp only [Module.finrank_pi, Fintype.card_fin] at hle
  omega

/-- **Better tolerance cannot repair missing rank.**  The obstruction is a
statement about the derivative, so it is unchanged by any hypothesis about
instrument tolerances: the same invisible direction is there for every tolerance
the analyst might declare. -/
theorem tolerance_cannot_repair_missing_rank (hmn : m < n)
    (J : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :
    ∀ _tol : ℝ, ∃ v, InvisibleDirection J v :=
  fun _ => few_measurements_give_invisible_direction hmn J

/-! ## §4 Negatives -/

/-- **The first-order test is only a first-order test.**  The map `x ↦ x³` has
derivative `0` at `0`, so the Jacobian rank is deficient there, yet it is
globally injective: rank deficiency exposes a direction the data cannot see *to
first order*, and is not a proof of non-identifiability. -/
theorem first_order_test_is_only_first_order :
    ∃ f : ℝ → ℝ, HasDerivAt f 0 0 ∧ Function.Injective f := by
  refine ⟨fun x => x ^ 3, ?_, ?_⟩
  · simpa using hasDerivAt_pow 3 (0:ℝ)
  · intro x y hxy
    exact Odd.strictMono_pow (R := ℝ) (by norm_num) |>.injective hxy

/-- **Local identifiability is not global identifiability.**  A map can have an
injective derivative at a point — hence be locally identifiable there — and
still fail to be injective on the prior region. -/
theorem local_identifiability_is_not_global :
    ∃ f : ℝ → ℝ, (∃ s ∈ 𝓝 (1:ℝ), InjOn f s) ∧ ¬ Function.Injective f := by
  refine ⟨fun x => x ^ 2, ⟨Ioi 0, Ioi_mem_nhds (by norm_num), ?_⟩, ?_⟩
  · intro x hx y hy hxy
    have hx' : (0:ℝ) < x := hx
    have hy' : (0:ℝ) < y := hy
    nlinarith [hxy]
  · intro hinj
    have := hinj (a₁ := (1:ℝ)) (a₂ := (-1:ℝ)) (by norm_num)
    norm_num at this

end Integration.Experiment.LocalIdentifiability
