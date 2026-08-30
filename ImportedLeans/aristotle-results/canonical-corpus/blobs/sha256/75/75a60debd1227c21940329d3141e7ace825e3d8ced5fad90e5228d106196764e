import Mathlib
import Integration.Experiment.LocalIdentifiability

/-!
# Stage 7, lane 5 — a certified radius of identifiability

`TOE_STAGE6_INFERENCE.md` frontier item 6 records the gap closed here:

> **Local identifiability is local and first-order.**  No global identifiability,
> no radius estimate for the neighbourhood, no rank condition checked
> automatically for a given family.

Stage 6 proved "a full-rank Jacobian at `θ₀` gives injectivity on *some*
neighbourhood".  That is not operational: an experimenter cannot act on an
unquantified neighbourhood.  This file replaces it with

```
σ_min(J(θ₀)) ≥ c > 0        (the derivative is bounded below)
‖J(θ) − J(θ₀)‖ ≤ L‖θ − θ₀‖  (curvature control)
L · r < c                    ⟹  the map is injective on ball(θ₀, r)
```

so that "locally identifiable" becomes **"certifiably identifiable within
radius `r`"**, with `r = c/(2L)` always admissible.

## The hypotheses, stated pointwise

Both hypotheses are stated *pointwise on vectors* — `∀ v, c‖v‖ ≤ ‖J v‖` and
`∀ v, ‖(J θ − J θ₀) v‖ ≤ L‖θ − θ₀‖‖v‖` — because that is the form an analyst can
check for a concrete model, and it implies the operator-norm form used by the
mean value inequality (`opNorm_bound_of_pointwise`).

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `opNorm_bound_of_pointwise` | theorem | the pointwise Lipschitz bound gives the operator-norm bound the MVT needs |
| **`injOn_ball_of_lipschitz_deriv`** | theorem | the quantitative injectivity theorem above |
| **`certifiably_identifiable_within_radius`** | theorem | the explicit admissible radius `c/(2L)` |
| `locallyIdentifiable_of_certified_radius` | theorem | it implies the Stage-6 qualitative statement |
| `readings_pin_down_within_the_certified_radius` | theorem | the payoff: exact readings identify the parameter *inside a known ball* |
| `quadraticMap_certified_radius` | theorem | worked scalar instance `θ ↦ θ + θ²/2`: certified radius `1/2` |
| `certified_radius_is_not_maximal` | negative | the same map is injective on the strictly larger ball of radius `1` — the certificate is sufficient, not sharp |
| `no_radius_without_curvature_control` | negative | with `L` unbounded the certified radius collapses to `0`: a derivative bound alone certifies nothing |

## Claim boundary

The theorem is about a declared map `f` with a declared derivative family `D`;
`c` and `L` are declared constants whose hypotheses must be discharged for each
model.  Nothing here estimates `c` or `L` from data, and injectivity of the
measurement map is not a statement about noise.
-/

namespace Integration.Experiment.IdentifiabilityRadius

open Set Metric
open Integration.Experiment.ParameterRegion
open Integration.Experiment.LocalIdentifiability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## §1 From a pointwise bound to an operator-norm bound -/

/-- A pointwise bound on a continuous linear map is an operator-norm bound. -/
theorem opNorm_bound_of_pointwise (T : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, ‖T v‖ ≤ C * ‖v‖) : ‖T‖ ≤ C :=
  T.opNorm_le_bound hC h

/-! ## §2 The quantitative injectivity theorem -/

/-- **Certified injectivity on a ball.**

If at the operating point the derivative is bounded below by `c > 0`, and on the
ball of radius `r` the derivative moves at most `L‖θ − θ₀‖` away from it, then
`L·r < c` forces `f` to be injective on that ball.

This is the quantitative successor of
`LocalIdentifiability.locallyIdentifiable_of_injective_deriv`: the neighbourhood
is no longer existential.

(`0 < c` is not a hypothesis: on a nonempty ball it follows from `L·r < c` and
`0 ≤ L`, and on an empty ball the conclusion is vacuous.) -/
theorem injOn_ball_of_lipschitz_deriv {f : E → F} {D : E → (E →L[ℝ] F)} {θ₀ : E}
    {c L r : ℝ} (hL : 0 ≤ L)
    (hlow : ∀ v, c * ‖v‖ ≤ ‖D θ₀ v‖)
    (hd : ∀ θ ∈ ball θ₀ r, HasFDerivAt f (D θ) θ)
    (hlip : ∀ θ ∈ ball θ₀ r, ∀ v, ‖D θ v - D θ₀ v‖ ≤ L * ‖θ - θ₀‖ * ‖v‖)
    (hLr : L * r < c) :
    InjOn f (ball θ₀ r) := by
  by_cases hrpos : 0 ≤ r
  swap
  · push_neg at hrpos
    rw [ball_eq_empty.2 (le_of_lt hrpos)]
    exact injOn_empty _
  -- the remainder `g = f − J₀` has derivative `D θ − D θ₀`, of norm `≤ L r`
  set g : E → F := fun θ => f θ - D θ₀ θ with hg
  have hgd : ∀ θ ∈ ball θ₀ r, HasFDerivWithinAt g (D θ - D θ₀) (ball θ₀ r) θ := by
    intro θ hθ
    exact ((hd θ hθ).sub (D θ₀).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ θ ∈ ball θ₀ r, ‖D θ - D θ₀‖ ≤ L * r := by
    intro θ hθ
    refine opNorm_bound_of_pointwise _ (mul_nonneg hL hrpos) (fun v => ?_)
    have hθr : ‖θ - θ₀‖ ≤ r := le_of_lt (by simpa [dist_eq_norm] using hθ)
    have h1 : ‖(D θ - D θ₀) v‖ ≤ L * ‖θ - θ₀‖ * ‖v‖ := by
      simpa using hlip θ hθ v
    have h2 : L * ‖θ - θ₀‖ * ‖v‖ ≤ L * r * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθr hL) (norm_nonneg v)
    linarith
  have hmvt : ∀ θ₁ ∈ ball θ₀ r, ∀ θ₂ ∈ ball θ₀ r, ‖g θ₂ - g θ₁‖ ≤ (L * r) * ‖θ₂ - θ₁‖ := by
    intro θ₁ h1 θ₂ h2
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hgd hbound (convex_ball θ₀ r) h1 h2
  intro θ₁ h1 θ₂ h2 hfeq
  by_contra hne
  have hΔ : 0 < ‖θ₂ - θ₁‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hne h.symm
  have hkey : ‖g θ₂ - g θ₁‖ = ‖D θ₀ (θ₂ - θ₁)‖ := by
    have : g θ₂ - g θ₁ = -(D θ₀ (θ₂ - θ₁)) := by
      simp only [hg, map_sub]
      rw [hfeq]
      abel
    rw [this, norm_neg]
  have hlb : c * ‖θ₂ - θ₁‖ ≤ ‖D θ₀ (θ₂ - θ₁)‖ := hlow _
  have hub := hmvt θ₁ h1 θ₂ h2
  rw [hkey] at hub
  nlinarith

/-- **The explicit radius.**  With a derivative bounded below by `c` and a
Lipschitz constant `L > 0` for the derivative, the map is injective on the ball
of radius `c / (2L)`.  This is the operational form:

```
locally identifiable   ⟹   certifiably identifiable within radius c/(2L).
```
-/
theorem certifiably_identifiable_within_radius {f : E → F} {D : E → (E →L[ℝ] F)} {θ₀ : E}
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hlow : ∀ v, c * ‖v‖ ≤ ‖D θ₀ v‖)
    (hd : ∀ θ ∈ ball θ₀ (c / (2 * L)), HasFDerivAt f (D θ) θ)
    (hlip : ∀ θ ∈ ball θ₀ (c / (2 * L)), ∀ v, ‖D θ v - D θ₀ v‖ ≤ L * ‖θ - θ₀‖ * ‖v‖) :
    InjOn f (ball θ₀ (c / (2 * L))) := by
  refine injOn_ball_of_lipschitz_deriv (le_of_lt hL) hlow hd hlip ?_
  have h : L * (c / (2 * L)) = c / 2 := by field_simp
  rw [h]
  linarith

/-- The certified radius implies the Stage-6 qualitative statement. -/
theorem locallyIdentifiable_of_certified_radius {n m : ℕ} {h : (Fin n → ℝ) → (Fin m → ℝ)}
    {θ₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hinj : InjOn h (ball θ₀ r)) :
    LocallyIdentifiable h θ₀ :=
  ⟨ball θ₀ r, ball_mem_nhds θ₀ hr, hinj⟩

/-! ## §3 The payoff for the surviving region -/

/-- **Exact readings identify the parameter inside a known ball.**  Combining the
certified radius with the Stage-6 set-valued theorem: if the true parameter and
a candidate both lie within the certified radius, exact readings force them to
coincide.  Unlike the Stage-6 version, the analyst knows how far "within" is. -/
theorem readings_pin_down_within_the_certified_radius {n m : ℕ}
    (Fam : ParamFamily (Fin n → ℝ)) (ts : Fin m → ℝ) {θ₀ : Fin n → ℝ} {r : ℝ}
    (hinj : InjOn (measurementMap Fam ts) (ball θ₀ r))
    (θ : Fin n → ℝ) (Ev : List Reading)
    (hE : ∀ i : Fin m, ∃ rd ∈ Ev, rd.time = ts i ∧ rd.tol = 0 ∧ rd.value = Fam.predict θ (ts i))
    {ϑ : Fin n → ℝ} (hϑ : ϑ ∈ ball θ₀ r) (hθ : θ ∈ ball θ₀ r)
    (hcomp : ϑ ∈ Compatible Fam Ev) :
    ϑ = θ :=
  exact_readings_pin_down_locally Fam ts hinj θ Ev hE hϑ hθ hcomp

/-! ## §4 A worked scalar instance -/

/-- The model `θ ↦ θ + θ²/2`, a one-parameter family with genuine curvature. -/
noncomputable def quadraticMap : ℝ → ℝ := fun θ => θ + θ ^ 2 / 2

/-- Its derivative, as a continuous linear map. -/
noncomputable def quadraticDeriv (θ : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 + θ)

theorem quadraticMap_hasFDerivAt (θ : ℝ) :
    HasFDerivAt quadraticMap (quadraticDeriv θ) θ := by
  have h : HasDerivAt quadraticMap (1 + θ) θ := by
    have : HasDerivAt (fun x : ℝ => x + x ^ 2 / 2) (1 + (2 * θ ^ 1) / 2) θ := by
      simpa using (hasDerivAt_id θ).add (((hasDerivAt_pow 2 θ).div_const 2))
    simpa [quadraticMap] using this.congr_deriv (by ring)
  exact h.hasFDerivAt

@[simp] theorem quadraticDeriv_apply (θ v : ℝ) : quadraticDeriv θ v = v * (1 + θ) := by
  simp [quadraticDeriv]

/-- **The certified radius of the worked instance is `1/2`**: at `θ₀ = 0` the
derivative is `1` (so `c = 1`) and the derivative is `1`-Lipschitz (so `L = 1`). -/
theorem quadraticMap_certified_radius : InjOn quadraticMap (ball (0 : ℝ) (1 / 2)) := by
  have h : (1 : ℝ) / 2 = 1 / (2 * 1) := by norm_num
  rw [h]
  refine certifiably_identifiable_within_radius (D := quadraticDeriv) one_pos one_pos
    (fun v => ?_) (fun θ _ => quadraticMap_hasFDerivAt θ) (fun θ _ v => ?_)
  · simp
  · simp only [quadraticDeriv_apply, Real.norm_eq_abs, sub_zero]
    have : v * (1 + θ) - v * (1 + 0) = θ * v := by ring
    rw [this, abs_mul]
    simp [mul_comm]

/-- **The certificate is sufficient, not sharp.**  The same map is injective on
the ball of radius `1`, which strictly contains the certified ball of radius
`1/2`.  A certified radius is a guarantee, never a boundary of identifiability. -/
theorem certified_radius_is_not_maximal :
    InjOn quadraticMap (ball (0 : ℝ) 1) ∧ ball (0 : ℝ) (1 / 2) ⊂ ball (0 : ℝ) 1 := by
  constructor
  · intro x hx y hy hxy
    simp only [mem_ball, Real.dist_eq, sub_zero, abs_lt] at hx hy
    simp only [quadraticMap] at hxy
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  · refine ⟨ball_subset_ball (by norm_num), ?_⟩
    intro hsub
    have h : (0.7 : ℝ) ∈ ball (0 : ℝ) 1 := by
      simp only [mem_ball, Real.dist_eq, sub_zero]
      norm_num
    have := hsub h
    simp only [mem_ball, Real.dist_eq, sub_zero] at this
    norm_num at this

/-- **Without curvature control there is no radius.**  The certified radius
`c/(2L)` tends to `0` as the derivative's Lipschitz constant grows: a lower
bound on the derivative at a point, alone, certifies injectivity on no ball of
any declared size. -/
theorem no_radius_without_curvature_control (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ c / (2 * L) < ε := by
  refine ⟨c / ε, by positivity, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  have h : ε * (2 * (c / ε)) = 2 * c := by field_simp
  rw [h]
  linarith

end Integration.Experiment.IdentifiabilityRadius
