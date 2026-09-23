import Mathlib

/-!
# The smooth normalized logarithmic window (Lemma 3.1 of the pole–quotient manuscript)

`Riemann_Pole_Quotient_Reduction_2026.pdf` §3 fixes a `C²` bump `ψ : ℝ → ℝ≥0`
supported in `[-1,1]` and positive at the origin, and for `c > e > 0` forms the
symmetrized, normalized taper

```
ψ_{c,e}(u) = ψ ((u - c)/e),    g^raw_{c,e}(u) = ψ_{c,e}(u) + ψ_{c,e}(-u),
M_{c,e}    = ∫ g^raw_{c,e},    g_{c,e}      = M_{c,e}⁻¹ • g^raw_{c,e}.
```

Lemma 3.1 asserts that `g_{c,e}` is even, nonnegative, `C²`, compactly
supported, of unit mass, supported in the annulus `c - e ≤ |u| ≤ c + e`, and
positive at `u = c`.  This module proves exactly that, over an arbitrary
admissible profile `ψ` packaged as `BumpProfile`, and exhibits one concrete
profile (`stdBumpProfile`, built from Mathlib's `ContDiffBump`) so that the
statements are not vacuous.

Nothing in this file mentions the zeta function: the window is a piece of real
analysis that the explicit-formula argument later consumes.
-/

namespace Integration.RiemannPoleQuotient

open MeasureTheory Function

/-! ## 1. Admissible bump profiles -/

/-- An admissible profile `ψ` for the manuscript's window construction: a `C²`,
nonnegative function supported in `[-1,1]` and positive at the origin. -/
structure BumpProfile where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- Nonnegativity. -/
  nonneg' : ∀ u, 0 ≤ toFun u
  /-- `C²` regularity. -/
  contDiff' : ContDiff ℝ 2 toFun
  /-- Support inside `[-1,1]`. -/
  support' : ∀ u, 1 < |u| → toFun u = 0
  /-- Positivity at the centre. -/
  pos_zero' : 0 < toFun 0

namespace BumpProfile

instance : CoeFun BumpProfile fun _ => ℝ → ℝ := ⟨BumpProfile.toFun⟩

variable (ψ : BumpProfile)

theorem nonneg (u : ℝ) : 0 ≤ ψ u := ψ.nonneg' u

theorem contDiff : ContDiff ℝ 2 (ψ : ℝ → ℝ) := ψ.contDiff'

theorem continuous : Continuous (ψ : ℝ → ℝ) := ψ.contDiff'.continuous

theorem eq_zero_of_one_lt_abs {u : ℝ} (hu : 1 < |u|) : ψ u = 0 := ψ.support' u hu

theorem pos_zero : 0 < ψ 0 := ψ.pos_zero'

/-- The support is contained in `[-1,1]`; contrapositive of `support'`. -/
theorem abs_le_one_of_ne_zero {u : ℝ} (hu : ψ u ≠ 0) : |u| ≤ 1 := by
  by_contra h
  exact hu (ψ.eq_zero_of_one_lt_abs (lt_of_not_ge h))

end BumpProfile

/-- Mathlib's `ContDiffBump` at the origin with inner radius `1/2` and outer
radius `1`, as an admissible profile.  It witnesses that `BumpProfile` is
inhabited. -/
noncomputable def stdBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The standard admissible profile. -/
noncomputable def stdBumpProfile : BumpProfile where
  toFun := stdBump
  nonneg' _ := stdBump.nonneg
  contDiff' := stdBump.contDiff
  support' u hu := by
    have : u ∉ Function.support (stdBump : ℝ → ℝ) := by
      rw [stdBump.support_eq]
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
      exact le_of_lt hu
    simpa [Function.mem_support] using this
  pos_zero' := by
    have : (stdBump : ℝ → ℝ) 0 = 1 :=
      stdBump.one_of_mem_closedBall (by simp [stdBump])
    rw [this]; norm_num

noncomputable instance : Inhabited BumpProfile := ⟨stdBumpProfile⟩

/-! ## 2. The window -/

variable (ψ : BumpProfile) (c e : ℝ)

/-- The unnormalized symmetrized window `g^raw_{c,e}`. -/
noncomputable def rawWindow : ℝ → ℝ := fun u => ψ ((u - c) / e) + ψ ((-u - c) / e)

/-- The normalizing mass `M_{c,e} = ∫ g^raw_{c,e}`. -/
noncomputable def windowMass : ℝ := ∫ u : ℝ, rawWindow ψ c e u

/-- The normalized window `g_{c,e} = M_{c,e}⁻¹ • g^raw_{c,e}`. -/
noncomputable def window : ℝ → ℝ := fun u => (windowMass ψ c e)⁻¹ * rawWindow ψ c e u

variable {ψ c e}

/-! ### Elementary structure of the raw window -/

theorem rawWindow_even (u : ℝ) : rawWindow ψ c e (-u) = rawWindow ψ c e u := by
  simp only [rawWindow, neg_neg]
  ring_nf

theorem rawWindow_nonneg (u : ℝ) : 0 ≤ rawWindow ψ c e u :=
  add_nonneg (ψ.nonneg _) (ψ.nonneg _)

theorem rawWindow_contDiff : ContDiff ℝ 2 (rawWindow ψ c e) := by
  have h₁ : ContDiff ℝ 2 fun u : ℝ => ((u - c) / e) := by
    exact ((contDiff_id.sub contDiff_const).div_const e)
  have h₂ : ContDiff ℝ 2 fun u : ℝ => ((-u - c) / e) := by
    exact (((contDiff_id.neg).sub contDiff_const).div_const e)
  exact (ψ.contDiff.comp h₁).add (ψ.contDiff.comp h₂)

/-- **Support of the raw window.**  If `0 < e < c` then the raw window vanishes
outside the annulus `c - e ≤ |u| ≤ c + e`. -/
theorem rawWindow_support {u : ℝ} (he : 0 < e) (hce : e < c)
    (hu : rawWindow ψ c e u ≠ 0) : c - e ≤ |u| ∧ |u| ≤ c + e := by
  have key : ∀ v : ℝ, ψ ((v - c) / e) ≠ 0 → c - e ≤ v ∧ v ≤ c + e := by
    intro v hv
    have h := ψ.abs_le_one_of_ne_zero hv
    rw [abs_div, abs_of_pos he, div_le_one he] at h
    have := abs_le.mp h
    constructor <;> linarith [this.1, this.2]
  by_cases h : ψ ((u - c) / e) ≠ 0
  · obtain ⟨h1, h2⟩ := key u h
    have hupos : 0 < u := by linarith
    rw [abs_of_pos hupos]
    exact ⟨h1, h2⟩
  · have h' : ψ ((-u - c) / e) ≠ 0 := by
      intro h2
      exact hu (by simp only [rawWindow, not_not.mp h, h2, add_zero])
    obtain ⟨h1, h2⟩ := key (-u) h'
    have huneg : u < 0 := by linarith
    rw [abs_of_neg huneg]
    exact ⟨h1, h2⟩

theorem rawWindow_hasCompactSupport (he : 0 < e) (hce : e < c) :
    HasCompactSupport (rawWindow ψ c e) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(c + e)) (b := c + e))
  intro x hx
  by_contra hne
  obtain ⟨-, h2⟩ := rawWindow_support he hce hne
  exact hx (Set.mem_Icc.mpr ⟨by cases abs_le.mp h2 with | intro l r => linarith,
    by cases abs_le.mp h2 with | intro l r => linarith⟩)

theorem rawWindow_integrable (he : 0 < e) (hce : e < c) :
    Integrable (rawWindow ψ c e) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (rawWindow_hasCompactSupport he hce)
  exact rawWindow_contDiff.continuous

theorem rawWindow_pos_at_centre : 0 < rawWindow ψ c e c := by
  have h : ψ ((c - c) / e) = ψ 0 := by norm_num
  have := ψ.pos_zero
  have h2 : 0 ≤ ψ ((-c - c) / e) := ψ.nonneg _
  simp only [rawWindow]
  rw [h]
  linarith

/-- **The normalizing mass is positive.** -/
theorem windowMass_pos (he : 0 < e) (hce : e < c) : 0 < windowMass ψ c e := by
  rw [windowMass, integral_pos_iff_support_of_nonneg (fun u => rawWindow_nonneg u)
      (rawWindow_integrable he hce)]
  have hopen : IsOpen {u : ℝ | 0 < rawWindow ψ c e u} :=
    isOpen_lt continuous_const rawWindow_contDiff.continuous
  have hsub : {u : ℝ | 0 < rawWindow ψ c e u} ⊆ Function.support (rawWindow ψ c e) :=
    fun u hu => ne_of_gt hu
  have hne : {u : ℝ | 0 < rawWindow ψ c e u}.Nonempty := ⟨c, rawWindow_pos_at_centre⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono hsub)

/-! ### Lemma 3.1 -/

/-- Evenness. -/
theorem window_even (u : ℝ) : window ψ c e (-u) = window ψ c e u := by
  simp [window, rawWindow_even]

/-- Nonnegativity. -/
theorem window_nonneg (he : 0 < e) (hce : e < c) (u : ℝ) : 0 ≤ window ψ c e u :=
  mul_nonneg (inv_nonneg.mpr (windowMass_pos he hce).le) (rawWindow_nonneg u)

/-- `C²` regularity. -/
theorem window_contDiff : ContDiff ℝ 2 (window ψ c e) :=
  contDiff_const.mul rawWindow_contDiff

/-- Compact support. -/
theorem window_hasCompactSupport (he : 0 < e) (hce : e < c) :
    HasCompactSupport (window ψ c e) :=
  (rawWindow_hasCompactSupport he hce).mul_left

/-- Support inside the annulus `c - e ≤ |u| ≤ c + e`. -/
theorem window_support {u : ℝ} (he : 0 < e) (hce : e < c) (hu : window ψ c e u ≠ 0) :
    c - e ≤ |u| ∧ |u| ≤ c + e := by
  refine rawWindow_support (ψ := ψ) he hce ?_
  intro h
  exact hu (by simp only [window, h, mul_zero])

/-- Unit mass. -/
theorem window_integral_eq_one (he : 0 < e) (hce : e < c) :
    ∫ u : ℝ, window ψ c e u = 1 := by
  have h : (∫ u : ℝ, window ψ c e u) = (windowMass ψ c e)⁻¹ * windowMass ψ c e :=
    integral_const_mul (windowMass ψ c e)⁻¹ (rawWindow ψ c e)
  rw [h]
  exact inv_mul_cancel₀ (ne_of_gt (windowMass_pos he hce))

/-- Positivity at `u = c`. -/
theorem window_pos_at_centre (he : 0 < e) (hce : e < c) : 0 < window ψ c e c :=
  mul_pos (inv_pos.mpr (windowMass_pos he hce)) rawWindow_pos_at_centre

/-- Integrability of the normalized window. -/
theorem window_integrable (he : 0 < e) (hce : e < c) : Integrable (window ψ c e) :=
  (rawWindow_integrable he hce).const_mul _

/-- **Lemma 3.1 (smooth normalized window).**  For `c > e > 0` the taper
`g_{c,e}` is even, nonnegative, `C²`, compactly supported, has unit mass, is
supported in `c - e ≤ |u| ≤ c + e`, and is positive at `u = c`. -/
theorem smooth_normalized_window (ψ : BumpProfile) {c e : ℝ} (he : 0 < e) (hce : e < c) :
    (∀ u, window ψ c e (-u) = window ψ c e u) ∧
    (∀ u, 0 ≤ window ψ c e u) ∧
    ContDiff ℝ 2 (window ψ c e) ∧
    HasCompactSupport (window ψ c e) ∧
    (∫ u : ℝ, window ψ c e u) = 1 ∧
    (∀ u, window ψ c e u ≠ 0 → c - e ≤ |u| ∧ |u| ≤ c + e) ∧
    0 < window ψ c e c :=
  ⟨fun u => window_even u, fun u => window_nonneg he hce u, window_contDiff,
    window_hasCompactSupport he hce, window_integral_eq_one he hce,
    fun _ hu => window_support he hce hu, window_pos_at_centre he hce⟩

/-! ### The short-window regime

The manuscript singles out the regime `0 < c - e < c + e < log 2`, in which the
whole support of `g_{c,e}` lies in `|u| < log 2`. -/

/-- In the short-window regime the support of `g_{c,e}` lies in `|u| < log 2`. -/
theorem window_support_lt_log_two {u : ℝ} (he : 0 < e) (hce : e < c)
    (hshort : c + e < Real.log 2) (hu : window ψ c e u ≠ 0) : |u| < Real.log 2 :=
  lt_of_le_of_lt (window_support he hce hu).2 hshort

end Integration.RiemannPoleQuotient
