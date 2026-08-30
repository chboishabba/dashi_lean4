/-
# The A-side scale Gram dichotomy

The A-side analogue of the transverse-coercivity geometry: instead of trying to
force a sign on the raw scale flux, measure the departure of the profile from
its own scaling orbit by a **Gram determinant**.

For a nonnegative weight `Γ` (the Gaussian/localizing kernel of the rescaled
problem), a profile `u` and the scaling generator

  `Λu = u + (x − x₀)·∇u + 2(t − t₀)∂_tu`      (`ClayNS.scaleGen`)

put

  `A = ∫Γ|u|²`,  `B = ∫Γ|Λu|²`,  `C = ∫Γ⟨u,Λu⟩`,  `Δ = AB − C²`.

This file proves, with no hypothesis beyond `Γ ≥ 0` and integrability:

* `ClayNS.gram_deficit_identity` — the exact quadratic expansion
  `∫Γ|Λu − cu|² = B − 2cC + c²A` for every `c`;
* `ClayNS.gramDefect_nonneg` — `Δ ≥ 0` (weighted Cauchy–Schwarz);
* `ClayNS.gram_orbit_distance` — the exact identity `∫Γ|Λu − (C/A)u|² = Δ/A`
  when `A > 0`: the Gram defect *is* (up to the normalization `A`) the squared
  weighted distance of the scaling derivative to the line spanned by the
  profile;
* `ClayNS.gaussian_scale_gram_dichotomy` — the resulting dichotomy: at each
  scale either `Δ ≥ εA` (a coercive scale cost) or the profile is
  `ε`-approximately invariant along the scaling orbit, `∫Γ|Λu − cu|² < ε`, i.e.
  approximately backward self-similar;
* `ClayNS.gram_orbit_exact` — the degenerate case: `Δ = 0` with `A > 0` forces
  `Λu = (C/A)u` in the weighted `L²` sense (exact self-similarity of the
  profile).

Nothing here is assumed: these are unconditional statements about the weighted
Gram determinant.  What is *not* claimed is that the near-self-similar branch is
impossible; that is the remaining A-side obligation.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementModulusGram

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

variable {α : Type*} [MeasurableSpace α]

/-! ## Weighted Gram quantities -/

/-- The weighted squared norm `∫Γ|f|²`. -/
def gramA (μ : Measure α) (Gam : α → ℝ) (f : α → E3) : ℝ :=
  ∫ x, Gam x * ∑ a, (f x a) ^ 2 ∂μ

/-- The weighted pairing `∫Γ⟨f,g⟩`. -/
def gramC (μ : Measure α) (Gam : α → ℝ) (f g : α → E3) : ℝ :=
  ∫ x, Gam x * ∑ a, f x a * g x a ∂μ

/-- The weighted Gram determinant `Δ = AB − C²`. -/
def gramDefect (μ : Measure α) (Gam : α → ℝ) (f g : α → E3) : ℝ :=
  gramA μ Gam f * gramA μ Gam g - (gramC μ Gam f g) ^ 2

lemma gramA_nonneg {μ : Measure α} {Gam : α → ℝ} (hGam : ∀ x, 0 ≤ Gam x) (f : α → E3) :
    0 ≤ gramA μ Gam f :=
  integral_nonneg fun x => mul_nonneg (hGam x) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **The exact quadratic expansion.**  `∫Γ|g − cf|² = B − 2cC + c²A`. -/
theorem gram_deficit_identity {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ) (c : ℝ) :
    ∫ x, Gam x * ∑ a, (g x a - c * f x a) ^ 2 ∂μ
      = gramA μ Gam g - 2 * c * gramC μ Gam f g + c ^ 2 * gramA μ Gam f := by
  have hpt : ∀ x, Gam x * ∑ a, (g x a - c * f x a) ^ 2
      = (Gam x * ∑ a, (g x a) ^ 2) - 2 * c * (Gam x * ∑ a, f x a * g x a)
        + c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2) := by
    intro x
    simp only [Fin.sum_univ_three]
    ring
  have hcongr : ∫ x, Gam x * ∑ a, (g x a - c * f x a) ^ 2 ∂μ
      = ∫ x, ((Gam x * ∑ a, (g x a) ^ 2) - 2 * c * (Gam x * ∑ a, f x a * g x a)
          + c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2)) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hI2 : Integrable (fun x => 2 * c * (Gam x * ∑ a, f x a * g x a)) μ :=
    hfg.const_mul _
  have hI3 : Integrable (fun x => c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2)) μ := hf.const_mul _
  have e1 : ∫ x, ((Gam x * ∑ a, (g x a) ^ 2)
        - 2 * c * (Gam x * ∑ a, f x a * g x a)
        + c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2)) ∂μ
      = (∫ x, ((Gam x * ∑ a, (g x a) ^ 2)
            - 2 * c * (Gam x * ∑ a, f x a * g x a)) ∂μ)
        + ∫ x, c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2) ∂μ :=
    integral_add (hg.sub hI2) hI3
  have e2 : ∫ x, ((Gam x * ∑ a, (g x a) ^ 2)
        - 2 * c * (Gam x * ∑ a, f x a * g x a)) ∂μ
      = (∫ x, Gam x * ∑ a, (g x a) ^ 2 ∂μ)
        - ∫ x, 2 * c * (Gam x * ∑ a, f x a * g x a) ∂μ :=
    integral_sub hg hI2
  have e3 : ∫ x, 2 * c * (Gam x * ∑ a, f x a * g x a) ∂μ = 2 * c * gramC μ Gam f g :=
    integral_const_mul _ _
  have e4 : ∫ x, c ^ 2 * (Gam x * ∑ a, (f x a) ^ 2) ∂μ = c ^ 2 * gramA μ Gam f :=
    integral_const_mul _ _
  rw [hcongr, e1, e2, e3, e4]
  rfl

/-- **The weighted Cauchy–Schwarz / Gram inequality.**  `Δ = AB − C² ≥ 0`. -/
theorem gramDefect_nonneg {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ) :
    0 ≤ gramDefect μ Gam f g := by
  set A := gramA μ Gam f with hA
  set B := gramA μ Gam g with hB
  set C := gramC μ Gam f g with hC
  have hquad : ∀ c : ℝ, 0 ≤ B - 2 * c * C + c ^ 2 * A := by
    intro c
    rw [← gram_deficit_identity hf hg hfg c]
    exact integral_nonneg fun x =>
      mul_nonneg (hGam x) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA0 : 0 ≤ A := gramA_nonneg hGam f
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · -- `A = 0` forces `C = 0`
    have hCzero : C = 0 := by
      by_contra hne
      have h := hquad ((B + 1) / (2 * C))
      rw [← hA0'] at h
      have h2 : 2 * ((B + 1) / (2 * C)) * C = B + 1 := by field_simp
      rw [h2] at h
      simp at h
      linarith
    simp [gramDefect, ← hA, ← hB, ← hC, ← hA0', hCzero]
  · have h := hquad (C / A)
    have hne : A ≠ 0 := ne_of_gt hApos
    have hexp : B - 2 * (C / A) * C + (C / A) ^ 2 * A = B - C ^ 2 / A := by
      field_simp; ring
    rw [hexp] at h
    have : C ^ 2 / A ≤ B := by linarith
    rw [gramDefect, ← hA, ← hB, ← hC]
    rw [div_le_iff₀ hApos] at this
    nlinarith [this]

/-- **The Gram defect is the squared distance to the scaling orbit.**  If
`A > 0` then `∫Γ|g − (C/A)f|² = Δ/A`. -/
theorem gram_orbit_distance {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (hA : 0 < gramA μ Gam f) :
    ∫ x, Gam x * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ
      = gramDefect μ Gam f g / gramA μ Gam f := by
  rw [gram_deficit_identity hf hg hfg (gramC μ Gam f g / gramA μ Gam f), gramDefect]
  field_simp
  ring

/-- **The scale Gram dichotomy.**  For every threshold `ε > 0`: either the Gram
defect is coercive relative to the weighted mass of the profile, `εA ≤ Δ`, or
the scaling derivative is `ε`-close, in the weighted `L²` sense, to the line
spanned by the profile — i.e. the profile is approximately invariant along its
own scaling orbit. -/
theorem gaussian_scale_gram_dichotomy {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (hA : 0 < gramA μ Gam f) (eps : ℝ) :
    eps * gramA μ Gam f ≤ gramDefect μ Gam f g
      ∨ ∃ c : ℝ, ∫ x, Gam x * ∑ a, (g x a - c * f x a) ^ 2 ∂μ < eps := by
  by_cases hcase : eps * gramA μ Gam f ≤ gramDefect μ Gam f g
  · exact Or.inl hcase
  · refine Or.inr ⟨gramC μ Gam f g / gramA μ Gam f, ?_⟩
    rw [gram_orbit_distance hf hg hfg hA, div_lt_iff₀ hA]
    push_neg at hcase
    linarith [hcase]

/-- **The degenerate branch.**  `Δ = 0` with `A > 0` means the scaling
derivative is *exactly* collinear with the profile in the weighted `L²` sense:
the weighted defect integral vanishes. -/
theorem gram_orbit_exact {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (hA : 0 < gramA μ Gam f) (hzero : gramDefect μ Gam f g = 0) :
    ∫ x, Gam x * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ = 0 := by
  rw [gram_orbit_distance hf hg hfg hA, hzero, zero_div]

/-! ## The scaling generator of the parabolic rescaling -/

/-- The generator of the parabolic scaling orbit based at `z₀`,
`Λu = u + (x − x₀)·∇u + 2(t − t₀)∂_tu`. -/
def scaleGen (z0 : STime) (U : STime → E3) : STime → E3 := fun z =>
  U z + (∑ j, ((z.2 - z0.2) j) • dvec (0, ee j) U z)
    + (2 * (z.1 - z0.1)) • dvec (1, 0) U z

/-- The scale Gram defect of a profile: the Gram determinant of the pair
`(u, Λu)` in the weighted space. -/
def scaleGramDefect (μ : Measure STime) (Gam : STime → ℝ) (z0 : STime)
    (U : STime → E3) : ℝ :=
  gramDefect μ Gam U (scaleGen z0 U)

/-- **`GaussianScaleGramDichotomy` for the parabolic scaling generator.**  At
each localization scale, either the scale Gram defect is coercive, or the
profile is `ε`-approximately self-similar: the scaling derivative `Λu` is
within `ε` (weighted `L²`) of a multiple of `u`. -/
theorem gaussianScaleGram_dichotomy {μ : Measure STime} {Gam : STime → ℝ} {z0 : STime}
    {U : STime → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (U x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (scaleGen z0 U x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, U x a * scaleGen z0 U x a) μ)
    (hA : 0 < gramA μ Gam U) (eps : ℝ) :
    eps * gramA μ Gam U ≤ scaleGramDefect μ Gam z0 U
      ∨ ∃ c : ℝ, ∫ x, Gam x * ∑ a, (scaleGen z0 U x a - c * U x a) ^ 2 ∂μ < eps :=
  gaussian_scale_gram_dichotomy hf hg hfg hA eps

/-- The scale Gram defect is always nonnegative. -/
theorem scaleGramDefect_nonneg {μ : Measure STime} {Gam : STime → ℝ} {z0 : STime}
    {U : STime → E3} (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (U x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (scaleGen z0 U x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, U x a * scaleGen z0 U x a) μ) :
    0 ≤ scaleGramDefect μ Gam z0 U :=
  gramDefect_nonneg hGam hf hg hfg

end ClayNS
