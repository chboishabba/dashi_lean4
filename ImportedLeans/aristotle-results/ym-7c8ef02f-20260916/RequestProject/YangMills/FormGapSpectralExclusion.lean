/-
# From a quadratic-form lower bound to an actual spectral exclusion

`MassGapFormTransport` proves that a *quadratic-form* lower bound survives a
strong limit.  As stated there, that is a statement about forms only: it says
nothing about spectra.  This module supplies the missing spectral content in
the bounded setting, so that the phrase "no spectrum below the gap" is a
theorem rather than a gloss:

* `IsFormCoercive H c` — the form lower bound `c‖ψ‖² ≤ re ⟪ψ, Hψ⟫`;
* `norm_le_of_isFormCoercive`, `antilipschitz_of_isFormCoercive` — coercivity
  makes `H` bounded below, hence injective with closed range;
* `bijective_of_isFormCoercive` — the Lax–Milgram argument: the range of a
  coercive operator is dense as well, so `H` is bijective.  Note that **no**
  self-adjointness or symmetry is used;
* `notMem_spectrum_of_formLowerBound` and `spectrum_subset_halfPlane` — if
  `Δ‖ψ‖² ≤ re ⟪ψ, Hψ⟫` for every `ψ`, then every spectral value `z` of `H`
  obeys `Δ ≤ z.re`; in particular no real `λ < Δ` is in the spectrum;
* `spectrum_restrict_subset_halfPlane` — the physical version: if `H` has a
  form gap `Δ` above a vacuum `v` (in the sense of `MassGapFormTransport`) and
  leaves the orthogonal complement of the vacuum invariant, then the spectrum
  of the restriction of `H` to that complement lies in `{Δ ≤ re z}`;
* `spectrum_restrict_of_tendsto` — combining with the strong-limit transport:
  a strong limit of Hamiltonians with a *uniform* form gap `Δ` above the same
  vacuum has, on the vacuum complement, no spectrum with real part below `Δ`.
  This is "no spectral pollution from below", proved, for bounded operators.

Everything here is for bounded operators `E →L[ℂ] E`; the domain-theoretic
(unbounded) statements are developed in `UnboundedHamiltonianDomain` and
`UnboundedFormGapTransport`, and the passage from a form bound to the spectrum
of an unbounded self-adjoint operator is *not* claimed anywhere.
-/
import Mathlib
import RequestProject.YangMills.MassGapFormTransport

namespace RequestProject.YangMills.FormGapSpectralExclusion

open scoped InnerProductSpace
open Filter Topology
open RequestProject.YangMills.MassGapFormTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `H` is form coercive with constant `c`: `c‖ψ‖² ≤ re ⟪ψ, Hψ⟫` for all `ψ`.
For `c > 0` this is exactly the hypothesis of the Lax–Milgram theorem. -/
def IsFormCoercive (H : E →L[ℂ] E) (c : ℝ) : Prop :=
  ∀ ψ : E, c * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re

/-- A form-coercive operator is bounded below. -/
theorem norm_le_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ}
    (h : IsFormCoercive H c) (ψ : E) : c * ‖ψ‖ ^ 2 ≤ ‖ψ‖ * ‖H ψ‖ :=
  le_trans (h ψ) (le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _))

theorem mul_norm_le_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ}
    (h : IsFormCoercive H c) (ψ : E) : c * ‖ψ‖ ≤ ‖H ψ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg ψ) with hψ | hψ
  · simp [← hψ]
  · have h1 := norm_le_of_isFormCoercive h ψ
    have h2 : c * ‖ψ‖ * ‖ψ‖ ≤ ‖H ψ‖ * ‖ψ‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hψ

theorem antilipschitz_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) : AntilipschitzWith (c⁻¹.toNNReal) H := by
  refine ContinuousLinearMap.antilipschitz_of_bound H (fun ψ => ?_)
  have hb := mul_norm_le_of_isFormCoercive h ψ
  have hinv : ‖ψ‖ ≤ c⁻¹ * ‖H ψ‖ := (le_inv_mul_iff₀ hc).mpr hb
  simpa [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr hc)] using hinv

theorem injective_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) : Function.Injective H :=
  (antilipschitz_of_isFormCoercive hc h).injective

variable [CompleteSpace E]

theorem isClosed_range_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) :
    IsClosed ((LinearMap.range (H : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) := by
  have hr := (antilipschitz_of_isFormCoercive hc h).isClosed_range H.uniformContinuous
  simpa [LinearMap.coe_range] using hr

theorem range_eq_top_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) : LinearMap.range (H : E →ₗ[ℂ] E) = ⊤ := by
  haveI := (isClosed_range_of_isFormCoercive hc h).completeSpace_coe
  rw [← (LinearMap.range (H : E →ₗ[ℂ] E)).orthogonal_orthogonal,
    Submodule.eq_top_iff']
  intro x w hw
  have hzero : w = 0 := by
    have hperp : ⟪H w, w⟫_ℂ = 0 := hw _ ⟨w, rfl⟩
    have hre : (⟪w, H w⟫_ℂ).re = 0 := by
      rw [← inner_conj_symm, hperp]
      simp
    have hcw := h w
    rw [hre] at hcw
    have hsq : ‖w‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq)
  subst hzero
  exact inner_zero_left _

/-- **Lax–Milgram, complex form.**  A form-coercive bounded operator is
bijective.  No symmetry or self-adjointness is assumed. -/
theorem bijective_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) : Function.Bijective H := by
  refine ⟨injective_of_isFormCoercive hc h, fun y => ?_⟩
  have hmem : y ∈ LinearMap.range (H : E →ₗ[ℂ] E) := by
    rw [range_eq_top_of_isFormCoercive hc h]; trivial
  exact LinearMap.mem_range.mp hmem

theorem isUnit_of_isFormCoercive {H : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (h : IsFormCoercive H c) : IsUnit H :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (bijective_of_isFormCoercive hc h)

/-- **No spectrum below a form lower bound.**  If `Δ‖ψ‖² ≤ re ⟪ψ, Hψ⟫` for all
`ψ`, then every `z` with `z.re < Δ` is in the resolvent set. -/
theorem notMem_spectrum_of_formLowerBound {H : E →L[ℂ] E} {Δ : ℝ}
    (hgap : ∀ ψ : E, Δ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re) {z : ℂ} (hz : z.re < Δ) :
    z ∉ spectrum ℂ H := by
  have hshift : IsFormCoercive (H - z • ContinuousLinearMap.id ℂ E) (Δ - z.re) := by
    intro ψ
    have hinner : ⟪ψ, (H - z • ContinuousLinearMap.id ℂ E) ψ⟫_ℂ
        = ⟪ψ, H ψ⟫_ℂ - z * ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      simp [inner_self_eq_norm_sq_to_K]
    rw [hinner, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [hgap ψ, sq_nonneg ‖ψ‖]
  have hpos : 0 < Δ - z.re := by linarith
  have hunit : IsUnit (H - z • ContinuousLinearMap.id ℂ E) :=
    isUnit_of_isFormCoercive hpos hshift
  have hunit' : IsUnit (z • ContinuousLinearMap.id ℂ E - H) := by
    have hneg : (z • ContinuousLinearMap.id ℂ E - H)
        = -(H - z • ContinuousLinearMap.id ℂ E) := by abel
    rw [hneg]
    exact hunit.neg
  intro hmem
  apply hmem
  simpa [Algebra.algebraMap_eq_smul_one] using hunit'

/-- The spectrum of a bounded operator with form lower bound `Δ` lies in the
closed half plane `{Δ ≤ re z}`. -/
theorem spectrum_subset_halfPlane {H : E →L[ℂ] E} {Δ : ℝ}
    (hgap : ∀ ψ : E, Δ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re) :
    spectrum ℂ H ⊆ {z : ℂ | Δ ≤ z.re} := by
  intro z hz
  by_contra hcon
  exact notMem_spectrum_of_formLowerBound hgap (lt_of_not_ge hcon) hz

/-! ## The physical version: gap above a vacuum -/

section Vacuum

variable (v : E)

/-- The states orthogonal to the vacuum. -/
noncomputable abbrev vacuumComplement : Submodule ℂ E := (ℂ ∙ v)ᗮ

instance : CompleteSpace (vacuumComplement (E := E) v) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

omit [CompleteSpace E] in
theorem mem_vacuumComplement_iff {ψ : E} :
    ψ ∈ vacuumComplement v ↔ ⟪ψ, v⟫_ℂ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left

variable {v}

/-- The restriction of an operator leaving the vacuum complement invariant. -/
noncomputable def restrictComplement (H : E →L[ℂ] E)
    (hinv : ∀ ψ ∈ vacuumComplement v, H ψ ∈ vacuumComplement v) :
    vacuumComplement v →L[ℂ] vacuumComplement v :=
  ContinuousLinearMap.codRestrict (H.comp (vacuumComplement v).subtypeL)
    (vacuumComplement v) (fun ψ => hinv ψ ψ.2)

omit [CompleteSpace E] in
@[simp] theorem restrictComplement_apply (H : E →L[ℂ] E)
    (hinv : ∀ ψ ∈ vacuumComplement v, H ψ ∈ vacuumComplement v)
    (ψ : vacuumComplement v) :
    ((restrictComplement H hinv ψ : vacuumComplement v) : E) = H (ψ : E) := rfl

/-- **No spectral pollution from below, bounded case.**  A form gap `Δ` above
the vacuum, for an operator leaving the vacuum complement invariant, forces the
spectrum of the restricted operator into `{Δ ≤ re z}`. -/
theorem spectrum_restrict_subset_halfPlane (H : E →L[ℂ] E) {Δ : ℝ}
    (hinv : ∀ ψ ∈ vacuumComplement v, H ψ ∈ vacuumComplement v)
    (hgap : HasFormGap H v Δ) :
    spectrum ℂ (restrictComplement H hinv) ⊆ {z : ℂ | Δ ≤ z.re} := by
  refine spectrum_subset_halfPlane (fun ψ => ?_)
  have hψ : ⟪(ψ : E), v⟫_ℂ = 0 := (mem_vacuumComplement_iff v).mp ψ.2
  have hin : ⟪ψ, restrictComplement H hinv ψ⟫_ℂ = ⟪(ψ : E), H (ψ : E)⟫_ℂ := rfl
  rw [hin]
  simpa using hgap (ψ : E) hψ

/-- **The transported statement.**  A strong limit of Hamiltonians with a
uniform form gap `Δ` above the same vacuum has no spectrum with real part below
`Δ` on the vacuum complement. -/
theorem spectrum_restrict_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {H : ι → E →L[ℂ] E} (Hlim : E →L[ℂ] E) {Δ : ℝ}
    (hinv : ∀ ψ ∈ vacuumComplement v, Hlim ψ ∈ vacuumComplement v)
    (hconv : ∀ ψ : E, Tendsto (fun n => H n ψ) l (𝓝 (Hlim ψ)))
    (hgap : ∀ᶠ n in l, HasFormGap (H n) v Δ) :
    spectrum ℂ (restrictComplement Hlim hinv) ⊆ {z : ℂ | Δ ≤ z.re} :=
  spectrum_restrict_subset_halfPlane Hlim hinv (hasFormGap_of_tendsto hconv hgap)

end Vacuum

end RequestProject.YangMills.FormGapSpectralExclusion

#print axioms RequestProject.YangMills.FormGapSpectralExclusion.bijective_of_isFormCoercive
#print axioms RequestProject.YangMills.FormGapSpectralExclusion.notMem_spectrum_of_formLowerBound
#print axioms RequestProject.YangMills.FormGapSpectralExclusion.spectrum_subset_halfPlane
#print axioms RequestProject.YangMills.FormGapSpectralExclusion.spectrum_restrict_subset_halfPlane
#print axioms RequestProject.YangMills.FormGapSpectralExclusion.spectrum_restrict_of_tendsto
