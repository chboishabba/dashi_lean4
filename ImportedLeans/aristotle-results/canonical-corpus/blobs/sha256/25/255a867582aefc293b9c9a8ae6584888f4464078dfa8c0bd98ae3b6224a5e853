/-
# Transport of a uniform mass gap through a limit of Hamiltonians

The terminal lane needs the finite-volume / finite-lattice gap to survive the
continuum limit.  What this file proves is the *quadratic-form* statement: no
loss of the form lower bound in a strong-limit setting.  It says nothing about
spectra by itself — the spectral consequence for bounded operators is proved
separately in `FormGapSpectralExclusion`, and the versions for genuinely
unbounded (partially defined) Hamiltonians are in `UnboundedFormGapTransport`.

Be precise about the scope: the Hamiltonians below are **bounded** operators
`E →L[ℂ] E`, including the limit `Hlim`.  This is therefore bounded strong-limit
form-gap transport, not the unbounded-Hamiltonian continuum-gap passage via
closed quadratic forms, resolvent convergence or Mosco convergence.

Stated at the level of quadratic forms — which is the level at which the gap is
actually *used*, both for the Clay statement and for the exponential clustering
argument — this is an unconditional theorem, and this file proves it:

* `HasFormGap H v Δ` — the form gap above the vacuum `v`: every state
  orthogonal to `v` has energy at least `Δ‖ψ‖²`;
* `hasFormGap_of_tendsto` — a **strong** limit of Hamiltonians with a *uniform*
  form gap `Δ` again has form gap `Δ`.  Only pointwise (strong) convergence is
  assumed: no norm convergence, no resolvent convergence, no compactness;
* `hasFormGap_of_tendsto_of_gap_tendsto` — the same with gap constants `Δ n`
  that merely converge to `Δ`;
* `energy_lower_bound` / `inner_self_re_nonneg_of_hasFormGap` — the two forms in
  which the gap is consumed downstream;
* `hasFormGap_smul_id` and `not_hasFormGap_zero_of_pos` show the notion is
  neither vacuous nor trivially true.

Nothing here supplies the physical gap; it supplies the statement that a
uniform gap is stable under limits, which is the step "uniform lattice gap ⟹
continuum gap" once the limit is taken in the strong sense.
-/
import Mathlib

namespace RequestProject.YangMills.MassGapFormTransport

open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `H` has form gap `Δ` above the vacuum `v`: every state orthogonal to the
vacuum has energy at least `Δ‖ψ‖²`. -/
def HasFormGap (H : E →L[ℂ] E) (v : E) (Δ : ℝ) : Prop :=
  ∀ ψ : E, ⟪ψ, v⟫_ℂ = 0 → Δ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re

/-- The gap read off as an energy lower bound on a unit vector. -/
theorem energy_lower_bound {H : E →L[ℂ] E} {v : E} {Δ : ℝ} (h : HasFormGap H v Δ)
    {ψ : E} (hψ : ⟪ψ, v⟫_ℂ = 0) (hnorm : ‖ψ‖ = 1) :
    Δ ≤ (⟪ψ, H ψ⟫_ℂ).re := by
  have := h ψ hψ
  simpa [hnorm] using this

/-- A nonnegative gap makes the energy nonnegative on the orthogonal
complement of the vacuum. -/
theorem inner_self_re_nonneg_of_hasFormGap {H : E →L[ℂ] E} {v : E} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : HasFormGap H v Δ) {ψ : E} (hψ : ⟪ψ, v⟫_ℂ = 0) :
    0 ≤ (⟪ψ, H ψ⟫_ℂ).re :=
  le_trans (mul_nonneg hΔ (by positivity)) (h ψ hψ)

/-- **Uniform gaps survive strong limits.**  If every `H n` has form gap `Δ`
above the same vacuum, and `H n ψ → Hlim ψ` for every state, then `Hlim` has
form gap `Δ`. -/
theorem hasFormGap_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {H : ι → E →L[ℂ] E} {Hlim : E →L[ℂ] E} {v : E} {Δ : ℝ}
    (hconv : ∀ ψ : E, Tendsto (fun n => H n ψ) l (𝓝 (Hlim ψ)))
    (hgap : ∀ᶠ n in l, HasFormGap (H n) v Δ) :
    HasFormGap Hlim v Δ := by
  intro ψ hψ
  have hcont : Tendsto (fun n => (⟪ψ, H n ψ⟫_ℂ).re) l (𝓝 ((⟪ψ, Hlim ψ⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (((continuous_inner (𝕜 := ℂ)).tendsto (ψ, Hlim ψ)).comp
        (Tendsto.prodMk_nhds tendsto_const_nhds (hconv ψ)))
  refine ge_of_tendsto hcont ?_
  filter_upwards [hgap] with n hn using hn ψ hψ

/-- The same, allowing the gap constants to vary and converge. -/
theorem hasFormGap_of_tendsto_of_gap_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {H : ι → E →L[ℂ] E} {Hlim : E →L[ℂ] E} {v : E} {Δ : ι → ℝ} {Δlim : ℝ}
    (hconv : ∀ ψ : E, Tendsto (fun n => H n ψ) l (𝓝 (Hlim ψ)))
    (hΔ : Tendsto Δ l (𝓝 Δlim))
    (hgap : ∀ᶠ n in l, HasFormGap (H n) v (Δ n)) :
    HasFormGap Hlim v Δlim := by
  intro ψ hψ
  have hcont : Tendsto (fun n => (⟪ψ, H n ψ⟫_ℂ).re) l (𝓝 ((⟪ψ, Hlim ψ⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (((continuous_inner (𝕜 := ℂ)).tendsto (ψ, Hlim ψ)).comp
        (Tendsto.prodMk_nhds tendsto_const_nhds (hconv ψ)))
  have hleft : Tendsto (fun n => Δ n * ‖ψ‖ ^ 2) l (𝓝 (Δlim * ‖ψ‖ ^ 2)) :=
    hΔ.mul tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hleft hcont ?_
  filter_upwards [hgap] with n hn using hn ψ hψ

/-- A monotonicity form: a larger uniform gap implies a smaller one. -/
theorem HasFormGap.mono {H : E →L[ℂ] E} {v : E} {Δ Δ' : ℝ} (h : HasFormGap H v Δ)
    (hle : Δ' ≤ Δ) : HasFormGap H v Δ' := by
  intro ψ hψ
  exact le_trans (by nlinarith [sq_nonneg ‖ψ‖]) (h ψ hψ)

/-- Non-vacuity: `Δ • id` has form gap `Δ` above any vacuum. -/
theorem hasFormGap_smul_id (Δ : ℝ) (v : E) :
    HasFormGap ((Δ : ℂ) • ContinuousLinearMap.id ℂ E) v Δ := by
  intro ψ _
  have h1 : ⟪ψ, ((Δ : ℂ) • ContinuousLinearMap.id ℂ E) ψ⟫_ℂ = (Δ : ℂ) * (‖ψ‖ : ℂ) ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [h1, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- And it is not trivially true: the zero operator has no positive gap as soon
as some state is orthogonal to the vacuum and nonzero. -/
theorem not_hasFormGap_zero_of_pos {v ψ : E} (hψ : ⟪ψ, v⟫_ℂ = 0) (hne : ψ ≠ 0)
    {Δ : ℝ} (hΔ : 0 < Δ) : ¬ HasFormGap (0 : E →L[ℂ] E) v Δ := by
  intro h
  have := h ψ hψ
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re] at this
  have hpos : 0 < Δ * ‖ψ‖ ^ 2 := by
    have : 0 < ‖ψ‖ := norm_pos_iff.mpr hne
    positivity
  linarith

end RequestProject.YangMills.MassGapFormTransport

#print axioms RequestProject.YangMills.MassGapFormTransport.hasFormGap_of_tendsto
#print axioms RequestProject.YangMills.MassGapFormTransport.hasFormGap_of_tendsto_of_gap_tendsto
#print axioms RequestProject.YangMills.MassGapFormTransport.hasFormGap_smul_id
#print axioms RequestProject.YangMills.MassGapFormTransport.not_hasFormGap_zero_of_pos
