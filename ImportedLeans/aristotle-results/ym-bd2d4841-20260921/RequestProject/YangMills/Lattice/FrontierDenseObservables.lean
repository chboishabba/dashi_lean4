/-
# The endpoint driven by gauge-invariant observable estimates

`Lattice/FrontierF1F3F4.lean` states the endpoint of the lattice lane:
`F1 + F3` give the continuum mass-gap conclusion, and `F1 + F3 + F4` give it for
the Osterwalder–Schrader Hamiltonian.  This file restates those endpoints with
`F1` replaced by the weakest finite-side input this development reaches: a
connected two-slice correlation estimate for the *mean-zero gauge-invariant
continuous observables* of the literal Wilson–Gibbs measure, with the
spacing-dependent tolerance `Δ a_k ≤ 1 − c_k`.

* `clay_massGap_of_gauge_invariant_mixing_F3`
* `clay_massGap_os_of_gauge_invariant_mixing_F3_F4`

The physical content is unchanged and nothing is proved about the interacting
measure: what changes is the shape of the input, which is now an estimate on a
dense algebra of physical observables rather than a statement quantified over
all square-integrable states.
-/
import Mathlib
import RequestProject.YangMills.Lattice.FrontierF1F3F4
import RequestProject.YangMills.Lattice.GaugeInvariantDenseObservables

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The endpoint on gauge-invariant observable estimates.**  If along the
trajectory the connected two-slice correlation of the literal four-dimensional
`SU(2)` Wilson–Gibbs measure obeys `|Corr_c(f,f)| ≤ c_k ‖f‖²` for every mean-zero
gauge-invariant continuous observable `f`, with the spectral defect condition
`Δ a_k ≤ 1 − c_k`, then together with `F3` the continuum Hamiltonian has the full
mass-gap conclusion. -/
theorem clay_massGap_of_gauge_invariant_mixing_F3 (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {cs : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hbound : ∀ k, ∀ f : C(SliceIdx (vol k) → SU2, ℂ), (∀ g u, f (sliceGauge g u) = f u) →
      (∫ u, f u ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2)) = 0 →
        ‖∫ U, (starRingEnd ℂ) (f (slice0 U)) * f (slice1 U)
            ∂(gibbs (vol k) SU2 (beta k) chiSU2)‖
          ≤ cs k * ∫ u, ‖f u‖ ^ 2 ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2))
    (hdefect : ∀ k, Δ * a k ≤ 1 - cs k)
    (L : EmbeddedContinuumLimit vol beta a (fun k => (hapos k).le) E) :
    Clay.MassGapConclusion L.ham L.vac Δ :=
  clay_massGap_of_F1_F3 vol beta a (fun k => (hapos k).le) hΔ
    (ym_uniform_gap_of_gauge_invariant_mixing vol beta a hapos hbound hdefect) L

/-- **The Osterwalder–Schrader version.**  Same finite-side input, together with
`F3` and the same-evolution identity `F4` on a common core. -/
theorem clay_massGap_os_of_gauge_invariant_mixing_F3_F4 (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (hapos : ∀ k, 0 < a k) {cs : ℕ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hbound : ∀ k, ∀ f : C(SliceIdx (vol k) → SU2, ℂ), (∀ g u, f (sliceGauge g u) = f u) →
      (∫ u, f u ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2)) = 0 →
        ‖∫ U, (starRingEnd ℂ) (f (slice0 U)) * f (slice1 U)
            ∂(gibbs (vol k) SU2 (beta k) chiSU2)‖
          ≤ cs k * ∫ u, ‖f u‖ ^ 2 ∂(sliceMeasure (vol k) SU2 (beta k) chiSU2))
    (hdefect : ∀ k, Δ * a k ≤ 1 - cs k)
    (L : EmbeddedContinuumLimit vol beta a (fun k => (hapos k).le) E)
    {Hos : E →ₗ.[ℂ] E} {U V : ℝ → E → E} {S : Submodule ℂ E} (hUV : U = V)
    (hcYM : L.ham.HasCore S) (hcOS : Hos.HasCore S)
    (hgYM : IsPMapEvolutionGenerator U S L.ham)
    (hgOS : IsPMapEvolutionGenerator V S Hos) :
    Clay.MassGapConclusion Hos L.vac Δ :=
  clay_massGap_os_of_F1_F3_F4 vol beta a (fun k => (hapos k).le) hΔ
    (ym_uniform_gap_of_gauge_invariant_mixing vol beta a hapos hbound hdefect) L
    hUV hcYM hcOS hgYM hgOS

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms clay_massGap_of_gauge_invariant_mixing_F3
#print axioms clay_massGap_os_of_gauge_invariant_mixing_F3_F4

end Audit
