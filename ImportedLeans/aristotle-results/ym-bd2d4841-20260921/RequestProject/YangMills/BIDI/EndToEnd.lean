/-
# The BIDI chain end to end

This file states the whole chain of the note as a single implication, with every
remaining residual of §"Current residual cut" (46) displayed as a named
hypothesis and every step that has actually been proved discharged by the
modules of this development.

`source_covariance_bound_of_polymer` runs the source side:

    polymer activity decay + polymer entropy   (RowBShellEnergy, already in this
                                                library)
      → far-shell tail energy  ≤ (AB/(1−r))·e^{−(μ−ν)d}     (PolymerShellBridge)
      → sup bound on the source-domain function on the polydisc  (the *attachment*
                                                hypothesis `hattach`)
      → Cauchy extraction                                    (CauchyMixed, R402)
      → spatial-to-temporal transfer at `t ≤ d`              (SourceCalculus)
      → finite covariance bound                              (definitional, (4))
      → continuum covariance bound                           (order closure, (38))

`bidi_end_to_end` runs the terminal side on that output:

      → exponential clustering of the correlation function    (the OS/reconstruction
                                                attachment `hos`)
      → no spectral weight in `(0,m)`                        (ClusteringGap, (42))
      → vacuum form gap `m` at every cutoff                  (ClusteringGap, (44))
      → continuum form gap                                   (ContinuumGapTransport)
      → no spectrum in `[0,m)` on the vacuum complement of the continuum
        Hamiltonian, with the resolvent bound.

The mass is `m = μ − ν`: the polymer decay rate minus the polymer entropy rate.

**Residuals, explicitly.**  `hattach` (the same-object source attachment),
`hslice`/`houter` (holomorphy of the source-domain function in the sources),
`hconv` (finite-to-continuum convergence of the covariance), `S` (the spectral
theorem for the cutoff Hamiltonians), `hos` (the OS identification of the
correlation function with the continuum covariance), `hlim` (the vacuum-sector
graph limit), `hsa`/`hground` (self-adjointness and the zero-energy vacuum of the
limit), and the two polymer inputs `hact`/`hcard`.  None of these is proved
here, and the file therefore claims no theorem about physical Yang–Mills.
-/
import Mathlib
import RequestProject.YangMills.BIDI.Assembly
import RequestProject.YangMills.BIDI.PolymerShellBridge
import RequestProject.YangMills.BIDI.ContinuumBridge

namespace RequestProject.YangMills.BIDI

open Metric Filter Topology MeasureTheory Finset
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open scoped InnerProductSpace

/-- **The source side, end to end.**  From the polymer inputs, the attachment of
the source-domain function to the differentiated shell decomposition, holomorphy
on the selected polydisc and the finite-to-continuum convergence, the continuum
covariance decays exponentially in the temporal separation, with mass `μ − ν`. -/
theorem source_covariance_bound_of_polymer {X : Type*} {shell : ℕ → Finset X}
    {act : X → ℝ} {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmn : nu < mu)
    {rad : ℝ} (hrad : 0 < rad) (d : ℕ) {t : ℝ} (htd : t ≤ (d : ℝ))
    {ν : Type*} {l : Filter ν} [l.NeBot] {logZ : ν → ℂ → ℂ → ℂ} {covInf : ℂ}
    (hslice : ∀ N, ∀ x ∈ closedBall (0:ℂ) rad,
      DiffContOnCl ℂ (fun y => logZ N x y) (ball 0 rad))
    (houter : ∀ N, DiffContOnCl ℂ (fun x => deriv (fun y => logZ N x y) 0) (ball 0 rad))
    (hattach : ∀ N, ∀ x ∈ closedBall (0:ℂ) rad, ∀ y ∈ sphere (0:ℂ) rad,
      ‖logZ N x y‖ ≤ ∑' k : ℕ, (∑ z ∈ shell (d + k), |act z|))
    (hconv : Tendsto (fun N => covFinite (logZ N)) l (𝓝 covInf)) :
    ‖covInf‖
      ≤ (cauchyConst rad * ((A * B) / (1 - _root_.YangMills.shellRatio nu mu)))
          * Real.exp (-((mu - nu) * t)) := by
  set r := _root_.YangMills.shellRatio nu mu with hr
  have hr1 : r < 1 := _root_.YangMills.shellRatio_lt_one hmn
  have hAB : 0 ≤ (A * B) / (1 - r) := div_nonneg (mul_nonneg hA hB) (by linarith)
  have hCgeo : 0 ≤ cauchyConst rad * ((A * B) / (1 - r)) :=
    mul_nonneg (le_of_lt (cauchyConst_pos hrad)) hAB
  have hm : 0 < mu - nu := by linarith
  have hgeom :
      cauchyConst rad * (∑' k : ℕ, (∑ z ∈ shell (d + k), |act z|))
        ≤ (cauchyConst rad * ((A * B) / (1 - r))) * Real.exp (-((mu - nu) * (d : ℝ))) :=
    cauchy_shell_estimate_of_polymer hrad hact hcard hA hB hmn d le_rfl
  exact continuum_clustering_of_source_data hrad hm hCgeo htd hslice houter hattach
    hgeom hconv

/-- **The BIDI chain, end to end.**  The source side supplies the exponential
clustering of the correlation functions; the terminal side converts it into the
statement that the continuum Hamiltonian has no spectrum in `[0, μ−ν)` on the
vacuum complement, with the resolvent bound. -/
theorem bidi_end_to_end {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {m : ℝ} (hm : 0 < m)
    (S : ∀ n, SpectralRepresentation (H n) (vacn n))
    (covInf : ∀ n, (H n).domain → ℝ → ℂ) (cconst : ∀ n, (H n).domain → ℝ)
    (hos : ∀ n, ∀ psi : (H n).domain, ⟪vacn n, (psi : E)⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂((S n).spectralMeasure psi) ≤ ‖covInf n psi t‖)
    (hsrc : ∀ n, ∀ psi : (H n).domain, ∀ t : ℝ, 0 ≤ t →
      ‖covInf n psi t‖ ≤ cconst n psi * Real.exp (-(m * t)))
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0)
    {lam : ℝ} (hlt : lam < m) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    (∃! psi : Hinf.domain, ⟪vac, (psi : E)⟫_ℂ = 0 ∧
        Hinf psi - (lam : ℂ) • (psi : E) = y) ∧
      HasVacuumFormGap Hinf vac m := by
  have Dn : ∀ n, ClusteringSpectralData (H n) (vacn n) m := fun n =>
    ClusteringSpectralData.ofSourceBound (S n) (covInf n) (cconst n) (hos n) (hsrc n)
  refine ⟨continuum_no_spectrum_below_gap_of_clustering Dn hlim hsa hmem hunit hground
      hm hlt hy, continuum_formGap_of_cutoff_clustering Dn hlim⟩

end RequestProject.YangMills.BIDI
