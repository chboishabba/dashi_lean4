/-
# The BIDI normal form (45): the assembled chain

This module composes the proved telescope, resolvent, localization, Cauchy,
source-calculus and clustering-to-gap pieces into the source waist and terminal
vacuum-sector statements.  Physical/source attachments remain explicit
hypotheses; no Clay completion is claimed.
-/
import Mathlib
import RequestProject.YangMills.BIDI.NoncommTelescope
import RequestProject.YangMills.BIDI.ResolventDefect
import RequestProject.YangMills.BIDI.Localization
import RequestProject.YangMills.BIDI.CauchyMixed
import RequestProject.YangMills.BIDI.SourceCalculus
import RequestProject.YangMills.BIDI.ClusteringGap

namespace RequestProject.YangMills.BIDI

open Metric Filter Topology MeasureTheory
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {ι κ : Type*}

theorem shell_sup_bound_of_localization {logZ : ℂ → ℂ → ℂ} {r : ℝ}
    (Ys : Finset κ) (Γ : κ → Finset ι) (T M : κ → ι → ℝ) (MY : κ → ℝ) {Mshell : ℝ}
    (hattach : ∀ x ∈ closedBall (0:ℂ) r, ∀ y ∈ sphere (0:ℂ) r,
      ‖logZ x y‖ ≤ |∑ Y ∈ Ys, ∑ γ ∈ Γ Y, T Y γ|)
    (hterm : ∀ Y ∈ Ys, ∀ γ ∈ Γ Y, |T Y γ| ≤ M Y γ)
    (hrow : ∀ Y ∈ Ys, ∑ γ ∈ Γ Y, M Y γ ≤ MY Y)
    (hshell : ∑ Y ∈ Ys, MY Y ≤ Mshell) :
    ∀ x ∈ closedBall (0:ℂ) r, ∀ y ∈ sphere (0:ℂ) r, ‖logZ x y‖ ≤ Mshell := by
  intro x hx y hy
  exact le_trans (hattach x hx y hy)
    (abs_double_sum_le_of_termwise Ys Γ T M MY hterm hrow hshell)

theorem mixedLog_bound_of_source_data {logZ : ℂ → ℂ → ℂ}
    {r Mshell Cgeo m dphys t : ℝ} (hr : 0 < r) (hm : 0 < m) (hCgeo : 0 ≤ Cgeo)
    (htd : t ≤ dphys)
    (hslice : ∀ x ∈ closedBall (0:ℂ) r, DiffContOnCl ℂ (fun y => logZ x y) (ball 0 r))
    (houter : DiffContOnCl ℂ (fun x => deriv (fun y => logZ x y) 0) (ball 0 r))
    (hsup : ∀ x ∈ closedBall (0:ℂ) r, ∀ y ∈ sphere (0:ℂ) r, ‖logZ x y‖ ≤ Mshell)
    (hgeom : cauchyConst r * Mshell ≤ Cgeo * Real.exp (-(m * dphys))) :
    ‖mixedLogDeriv logZ‖ ≤ Cgeo * Real.exp (-(m * t)) := by
  have hcauchy : ‖mixedLogDeriv logZ‖ ≤ cauchyConst r * Mshell :=
    norm_mixed_deriv_le_cauchyConst hr hslice hsup houter
  exact exp_decay_transfer hm hCgeo htd (le_trans hcauchy hgeom)

theorem polarized_bound_of_source_data {hp hmn : ℂ → ℂ}
    {r Mshell Cgeo m dphys t : ℝ} (hr : 0 < r) (hmpos : 0 < m) (hCgeo : 0 ≤ Cgeo)
    (htd : t ≤ dphys)
    (hhp : DiffContOnCl ℂ hp (ball 0 r)) (hhm : DiffContOnCl ℂ hmn (ball 0 r))
    (hbp : ∀ z ∈ sphere (0:ℂ) r, ‖hp z‖ ≤ Mshell)
    (hbm : ∀ z ∈ sphere (0:ℂ) r, ‖hmn z‖ ≤ Mshell)
    (hgeom : cauchyConst r * Mshell ≤ Cgeo * Real.exp (-(m * dphys))) :
    ‖polarizedMixed hp hmn‖ ≤ Cgeo * Real.exp (-(m * t)) :=
  exp_decay_transfer hmpos hCgeo htd
    (le_trans (norm_polarized_mixed_le hr hhp hhm hbp hbm) hgeom)

theorem covariance_bound_finite {logZ : ℂ → ℂ → ℂ} {C m t : ℝ}
    (h : ‖mixedLogDeriv logZ‖ ≤ C * Real.exp (-(m * t))) :
    ‖covFinite logZ‖ ≤ C * Real.exp (-(m * t)) := by
  rwa [covFinite_eq_mixedLogDeriv]

theorem covariance_bound_continuum {ν : Type*} {l : Filter ν} [l.NeBot]
    {logZ : ν → ℂ → ℂ → ℂ} {covInf : ℂ} {C m t : ℝ}
    (hconv : Tendsto (fun N => covFinite (logZ N)) l (𝓝 covInf))
    (hfin : ∀ N, ‖covFinite (logZ N)‖ ≤ C * Real.exp (-(m * t))) :
    ‖covInf‖ ≤ C * Real.exp (-(m * t)) :=
  norm_le_of_tendsto hconv hfin

theorem continuum_clustering_of_source_data {ν : Type*} {l : Filter ν} [l.NeBot]
    {logZ : ν → ℂ → ℂ → ℂ} {covInf : ℂ}
    {r Mshell Cgeo m dphys t : ℝ} (hr : 0 < r) (hm : 0 < m) (hCgeo : 0 ≤ Cgeo)
    (htd : t ≤ dphys)
    (hslice : ∀ N, ∀ x ∈ closedBall (0:ℂ) r,
      DiffContOnCl ℂ (fun y => logZ N x y) (ball 0 r))
    (houter : ∀ N, DiffContOnCl ℂ (fun x => deriv (fun y => logZ N x y) 0) (ball 0 r))
    (hsup : ∀ N, ∀ x ∈ closedBall (0:ℂ) r, ∀ y ∈ sphere (0:ℂ) r,
      ‖logZ N x y‖ ≤ Mshell)
    (hgeom : cauchyConst r * Mshell ≤ Cgeo * Real.exp (-(m * dphys)))
    (hconv : Tendsto (fun N => covFinite (logZ N)) l (𝓝 covInf)) :
    ‖covInf‖ ≤ Cgeo * Real.exp (-(m * t)) :=
  covariance_bound_continuum hconv
    (fun N => covariance_bound_finite
      (mixedLog_bound_of_source_data hr hm hCgeo htd (hslice N) (houter N) (hsup N) hgeom))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open scoped InnerProductSpace

noncomputable def gapDatum_of_clustering {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (hm : 0 < m) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H)
    (D : ClusteringSpectralData H vac m) : VacuumGapDatum E where
  op := H
  vac := vac
  gap := m
  vac_mem := hmem
  vac_unit := hunit
  vac_ground := hground
  selfAdjoint := hsa
  gap_pos := hm
  form_gap := hasVacuumFormGap_of_clustering D

theorem no_eigenvalue_below_gap {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (hm : 0 < m) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H)
    (D : ClusteringSpectralData H vac m)
    {lam : ℝ} {psi : H.domain} (hne : (psi : E) ≠ 0)
    (heig : H psi = (lam : ℂ) • (psi : E)) (hlt : lam < m) :
    lam = 0 :=
  (gapDatum_of_clustering hm hmem hunit hground hsa D).eigenvalue_eq_zero_of_lt_gap
    hne heig hlt

theorem resolvent_solvable_below_gap {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (hm : 0 < m) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H)
    (D : ClusteringSpectralData H vac m)
    {lam : ℝ} (hlt : lam < m) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 ∧
      H psi - (lam : ℂ) • (psi : E) = y :=
  (gapDatum_of_clustering hm hmem hunit hground hsa D).exists_unique_solution_vacuumSector
    hlt hy

omit [CompleteSpace E] in
theorem mass_gap_of_clustering {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (D : ClusteringSpectralData H vac m) (psi : H.domain)
    (horth : ⟪vac, (psi : E)⟫_ℂ = 0) :
    m * ‖(psi : E)‖ ^ 2 ≤ (⟪(psi : E), H psi⟫_ℂ).re :=
  hasVacuumFormGap_of_clustering D psi horth

theorem bidi_waist_to_gap {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (hm : 0 < m) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H)
    (D : ClusteringSpectralData H vac m)
    {lam : ℝ} (hlt : lam < m) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    (∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
        m * ‖(psi : E)‖ ^ 2 ≤ (⟪(psi : E), H psi⟫_ℂ).re) ∧
      (∃! psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 ∧
        H psi - (lam : ℂ) • (psi : E) = y) :=
  ⟨fun psi horth => mass_gap_of_clustering D psi horth,
   resolvent_solvable_below_gap hm hmem hunit hground hsa D hlt hy⟩

end RequestProject.YangMills.BIDI
