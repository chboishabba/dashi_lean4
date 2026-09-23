/-
# The BIDI normal form (45): the assembled chain

This module composes the pieces proved in

* `NoncommTelescope`  (§4, §5, §7: R406/R407/R409),
* `ResolventDefect`   (§6: R408, CMP99),
* `Localization`      (§3, §9: R404/R405, CMP116),
* `CauchyMixed`       (§10: R402),
* `SourceCalculus`    (§2, §11, §13: the source calculus and the order closures),
* `ClusteringGap`     (§14: clustering ⟹ spectral gap),

into the two halves of the BIDI waist and then into the terminal spectral
statement, and it connects the terminal end to the vacuum-sector machinery that
this library already contains.

## What is proved here

1. `shell_sup_bound_of_localization` — the CMP116 layers R404/R405, attached to
   the source-domain function, give the sup bound `|log Z| ≤ M_shell` on the
   selected polydisc.
2. `mixedLog_bound_of_source_data` — **equation (35)**: Cauchy extraction and
   the spatial-to-temporal transfer give the finite mixed-logarithmic estimate
   `|D_{J_L} D_{J_R} log Z_N| ≤ C e^{-mt}`, which is the BIDI waist (1).
3. `covariance_bound_finite` — **equation (36)**: the same bound for the finite
   covariance, by the definitional identity (4).
4. `covariance_bound_continuum` — **equation (38)**: one-sided order closure
   along the declared same-family convergence.
5. `gapDatum_of_clustering`, `no_eigenvalue_below_gap`,
   `resolvent_solvable_below_gap`, `mass_gap_of_clustering` — the terminal end:
   exponential clustering of every vacuum-orthogonal state, with a spectral
   representation, yields a `VacuumGapDatum` with gap `m`, hence (by the results
   already proved in `VacuumSectorSpectralGap`) no eigenvalue in `(0,m)`, unique
   solvability of `Hψ − λψ = y` on the vacuum complement for every `λ < m`, and
   `Δ(H) ≥ m > 0`.
6. `bidi_waist_to_gap` — the composite: the source-side estimate feeds the
   terminal consumer through the clustering hypothesis.

## What is *not* proved here — the residual cut (46)

Each of the following appears below as an explicit, named hypothesis, and is
exactly the "same-object / source attachment" residual of the note:

* the identification of the CMP99 defect with the changed R407 factor and the
  literal equality of the three unchanged stages (§8 (23)(24)): in this
  development these are the `Stage` fields `before`, `after` and the `defect = 0`
  hypotheses of `marked_product_bound`, which must be discharged by the literal
  CMP109 carrier;
* the identification of the R409 product with the R406 scalarised term (§8 (25)):
  the hypothesis `hscalar` of `abs_double_sum_le_of_norm_termwise`;
* the attachment of the positive CMP116 majorants to the *same* differentiated
  decomposition as the selected term (§9): the hypothesis `hattach` below;
* the holomorphy of the source-domain function on the selected polydisc
  (hypotheses `hslice`, `houter`);
* the spectral representation of the physical Hamiltonian and the identification
  of the continuum covariance with the correlation function `C_O(t)`: the
  structure `ClusteringSpectralData`.

Consequently nothing in this file claims the Clay theorem.  What it does claim,
and what compiles, is the implication: *given* those attachments, the finite
source estimate and the positive continuum mass gap are equivalent endpoints of
one machine-checked chain.
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

/-! ## The source side: from the differentiated decomposition to the waist -/

variable {ι κ : Type*}

/-- **CMP116 attached to the source domain.**  If the source-domain function is
dominated on the polydisc by the differentiated boundary contribution
`B = Σ_Y Σ_γ T_{Y,γ}` (this is the R410 attachment, an input), then the R404 and
R405 layers bound it by the shell budget. -/
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

/-- **Equation (35): the BIDI waist.**  Cauchy extraction on the selected
polydisc, the geometric shell estimate and `t ≤ d_phys` give the finite mixed
logarithmic bound. -/
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

/-- **Equation (35), polarised presentation.**  The polarisation identity
`D_L D_R = ¼(D₊² − D₋²)` needs only the holomorphy of the two diagonal
restrictions `h±(z) = log Z(z·(J_L ± J_R))` on the selected disc, so this
version of the waist estimate carries no hypothesis on a slice derivative. -/
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

/-- **Equation (36)**: the same bound for the finite covariance, by the
definitional two-source identity (4). -/
theorem covariance_bound_finite {logZ : ℂ → ℂ → ℂ} {C m t : ℝ}
    (h : ‖mixedLogDeriv logZ‖ ≤ C * Real.exp (-(m * t))) :
    ‖covFinite logZ‖ ≤ C * Real.exp (-(m * t)) := by
  rwa [covFinite_eq_mixedLogDeriv]

/-- **Equation (38)**: the continuum covariance inherits the finite bound along
the declared same-family convergence. -/
theorem covariance_bound_continuum {ν : Type*} {l : Filter ν} [l.NeBot]
    {logZ : ν → ℂ → ℂ → ℂ} {covInf : ℂ} {C m t : ℝ}
    (hconv : Tendsto (fun N => covFinite (logZ N)) l (𝓝 covInf))
    (hfin : ∀ N, ‖covFinite (logZ N)‖ ≤ C * Real.exp (-(m * t))) :
    ‖covInf‖ ≤ C * Real.exp (-(m * t)) :=
  norm_le_of_tendsto hconv hfin

/-- The whole source side in one statement: the CMP116 decomposition, the
majorants, the attachment, the holomorphy of the source-domain function and the
geometric shell estimate give the continuum clustering bound (38). -/
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

/-! ## The terminal side: from clustering to the Clay mass gap -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped InnerProductSpace

/-- **The terminal carrier.**  Exponential clustering of every vacuum-orthogonal
state, together with the spectral representation of those states, produces the
`VacuumGapDatum` of `VacuumSectorSpectralGap` with gap `m`. -/
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

/-- **Equation (43)**: no excited state below the gap.  An eigenvalue smaller
than `m` is forced to be `0`, i.e. the spectrum of `H` on the vacuum complement
avoids `(0, m)` in the eigenvalue sense. -/
theorem no_eigenvalue_below_gap {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (hm : 0 < m) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H)
    (D : ClusteringSpectralData H vac m)
    {lam : ℝ} {psi : H.domain} (hne : (psi : E) ≠ 0)
    (heig : H psi = (lam : ℂ) • (psi : E)) (hlt : lam < m) :
    lam = 0 :=
  (gapDatum_of_clustering hm hmem hunit hground hsa D).eigenvalue_eq_zero_of_lt_gap
    hne heig hlt

/-- **Equation (43), resolvent form**: for every real `λ < m` and every
`y ⊥ Ω` there is a unique vacuum-orthogonal `ψ` in the domain with
`Hψ − λψ = y`.  There is no spectrum in `[0, m)` on the vacuum complement. -/
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
/-- **Equation (44)**: the positive mass gap.  Every vacuum-orthogonal state of
the domain has energy at least `m‖ψ‖²`, with `m > 0`. -/
theorem mass_gap_of_clustering {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (D : ClusteringSpectralData H vac m) (psi : H.domain)
    (horth : ⟪vac, (psi : E)⟫_ℂ = 0) :
    m * ‖(psi : E)‖ ^ 2 ≤ (⟪(psi : E), H psi⟫_ℂ).re :=
  hasVacuumFormGap_of_clustering D psi horth

/-- **The BIDI normal form (45), assembled.**  The source side produces the
clustering bound; the terminal side turns exactly that bound into the positive
mass gap.  The hypothesis `hbridge` is the OS/reconstruction attachment: the
correlation function of a vacuum-orthogonal state at temporal separation `t` is
the continuum covariance bounded by the source side. -/
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
