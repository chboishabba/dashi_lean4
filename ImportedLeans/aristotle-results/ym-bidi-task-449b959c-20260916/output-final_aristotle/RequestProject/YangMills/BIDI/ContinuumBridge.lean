/-
# Working backwards: cutoff clustering to the continuum spectral gap

The terminal half of the BIDI chain proves, in `BIDI.ClusteringGap`, that
exponential clustering of the vacuum-orthogonal states gives the vacuum form gap
of *one* Hamiltonian.  The Yang–Mills chain produces clustering at every cutoff,
with a rate that does not depend on the cutoff; this file composes the two
directions by feeding that uniform gap into the transport machinery already in
this library (`ContinuumGapTransport`).

* `continuum_formGap_of_cutoff_clustering` — uniform clustering along the cutoff
  family plus a vacuum-sector graph limit gives the vacuum form gap of the limit
  operator;
* `continuum_no_spectrum_below_gap_of_clustering` — with self-adjointness and a
  normalised zero-energy limit vacuum: for every real `λ < m` and every
  `y ⊥ Ω` the equation `H∞ψ − λψ = y` has a unique vacuum-orthogonal solution,
  i.e. *no spectrum in `[0,m)` on the vacuum complement of the continuum
  Hamiltonian*;
* `continuum_resolvent_bound_of_clustering` — the quantitative resolvent bound
  `‖ψ‖ ≤ (m − λ)⁻¹‖H∞ψ − λψ‖`;
* `continuum_no_eigenvalue_below_gap_of_clustering` — no excited state below the
  gap.

Every hypothesis is displayed: the cutoff clustering data, the graph limit, and
the self-adjointness of the limit.  Nothing here constructs the Yang–Mills
cutoff family or proves that it converges.
-/
import Mathlib
import RequestProject.YangMills.BIDI.ClusteringGap
import RequestProject.YangMills.ContinuumGapTransport

namespace RequestProject.YangMills.BIDI

open Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Uniform cutoff clustering gives the continuum form gap.** -/
theorem continuum_formGap_of_cutoff_clustering {H : ℕ → E →ₗ.[ℂ] E} {vacn : ℕ → E}
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (Dn : ∀ n, ClusteringSpectralData (H n) (vacn n) m)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac) :
    HasVacuumFormGap Hinf vac m :=
  hasVacuumFormGap_of_graphLimit (fun n => hasVacuumFormGap_of_clustering (Dn n)) hlim

variable [CompleteSpace E]

/-- **No continuum spectrum below the clustering rate.** -/
theorem continuum_no_spectrum_below_gap_of_clustering {H : ℕ → E →ₗ.[ℂ] E}
    {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (Dn : ∀ n, ClusteringSpectralData (H n) (vacn n) m)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hm : 0 < m)
    {lam : ℝ} (hlt : lam < m) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    ∃! psi : Hinf.domain, ⟪vac, (psi : E)⟫_ℂ = 0 ∧
      Hinf psi - (lam : ℂ) • (psi : E) = y :=
  continuum_no_spectrum_below_gap (fun n => hasVacuumFormGap_of_clustering (Dn n))
    hlim hsa hmem hunit hground hm hlt hy

/-- **The continuum resolvent bound from cutoff clustering.** -/
theorem continuum_resolvent_bound_of_clustering {H : ℕ → E →ₗ.[ℂ] E}
    {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (Dn : ∀ n, ClusteringSpectralData (H n) (vacn n) m)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hm : 0 < m)
    {lam : ℝ} (hlt : lam < m) {psi : Hinf.domain}
    (horth : ⟪vac, (psi : E)⟫_ℂ = 0) :
    ‖(psi : E)‖ ≤ (m - lam)⁻¹ * ‖Hinf psi - (lam : ℂ) • (psi : E)‖ :=
  continuum_resolvent_bound (fun n => hasVacuumFormGap_of_clustering (Dn n))
    hlim hsa hmem hunit hground hm hlt horth

/-- **No excited state below the gap in the continuum.** -/
theorem continuum_no_eigenvalue_below_gap_of_clustering {H : ℕ → E →ₗ.[ℂ] E}
    {vacn : ℕ → E} {Hinf : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (Dn : ∀ n, ClusteringSpectralData (H n) (vacn n) m)
    (hlim : IsVacuumGraphLimit H vacn Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0) (hm : 0 < m)
    {lam : ℝ} {psi : Hinf.domain} (hne : (psi : E) ≠ 0)
    (heig : Hinf psi = (lam : ℂ) • (psi : E)) (hlt : lam < m) :
    lam = 0 :=
  (continuumDatum (fun n => hasVacuumFormGap_of_clustering (Dn n)) hlim hsa hmem
    hunit hground hm).eigenvalue_eq_zero_of_lt_gap hne heig hlt

end RequestProject.YangMills.BIDI
