/-
# Equation (43) as a genuine spectrum statement, in the bounded case

`ClusteringGap` delivers the vacuum form gap; for a *bounded* Hamiltonian the
library already converts a form gap above the vacuum into an actual spectral
exclusion (`FormGapSpectralExclusion.spectrum_restrict_subset_halfPlane`, proved
there by a complex Lax–Milgram argument).  Composing the two gives the note's
equation (43) in the literal form

    spec(H|_{Ω^⊥}) ∩ (0, m) = ∅,

for a bounded Hamiltonian whose vacuum-orthogonal states cluster exponentially
at rate `m`.

* `hasFormGap_of_clustering_bounded` — clustering gives the bounded-operator
  form gap;
* `spectrum_restrict_subset_halfPlane_of_clustering` — the spectrum of the
  restriction to the vacuum complement lies in `{m ≤ re z}`;
* `notMem_spectrum_of_clustering` — no real `λ < m` is in that spectrum;
* `spectrum_inter_Ioo_eq_empty_of_clustering` — the displayed form
  `spec ∩ (0,m) = ∅`.

The unbounded (physical) version remains the resolvent statement of
`Assembly.resolvent_solvable_below_gap`, because no spectral theorem for
unbounded self-adjoint operators is available in the ambient library.
-/
import Mathlib
import RequestProject.YangMills.BIDI.ClusteringGap
import RequestProject.YangMills.FormGapSpectralExclusion

namespace RequestProject.YangMills.BIDI

open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.MassGapFormTransport
open RequestProject.YangMills.FormGapSpectralExclusion
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Exponential clustering of the vacuum-orthogonal states of a bounded
Hamiltonian gives the bounded-operator form gap. -/
theorem hasFormGap_of_clustering_bounded {Hb : E →L[ℂ] E} {vac : E} {m : ℝ}
    (D : ClusteringSpectralData (Hb.toPMap ⊤) vac m) : HasFormGap Hb vac m := by
  intro psi hpsi
  have horth : ⟪vac, psi⟫_ℂ = 0 := inner_eq_zero_symm.mp hpsi
  have h := hasVacuumFormGap_of_clustering D ⟨psi, Submodule.mem_top⟩ horth
  simpa using h

/-- **Equation (43), bounded case.**  The spectrum of the Hamiltonian restricted
to the vacuum complement lies in the half plane `{m ≤ re z}`. -/
theorem spectrum_restrict_subset_halfPlane_of_clustering {Hb : E →L[ℂ] E} {vac : E}
    {m : ℝ} (hinv : ∀ psi ∈ vacuumComplement vac, Hb psi ∈ vacuumComplement vac)
    (D : ClusteringSpectralData (Hb.toPMap ⊤) vac m) :
    spectrum ℂ (restrictComplement Hb hinv) ⊆ {z : ℂ | m ≤ z.re} :=
  spectrum_restrict_subset_halfPlane Hb hinv (hasFormGap_of_clustering_bounded D)

/-- No real value below the clustering rate belongs to the spectrum on the
vacuum complement. -/
theorem notMem_spectrum_of_clustering {Hb : E →L[ℂ] E} {vac : E} {m : ℝ}
    (hinv : ∀ psi ∈ vacuumComplement vac, Hb psi ∈ vacuumComplement vac)
    (D : ClusteringSpectralData (Hb.toPMap ⊤) vac m) {lam : ℝ} (hlt : lam < m) :
    ((lam : ℂ)) ∉ spectrum ℂ (restrictComplement Hb hinv) := by
  intro hmem
  have h := spectrum_restrict_subset_halfPlane_of_clustering hinv D hmem
  simp only [Set.mem_setOf_eq, Complex.ofReal_re] at h
  linarith

/-- **`spec(H|_{Ω^⊥}) ∩ (0,m) = ∅`**, the displayed conclusion (43). -/
theorem spectrum_inter_Ioo_eq_empty_of_clustering {Hb : E →L[ℂ] E} {vac : E} {m : ℝ}
    (hinv : ∀ psi ∈ vacuumComplement vac, Hb psi ∈ vacuumComplement vac)
    (D : ClusteringSpectralData (Hb.toPMap ⊤) vac m) :
    spectrum ℂ (restrictComplement Hb hinv)
        ∩ (fun x : ℝ => (x : ℂ)) '' Set.Ioo 0 m = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Ioo, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro hz ⟨lam, ⟨_, hlam⟩, rfl⟩
  exact notMem_spectrum_of_clustering hinv D hlam hz

end RequestProject.YangMills.BIDI
