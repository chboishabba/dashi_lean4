/-
# Self / external split of the Waleffe network forcing

`WaleffeSelfForcingSign.lean` computes the *self* slot of the projected forcing
of a helical triad exactly, and `WaleffeSelfPhaseEnergyPayment.lean` pays it
with the classical energy expenditure.  This file performs the corresponding
**decomposition of the literal forcing**, so that the two statements can be
composed on the actual Galerkin carrier:

  `f_k = f_k^{self(p,q)} + f_k^{ext(p,q)}`,

where `f_k^{self(p,q)} = −P_k(pairAdvection p q u_p u_q)` collects exactly the
two convolution terms `p' = p` and `p' = q` of the advective sum, and the
external part is the convolution over the remaining retained modes
(`advection_self_external_split`).

The consequences:

* `herm_force_pair_split` — the physical pairing of the forcing of the mode `k`
  against `u_p × u_q` splits into the exact signed square
  `(λ_q − λ_p)‖P_k(u_p×u_q)‖²` and the external residue;
* `abs_herm_force_pair_le` — hence the modal bound
  `|Re⟪f_k, u_p×u_q⟫| ≤ (D_p E_q + E_p D_q) + |Re⟪f_k^{ext}, u_p×u_q⟫|`;
* `GalerkinFlow.selected_pair_forcing_le` and
  `GalerkinFlow.selected_pair_forcing_integrated_le` — over an arbitrary
  selection `χ` of ordered pairs of distinct retained modes the whole first slot
  of the network forcing is bounded by `2E𝔇` plus the external residue, and its
  time integral by `E(t₀)²/ν` plus the integrated external residue.

So, after this file, the entire self contribution to the first slot of the
Waleffe network forcing is *paid*, cutoff-uniformly, by the ordinary energy
identity, and the open budget is exactly the external cross-triad residue.
-/
import RequestProject.NavierStokes.WaleffeSelfPhaseEnergyPayment

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-- The external part of the advective sum at the mode `k`, relative to the
ordered pair `(p,q)`: the convolution over the retained modes other than `p`
and `q`. -/
def externalAdvection (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k p q : Wave) :
    Fin 3 → ℂ :=
  fun i => ∑ p' ∈ (modes.erase p).erase q,
    (Complex.I * (∑ j, u p' j * (((k - p') j : ℤ) : ℂ))) * u (k - p') i

/-- **The advective sum splits into the triad's own pair and the external
remainder.**  For distinct retained modes `p ≠ q` with `k = p + q`, the two
convolution terms `p' = p` and `p' = q` are exactly `pairAdvection p q u_p u_q`. -/
theorem advection_self_external_split (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {p q k : Wave} (hpq : p + q = k) (hp : p ∈ modes) (hq : q ∈ modes) (hne : p ≠ q) :
    advection modes u k
      = fun i => pairAdvection p q (u p) (u q) i + externalAdvection modes u k p q i := by
  classical
  funext i
  set F : Wave → ℂ := fun p' =>
    (Complex.I * (∑ j, u p' j * (((k - p') j : ℤ) : ℂ))) * u (k - p') i with hF
  have hkp : k - p = q := by
    rw [← hpq]; abel
  have hkq : k - q = p := by
    rw [← hpq]; abel
  have hqmem : q ∈ modes.erase p := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hq⟩
  have h1 : ∑ p' ∈ modes, F p' = F p + ∑ p' ∈ modes.erase p, F p' :=
    (Finset.add_sum_erase modes F hp).symm
  have h2 : ∑ p' ∈ modes.erase p, F p' = F q + ∑ p' ∈ (modes.erase p).erase q, F p' :=
    (Finset.add_sum_erase _ F hqmem).symm
  have hFp : F p = (Complex.I * dotb (u p) (wC q)) * u q i := by
    simp only [hF, hkp, dotb, wC]
  have hFq : F q = (Complex.I * dotb (u q) (wC p)) * u p i := by
    simp only [hF, hkq, dotb, wC]
  show ∑ p' ∈ modes, F p' = pairAdvection p q (u p) (u q) i + externalAdvection modes u k p q i
  rw [h1, h2, hFp, hFq]
  simp only [pairAdvection, externalAdvection, hF]
  ring

/-- The modal forcing splits accordingly. -/
theorem modalForcing_self_external_split (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {p q k : Wave} (hpq : p + q = k) (hp : p ∈ modes) (hq : q ∈ modes) (hne : p ≠ q) :
    modalForcing modes u k
      = fun i => -(leray k (pairAdvection p q (u p) (u q)) i)
          + -(leray k (externalAdvection modes u k p q) i) := by
  funext i
  simp only [modalForcing]
  rw [advection_self_external_split modes u hpq hp hq hne,
    leray_add k (pairAdvection p q (u p) (u q)) (externalAdvection modes u k p q)]
  ring

/-- **The physical forcing pairing splits into the exact self square and the
external residue.** -/
theorem herm_force_pair_split (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {p q k : Wave} (hpq : p + q = k) (hp : p ∈ modes) (hq : q ∈ modes) (hne : p ≠ q)
    (hk : wsq k ≠ 0) {lp lq : ℝ}
    (hbp : cross (wC p) (u p) = fun i => (-Complex.I) * (lp : ℂ) * u p i)
    (hbq : cross (wC q) (u q) = fun i => (-Complex.I) * (lq : ℂ) * u q i) :
    (herm (modalForcing modes u k) (cross (u p) (u q))).re
      = (lq - lp) * nsq (leray k (cross (u p) (u q)))
        + (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
            (cross (u p) (u q))).re := by
  rw [modalForcing_self_external_split modes u hpq hp hq hne, herm_add_left,
    Complex.add_re, pair_self_forcing_signed_square hpq hk (u p) (u q) lp lq hbp hbq]

/-- **The modal bound for the first slot of the network forcing.**  The self part
is paid by the modal energy–dissipation kernel; only the external residue
remains. -/
theorem abs_herm_force_pair_le (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {p q k : Wave} (hpq : p + q = k) (hp : p ∈ modes) (hq : q ∈ modes) (hne : p ≠ q)
    (hk : wsq k ≠ 0) (hwp : 1 ≤ wsq p) (hwq : 1 ≤ wsq q) {lp lq : ℝ}
    (hbp : cross (wC p) (u p) = fun i => (-Complex.I) * (lp : ℂ) * u p i)
    (hbq : cross (wC q) (u q) = fun i => (-Complex.I) * (lq : ℂ) * u q i) :
    |(herm (modalForcing modes u k) (cross (u p) (u q))).re|
      ≤ ((wsq p * nsq (u p)) * nsq (u q) + nsq (u p) * (wsq q * nsq (u q)))
        + |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
            (cross (u p) (u q))).re| := by
  rw [herm_force_pair_split modes u hpq hp hq hne hk hbp hbq]
  have hself : |(lq - lp) * nsq (leray k (cross (u p) (u q)))|
      ≤ (wsq p * nsq (u p)) * nsq (u q) + nsq (u p) * (wsq q * nsq (u q)) := by
    rw [abs_mul, abs_of_nonneg (nsq_nonneg (leray k (cross (u p) (u q))))]
    exact self_phase_ED_bound hk hwp hwq hbp hbq
  calc |(lq - lp) * nsq (leray k (cross (u p) (u q)))
        + (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
            (cross (u p) (u q))).re|
      ≤ |(lq - lp) * nsq (leray k (cross (u p) (u q)))|
        + |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
            (cross (u p) (u q))).re| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## The selected network on a Galerkin flow -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The external residue of the first forcing slot of the ordered pair `x`. -/
def externalResidue (t : ℝ) (x : Wave × Wave) : ℝ :=
  (herm (fun i => -(leray (x.1 + x.2)
      (externalAdvection G.modes (G.u t) (x.1 + x.2) x.1 x.2) i))
    (cross (G.u t x.1) (G.u t x.2))).re

/-- **The whole first slot of the selected network forcing is bounded by
`2E𝔇` plus the external residue.**  `χ` is an arbitrary selection of ordered
pairs of *distinct* retained modes whose sum is again retained. -/
theorem selected_pair_forcing_le (t : ℝ) (chi : Finset (Wave × Wave))
    (hchi : chi ⊆ G.modes ×ˢ G.modes) (hne : ∀ x ∈ chi, x.1 ≠ x.2)
    (hsum : ∀ x ∈ chi, x.1 + x.2 ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    ∑ x ∈ chi, |(herm (G.force t (x.1 + x.2)) (cross (G.u t x.1) (G.u t x.2))).re|
      ≤ 2 * G.energy t * G.dissipation t + ∑ x ∈ chi, |G.externalResidue t x| := by
  classical
  set E : Wave → ℝ := fun p => nsq (G.u t p) with hEdef
  set D : Wave → ℝ := fun p => wsq p * nsq (G.u t p) with hDdef
  have hterm : ∀ x ∈ chi,
      |(herm (G.force t (x.1 + x.2)) (cross (G.u t x.1) (G.u t x.2))).re|
        ≤ (D x.1 * E x.2 + E x.1 * D x.2) + |G.externalResidue t x| := by
    intro x hx
    have hmem := Finset.mem_product.mp (hchi hx)
    exact abs_herm_force_pair_le G.modes (G.u t) rfl hmem.1 hmem.2 (hne x hx)
      (G.wsq_ne_zero_of_mem (hsum x hx))
      (G.one_le_wsq_of_mem hmem.1) (G.one_le_wsq_of_mem hmem.2) (hbel x.1 hmem.1)
      (hbel x.2 hmem.2)
  have hle := Finset.sum_le_sum hterm
  have hsplit : ∑ x ∈ chi, ((D x.1 * E x.2 + E x.1 * D x.2) + |G.externalResidue t x|)
      = (∑ x ∈ chi, (D x.1 * E x.2 + E x.1 * D x.2)) + ∑ x ∈ chi, |G.externalResidue t x| :=
    Finset.sum_add_distrib
  have hED := selected_pair_ED_sum G.modes chi hchi E D
    (fun i _ => nsq_nonneg _) (fun i _ => mul_nonneg (wsq_nonneg' i) (nsq_nonneg _))
  have hE : ∑ i ∈ G.modes, E i = G.energy t := rfl
  have hD : ∑ i ∈ G.modes, D i = G.dissipation t := rfl
  rw [hE, hD] at hED
  rw [hsplit] at hle
  linarith

/-! ### Continuity in time -/

theorem continuous_externalAdvection (k p q : Wave) (i : Fin 3) :
    Continuous fun t => externalAdvection G.modes (G.u t) k p q i := by
  classical
  show Continuous fun t => ∑ p' ∈ (G.modes.erase p).erase q,
    (Complex.I * (∑ j, G.u t p' j * (((k - p') j : ℤ) : ℂ))) * G.u t (k - p') i
  refine continuous_finset_sum _ fun p' _ => Continuous.mul ?_ (G.continuous_u (k - p') i)
  exact continuous_const.mul
    (continuous_finset_sum _ fun j _ => (G.continuous_u p' j).mul continuous_const)

theorem continuous_externalResidue (x : Wave × Wave) :
    Continuous fun t => G.externalResidue t x := by
  refine Complex.continuous_re.comp ?_
  exact continuous_herm_of
    (fun i => ((continuous_leray_of
      (fun j => G.continuous_externalAdvection (x.1 + x.2) x.1 x.2 j) (x.1 + x.2) i)).neg)
    (continuous_cross_of (G.continuous_u x.1) (G.continuous_u x.2))

/-- **The integrated first slot of the selected network forcing.**  The self part
is paid outright by the initial energy; only the external cross-triad residue
remains. -/
theorem selected_pair_forcing_integrated_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (chi : Finset (Wave × Wave)) (hchi : chi ⊆ G.modes ×ˢ G.modes)
    (hne : ∀ x ∈ chi, x.1 ≠ x.2) (hsum : ∀ x ∈ chi, x.1 + x.2 ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    (∫ t in t₀..t₁,
        ∑ x ∈ chi, |(herm (G.force t (x.1 + x.2)) (cross (G.u t x.1) (G.u t x.2))).re|)
      ≤ G.energy t₀ ^ 2 / G.nu
        + ∫ t in t₀..t₁, ∑ x ∈ chi, |G.externalResidue t x| := by
  classical
  have hcontL : Continuous fun t =>
      ∑ x ∈ chi, |(herm (G.force t (x.1 + x.2)) (cross (G.u t x.1) (G.u t x.2))).re| := by
    refine continuous_finset_sum _ fun x _ => continuous_abs.comp ?_
    exact Complex.continuous_re.comp (continuous_herm_of (G.continuous_force (x.1 + x.2))
      (continuous_cross_of (G.continuous_u x.1) (G.continuous_u x.2)))
  have hcontR : Continuous fun t => 2 * G.energy t * G.dissipation t
      + ∑ x ∈ chi, |G.externalResidue t x| :=
    ((continuous_const.mul G.continuous_energy).mul G.continuous_dissipation).add
      (continuous_finset_sum _ fun x _ => continuous_abs.comp (G.continuous_externalResidue x))
  have hmono : (∫ t in t₀..t₁,
      ∑ x ∈ chi, |(herm (G.force t (x.1 + x.2)) (cross (G.u t x.1) (G.u t x.2))).re|)
      ≤ ∫ t in t₀..t₁, (2 * G.energy t * G.dissipation t
          + ∑ x ∈ chi, |G.externalResidue t x|) := by
    refine intervalIntegral.integral_mono_on ht (hcontL.intervalIntegrable _ _)
      (hcontR.intervalIntegrable _ _) ?_
    intro t _
    exact G.selected_pair_forcing_le t chi hchi hne hsum l (hbel t)
  have hsplit : (∫ t in t₀..t₁, (2 * G.energy t * G.dissipation t
        + ∑ x ∈ chi, |G.externalResidue t x|))
      = (∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t)
        + ∫ t in t₀..t₁, ∑ x ∈ chi, |G.externalResidue t x| := by
    refine intervalIntegral.integral_add ?_ ?_
    · exact (((continuous_const.mul G.continuous_energy).mul
        G.continuous_dissipation)).intervalIntegrable _ _
    · exact (continuous_finset_sum _ fun x _ =>
        continuous_abs.comp (G.continuous_externalResidue x)).intervalIntegrable _ _
  have hpay := G.integral_energy_dissipation_le hnu ht
  rw [hsplit] at hmono
  linarith

end GalerkinFlow

end ClayNS.Waleffe
