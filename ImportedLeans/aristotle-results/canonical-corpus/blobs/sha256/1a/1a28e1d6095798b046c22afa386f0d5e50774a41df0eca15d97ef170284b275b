/-
# The whole triad-internal Waleffe network forcing is paid by the energy expenditure

`WaleffeSelfPhaseEnergyPayment.lean` pays the *first* slot of the network
forcing of a helical triad — the contribution of `f_k` paired against
`u_p × u_q` — with the classical energy expenditure.  This file does the same
for the two remaining slots, `⟪u_k, f_p × u_q⟫` and `⟪u_k, u_p × f_q⟫`, and
assembles the three into a single statement about the *triad-internal* part of
the Waleffe network forcing

  `F_τ = Re[⟪f_k, u_p×u_q⟫ + ⟪u_k, f_p×u_q⟫ + ⟪u_k, u_p×f_q⟫]`,   `k = p + q`.

The triad-internal part is obtained by replacing each `f` by the two convolution
terms of the triad itself: `f_k ↦ −P_k(pairAdvection p q u_p u_q)`,
`f_p ↦ −P_p(pairAdvection k (−q) u_k u_{−q})`,
`f_q ↦ −P_q(pairAdvection k (−p) u_k u_{−p})`
(`triadSelfForcing`); this is literally what the advective convolution
contributes from inside the triad, by `advection_self_external_split`.

Results:

* `slot_forcing_chain`, `slot_forcing_chain'` — the two remaining slots are
  controlled by the same rotational normal form: the helicity gap times a
  product of four modal norms;
* `abs_slot_forcing_le_ED`, `abs_slot_forcing_le_ED'` — hence by the same
  energy–dissipation kernel `D_a E_b + E_a D_b` as the first slot;
* `GalerkinFlow.abs_triadSelfForcing_le` — the modal bound for the full
  triad-internal forcing;
* `GalerkinFlow.selected_triad_internal_le` — over an arbitrary selection `S` of
  resonant triads, `∑_{τ∈S} |F_τ^{int}| ≤ 6 E(t) 𝔇(t)`;
* `GalerkinFlow.selected_triad_internal_integrated_le` — and therefore
  `∫_{t₀}^{t₁} ∑_{τ∈S} |F_τ^{int}| dt ≤ 3 E(t₀)²/ν`, uniformly in the Galerkin
  cutoff, in the frequency range and in the number of triads selected.

Only the genuinely external cross-triad forcing is left outside this payment.
-/
import RequestProject.NavierStokes.WaleffeExternalForcingSplit

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-! ## Norm-level Cauchy–Schwarz and cross bounds -/

theorem norm_herm_le (u v : Fin 3 → ℂ) : ‖herm u v‖ ≤ nrm u * nrm v := by
  have h := normSq_herm_le u v
  rw [Complex.norm_def, nrm, nrm, ← Real.sqrt_mul (nsq_nonneg u)]
  exact Real.sqrt_le_sqrt h

theorem nrm_cross_le (u v : Fin 3 → ℂ) : nrm (cross u v) ≤ nrm u * nrm v := by
  have h := nsq_cross_le u v
  rw [nrm, nrm, nrm, ← Real.sqrt_mul (nsq_nonneg u)]
  exact Real.sqrt_le_sqrt h

theorem wsq_neg (k : Wave) : wsq (-k) = wsq k := by
  simp [wsq]

theorem wlen_neg (k : Wave) : wlen (-k) = wlen k := by
  simp [wlen, wsq_neg]

theorem nsq_eq_nrm_sq (u : Fin 3 → ℂ) : nsq u = nrm u * nrm u := by
  rw [nrm, Real.mul_self_sqrt (nsq_nonneg u)]

/-! ## The two remaining slots of the network forcing -/

/-- The middle slot `⟪u_k, f_p^{self} × u_q⟫` in terms of the helicity gap and
the modal norms. -/
theorem slot_forcing_chain {k q p : Wave} (hkq : k + (-q) = p) (hp : wsq p ≠ 0)
    {uk umq uq : Fin 3 → ℂ} {lk lmq : ℝ}
    (hbk : cross (wC k) uk = fun i => (-Complex.I) * (lk : ℂ) * uk i)
    (hbmq : cross (wC (-q)) umq = fun i => (-Complex.I) * (lmq : ℂ) * umq i) :
    |(herm uk (cross (fun i => -(leray p (pairAdvection k (-q) uk umq) i)) uq)).re|
      ≤ |lmq - lk| * (nrm uk * (nrm uk * nrm umq) * nrm uq) := by
  have hL := leray_pairAdvection hkq hp uk umq lk lmq hbk hbmq
  set X := leray p (cross uk umq) with hX
  have hV : (fun i => -(leray p (pairAdvection k (-q) uk umq) i))
      = fun i => (((lmq - lk : ℝ)) : ℂ) * X i := by
    funext i
    rw [hL]
    push_cast
    ring
  rw [hV, cross_smul_left, herm_smul_right]
  have hre : ((((lmq - lk : ℝ)) : ℂ) * herm uk (cross X uq)).re
      = (lmq - lk) * (herm uk (cross X uq)).re := by
    simp [Complex.mul_re]
  rw [hre, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hnn := nrm_nonneg uk
  calc |(herm uk (cross X uq)).re| ≤ ‖herm uk (cross X uq)‖ := Complex.abs_re_le_norm _
    _ ≤ nrm uk * nrm (cross X uq) := norm_herm_le _ _
    _ ≤ nrm uk * (nrm X * nrm uq) := mul_le_mul_of_nonneg_left (nrm_cross_le _ _) hnn
    _ ≤ nrm uk * ((nrm uk * nrm umq) * nrm uq) := by
        have h4 : nrm X ≤ nrm uk * nrm umq :=
          le_trans (nrm_leray_le p _ hp) (nrm_cross_le _ _)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (nrm_nonneg uq)) hnn
    _ = nrm uk * (nrm uk * nrm umq) * nrm uq := by ring

/-- The last slot `⟪u_k, u_p × f_q^{self}⟫` in terms of the helicity gap and the
modal norms. -/
theorem slot_forcing_chain' {k p q : Wave} (hkp : k + (-p) = q) (hq : wsq q ≠ 0)
    {uk ump up : Fin 3 → ℂ} {lk lmp : ℝ}
    (hbk : cross (wC k) uk = fun i => (-Complex.I) * (lk : ℂ) * uk i)
    (hbmp : cross (wC (-p)) ump = fun i => (-Complex.I) * (lmp : ℂ) * ump i) :
    |(herm uk (cross up (fun i => -(leray q (pairAdvection k (-p) uk ump) i)))).re|
      ≤ |lmp - lk| * (nrm uk * (nrm up * (nrm uk * nrm ump))) := by
  have hL := leray_pairAdvection hkp hq uk ump lk lmp hbk hbmp
  set X := leray q (cross uk ump) with hX
  have hV : (fun i => -(leray q (pairAdvection k (-p) uk ump) i))
      = fun i => (((lmp - lk : ℝ)) : ℂ) * X i := by
    funext i
    rw [hL]
    push_cast
    ring
  have hcross : cross up (fun i => (((lmp - lk : ℝ)) : ℂ) * X i)
      = fun i => (((lmp - lk : ℝ)) : ℂ) * cross up X i := by
    funext i
    fin_cases i <;> simp [cross, crossProduct] <;> ring
  rw [hV, hcross, herm_smul_right]
  have hre : ((((lmp - lk : ℝ)) : ℂ) * herm uk (cross up X)).re
      = (lmp - lk) * (herm uk (cross up X)).re := by
    simp [Complex.mul_re]
  rw [hre, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hnn := nrm_nonneg uk
  calc |(herm uk (cross up X)).re| ≤ ‖herm uk (cross up X)‖ := Complex.abs_re_le_norm _
    _ ≤ nrm uk * nrm (cross up X) := norm_herm_le _ _
    _ ≤ nrm uk * (nrm up * nrm X) := mul_le_mul_of_nonneg_left (nrm_cross_le _ _) hnn
    _ ≤ nrm uk * (nrm up * (nrm uk * nrm ump)) := by
        have h4 : nrm X ≤ nrm uk * nrm ump :=
          le_trans (nrm_leray_le q _ hq) (nrm_cross_le _ _)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h4 (nrm_nonneg up)) hnn

/-- The helicity gap of a pair of nonzero lattice modes, one of them reflected,
is bounded by the sum of the two squared frequencies. -/
theorem abs_gap_le {k q : Wave} (hwk : 1 ≤ wsq k) (hwq : 1 ≤ wsq q)
    {uk umq : Fin 3 → ℂ} {lk lmq : ℝ} (huk : nsq uk ≠ 0) (humq : nsq umq ≠ 0)
    (hbk : cross (wC k) uk = fun i => (-Complex.I) * (lk : ℂ) * uk i)
    (hbmq : cross (wC (-q)) umq = fun i => (-Complex.I) * (lmq : ℂ) * umq i) :
    |lmq - lk| ≤ wsq k + wsq q := by
  have h1 : |lk| ≤ wlen k := abs_helical_le_wlen huk hbk
  have h2 : |lmq| ≤ wlen (-q) := abs_helical_le_wlen humq hbmq
  rw [wlen_neg] at h2
  have h3 : |lmq - lk| ≤ |lmq| + |lk| := abs_sub _ _
  have h4 := wlen_le_wsq hwk
  have h5 := wlen_le_wsq hwq
  linarith

/-- **The middle slot obeys the energy–dissipation kernel bound.** -/
theorem abs_slot_forcing_le_ED {k q p : Wave} (hkq : k + (-q) = p) (hp : wsq p ≠ 0)
    (hwk : 1 ≤ wsq k) (hwq : 1 ≤ wsq q)
    {uk umq uq : Fin 3 → ℂ} {lk lmq : ℝ} (hreal : nsq umq = nsq uq)
    (hbk : cross (wC k) uk = fun i => (-Complex.I) * (lk : ℂ) * uk i)
    (hbmq : cross (wC (-q)) umq = fun i => (-Complex.I) * (lmq : ℂ) * umq i) :
    |(herm uk (cross (fun i => -(leray p (pairAdvection k (-q) uk umq) i)) uq)).re|
      ≤ (wsq k * nsq uk) * nsq uq + nsq uk * (wsq q * nsq uq) := by
  have hchain := slot_forcing_chain (uq := uq) hkq hp hbk hbmq
  have hnrm : nrm umq = nrm uq := by rw [nrm, nrm, hreal]
  rw [hnrm] at hchain
  have hprod : nrm uk * (nrm uk * nrm uq) * nrm uq = nsq uk * nsq uq := by
    rw [nsq_eq_nrm_sq, nsq_eq_nrm_sq]; ring
  rw [hprod] at hchain
  rcases eq_or_ne (nsq uk) 0 with huk | huk
  · rw [huk] at hchain ⊢
    simpa using hchain
  rcases eq_or_ne (nsq uq) 0 with huq | huq
  · rw [huq] at hchain ⊢
    simpa using hchain
  have humq : nsq umq ≠ 0 := by rw [hreal]; exact huq
  have hgap := abs_gap_le hwk hwq huk humq hbk hbmq
  have hE := nsq_nonneg uk
  have hF := nsq_nonneg uq
  nlinarith [hchain, mul_nonneg hE hF]

/-- **The last slot obeys the energy–dissipation kernel bound.** -/
theorem abs_slot_forcing_le_ED' {k p q : Wave} (hkp : k + (-p) = q) (hq : wsq q ≠ 0)
    (hwk : 1 ≤ wsq k) (hwp : 1 ≤ wsq p)
    {uk ump up : Fin 3 → ℂ} {lk lmp : ℝ} (hreal : nsq ump = nsq up)
    (hbk : cross (wC k) uk = fun i => (-Complex.I) * (lk : ℂ) * uk i)
    (hbmp : cross (wC (-p)) ump = fun i => (-Complex.I) * (lmp : ℂ) * ump i) :
    |(herm uk (cross up (fun i => -(leray q (pairAdvection k (-p) uk ump) i)))).re|
      ≤ (wsq k * nsq uk) * nsq up + nsq uk * (wsq p * nsq up) := by
  have hchain := slot_forcing_chain' (up := up) hkp hq hbk hbmp
  have hnrm : nrm ump = nrm up := by rw [nrm, nrm, hreal]
  rw [hnrm] at hchain
  have hprod : nrm uk * (nrm up * (nrm uk * nrm up)) = nsq uk * nsq up := by
    rw [nsq_eq_nrm_sq, nsq_eq_nrm_sq]; ring
  rw [hprod] at hchain
  rcases eq_or_ne (nsq uk) 0 with huk | huk
  · rw [huk] at hchain ⊢
    simpa using hchain
  rcases eq_or_ne (nsq up) 0 with hup | hup
  · rw [hup] at hchain ⊢
    simpa using hchain
  have hump : nsq ump ≠ 0 := by rw [hreal]; exact hup
  have hgap := abs_gap_le hwk hwp huk hump hbk hbmp
  have hE := nsq_nonneg uk
  have hF := nsq_nonneg up
  nlinarith [hchain, mul_nonneg hE hF]

/-! ## The triad-internal network forcing of a Galerkin flow -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The reality condition makes the modal energy even in the wavevector. -/
theorem nsq_u_neg (t : ℝ) (k : Wave) : nsq (G.u t (-k)) = nsq (G.u t k) := by
  simp only [nsq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [G.reality t k i, Complex.normSq_conj]

/-- **The triad-internal Waleffe network forcing**: the network forcing `F_τ`
with each modal forcing replaced by the two convolution terms contributed by the
triad itself. -/
def triadSelfForcing (t : ℝ) (τ : Wave × Wave × Wave) : ℝ :=
  (herm (fun i => -(leray τ.1 (pairAdvection τ.2.1 τ.2.2 (G.u t τ.2.1) (G.u t τ.2.2)) i))
      (cross (G.u t τ.2.1) (G.u t τ.2.2))).re
  + (herm (G.u t τ.1)
      (cross (fun i => -(leray τ.2.1
          (pairAdvection τ.1 (-τ.2.2) (G.u t τ.1) (G.u t (-τ.2.2))) i)) (G.u t τ.2.2))).re
  + (herm (G.u t τ.1)
      (cross (G.u t τ.2.1) (fun i => -(leray τ.2.2
          (pairAdvection τ.1 (-τ.2.1) (G.u t τ.1) (G.u t (-τ.2.1))) i)))).re

/-- **The modal bound for the triad-internal network forcing.** -/
theorem abs_triadSelfForcing_le (t : ℝ) {τ : Wave × Wave × Wave} (hτ : τ ∈ triads G.modes)
    (hsym : ∀ k ∈ G.modes, -k ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    |G.triadSelfForcing t τ|
      ≤ ((wsq τ.2.1 * nsq (G.u t τ.2.1)) * nsq (G.u t τ.2.2)
          + nsq (G.u t τ.2.1) * (wsq τ.2.2 * nsq (G.u t τ.2.2)))
        + ((wsq τ.1 * nsq (G.u t τ.1)) * nsq (G.u t τ.2.2)
          + nsq (G.u t τ.1) * (wsq τ.2.2 * nsq (G.u t τ.2.2)))
        + ((wsq τ.1 * nsq (G.u t τ.1)) * nsq (G.u t τ.2.1)
          + nsq (G.u t τ.1) * (wsq τ.2.1 * nsq (G.u t τ.2.1))) := by
  obtain ⟨hk, hp, hq, hres⟩ := mem_triads hτ
  have hwk := G.one_le_wsq_of_mem hk
  have hwp := G.one_le_wsq_of_mem hp
  have hwq := G.one_le_wsq_of_mem hq
  have hnk := G.wsq_ne_zero_of_mem hk
  have hnp := G.wsq_ne_zero_of_mem hp
  have hnq := G.wsq_ne_zero_of_mem hq
  have h1 : |(herm (fun i => -(leray τ.1
        (pairAdvection τ.2.1 τ.2.2 (G.u t τ.2.1) (G.u t τ.2.2)) i))
          (cross (G.u t τ.2.1) (G.u t τ.2.2))).re|
      ≤ (wsq τ.2.1 * nsq (G.u t τ.2.1)) * nsq (G.u t τ.2.2)
        + nsq (G.u t τ.2.1) * (wsq τ.2.2 * nsq (G.u t τ.2.2)) :=
    abs_pair_self_forcing_le_ED hres.symm hnk hwp hwq (hbel τ.2.1 hp) (hbel τ.2.2 hq)
  have hkq : τ.1 + (-τ.2.2) = τ.2.1 := by rw [hres]; abel
  have hkp : τ.1 + (-τ.2.1) = τ.2.2 := by rw [hres]; abel
  have h2 : |(herm (G.u t τ.1)
        (cross (fun i => -(leray τ.2.1
          (pairAdvection τ.1 (-τ.2.2) (G.u t τ.1) (G.u t (-τ.2.2))) i)) (G.u t τ.2.2))).re|
      ≤ (wsq τ.1 * nsq (G.u t τ.1)) * nsq (G.u t τ.2.2)
        + nsq (G.u t τ.1) * (wsq τ.2.2 * nsq (G.u t τ.2.2)) :=
    abs_slot_forcing_le_ED hkq hnp hwk hwq (G.nsq_u_neg t τ.2.2) (hbel τ.1 hk)
      (hbel (-τ.2.2) (hsym τ.2.2 hq))
  have h3 : |(herm (G.u t τ.1)
        (cross (G.u t τ.2.1) (fun i => -(leray τ.2.2
          (pairAdvection τ.1 (-τ.2.1) (G.u t τ.1) (G.u t (-τ.2.1))) i)))).re|
      ≤ (wsq τ.1 * nsq (G.u t τ.1)) * nsq (G.u t τ.2.1)
        + nsq (G.u t τ.1) * (wsq τ.2.1 * nsq (G.u t τ.2.1)) :=
    abs_slot_forcing_le_ED' hkp hnq hwk hwp (G.nsq_u_neg t τ.2.1) (hbel τ.1 hk)
      (hbel (-τ.2.1) (hsym τ.2.1 hp))
  simp only [triadSelfForcing]
  refine le_trans (abs_add_three _ _ _) ?_
  linarith

/-! ### Summation over a selected family of triads -/

theorem selected_triad_internal_le (t : ℝ) (S : Finset (Wave × Wave × Wave))
    (hS : S ⊆ triads G.modes) (hsym : ∀ k ∈ G.modes, -k ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    ∑ τ ∈ S, |G.triadSelfForcing t τ| ≤ 6 * G.energy t * G.dissipation t := by
  classical
  set E : Wave → ℝ := fun p => nsq (G.u t p) with hEdef
  set D : Wave → ℝ := fun p => wsq p * nsq (G.u t p) with hDdef
  have hEnn : ∀ i ∈ G.modes, 0 ≤ E i := fun i _ => nsq_nonneg _
  have hDnn : ∀ i ∈ G.modes, 0 ≤ D i := fun i _ => mul_nonneg (wsq_nonneg' i) (nsq_nonneg _)
  have hE : ∑ i ∈ G.modes, E i = G.energy t := rfl
  have hD : ∑ i ∈ G.modes, D i = G.dissipation t := rfl
  have hstep : ∑ τ ∈ S, |G.triadSelfForcing t τ|
      ≤ ∑ τ ∈ S, ((D τ.2.1 * E τ.2.2 + E τ.2.1 * D τ.2.2)
          + (D τ.1 * E τ.2.2 + E τ.1 * D τ.2.2)
          + (D τ.1 * E τ.2.1 + E τ.1 * D τ.2.1)) :=
    Finset.sum_le_sum fun τ hτ => G.abs_triadSelfForcing_le t (hS hτ) hsym l hbel
  have hsplit : ∑ τ ∈ S, ((D τ.2.1 * E τ.2.2 + E τ.2.1 * D τ.2.2)
        + (D τ.1 * E τ.2.2 + E τ.1 * D τ.2.2)
        + (D τ.1 * E τ.2.1 + E τ.1 * D τ.2.1))
      = (∑ τ ∈ S, (D τ.2.1 * E τ.2.2 + E τ.2.1 * D τ.2.2))
        + (∑ τ ∈ S, (D τ.1 * E τ.2.2 + E τ.1 * D τ.2.2))
        + ∑ τ ∈ S, (D τ.1 * E τ.2.1 + E τ.1 * D τ.2.1) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hinj1 : Set.InjOn (fun τ : Wave × Wave × Wave => (τ.2.1, τ.2.2)) S := by
    intro a ha b hb hab
    obtain ⟨-, -, -, hares⟩ := mem_triads (hS ha)
    obtain ⟨-, -, -, hbres⟩ := mem_triads (hS hb)
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hk : a.1 = b.1 := by rw [hares, hbres, h1, h2]
    exact Prod.ext_iff.mpr ⟨hk, Prod.ext_iff.mpr ⟨h1, h2⟩⟩
  have hinj2 : Set.InjOn (fun τ : Wave × Wave × Wave => (τ.1, τ.2.2)) S := by
    intro a ha b hb hab
    obtain ⟨-, -, -, hares⟩ := mem_triads (hS ha)
    obtain ⟨-, -, -, hbres⟩ := mem_triads (hS hb)
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have h3 : a.2.1 = b.2.1 := by
      have ha1 : a.2.1 = a.1 - a.2.2 := by rw [hares]; abel
      have hb1 : b.2.1 = b.1 - b.2.2 := by rw [hbres]; abel
      rw [ha1, hb1, h1, h2]
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h3, h2⟩⟩
  have hinj3 : Set.InjOn (fun τ : Wave × Wave × Wave => (τ.1, τ.2.1)) S := by
    intro a ha b hb hab
    obtain ⟨-, -, -, hares⟩ := mem_triads (hS ha)
    obtain ⟨-, -, -, hbres⟩ := mem_triads (hS hb)
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have h3 : a.2.2 = b.2.2 := by
      have ha1 : a.2.2 = a.1 - a.2.1 := by rw [hares]; abel
      have hb1 : b.2.2 = b.1 - b.2.1 := by rw [hbres]; abel
      rw [ha1, hb1, h1, h2]
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
  have hsub1 : S.image (fun τ : Wave × Wave × Wave => (τ.2.1, τ.2.2)) ⊆ G.modes ×ˢ G.modes := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨-, hp, hq, -⟩ := mem_triads (hS hτ)
    exact Finset.mem_product.mpr ⟨hp, hq⟩
  have hsub2 : S.image (fun τ : Wave × Wave × Wave => (τ.1, τ.2.2)) ⊆ G.modes ×ˢ G.modes := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk, -, hq, -⟩ := mem_triads (hS hτ)
    exact Finset.mem_product.mpr ⟨hk, hq⟩
  have hsub3 : S.image (fun τ : Wave × Wave × Wave => (τ.1, τ.2.1)) ⊆ G.modes ×ˢ G.modes := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk, hp, -, -⟩ := mem_triads (hS hτ)
    exact Finset.mem_product.mpr ⟨hk, hp⟩
  have hbnd1 : ∑ τ ∈ S, (D τ.2.1 * E τ.2.2 + E τ.2.1 * D τ.2.2)
      ≤ 2 * G.energy t * G.dissipation t := by
    have himg : ∑ x ∈ S.image (fun τ : Wave × Wave × Wave => (τ.2.1, τ.2.2)),
          (D x.1 * E x.2 + E x.1 * D x.2)
        = ∑ τ ∈ S, (D τ.2.1 * E τ.2.2 + E τ.2.1 * D τ.2.2) :=
      Finset.sum_image fun a ha b hb hab => hinj1 ha hb hab
    have hbound := selected_pair_ED_sum G.modes _ hsub1 E D hEnn hDnn
    rw [hE, hD] at hbound
    rw [← himg]
    exact hbound
  have hbnd2 : ∑ τ ∈ S, (D τ.1 * E τ.2.2 + E τ.1 * D τ.2.2)
      ≤ 2 * G.energy t * G.dissipation t := by
    have himg : ∑ x ∈ S.image (fun τ : Wave × Wave × Wave => (τ.1, τ.2.2)),
          (D x.1 * E x.2 + E x.1 * D x.2)
        = ∑ τ ∈ S, (D τ.1 * E τ.2.2 + E τ.1 * D τ.2.2) :=
      Finset.sum_image fun a ha b hb hab => hinj2 ha hb hab
    have hbound := selected_pair_ED_sum G.modes _ hsub2 E D hEnn hDnn
    rw [hE, hD] at hbound
    rw [← himg]
    exact hbound
  have hbnd3 : ∑ τ ∈ S, (D τ.1 * E τ.2.1 + E τ.1 * D τ.2.1)
      ≤ 2 * G.energy t * G.dissipation t := by
    have himg : ∑ x ∈ S.image (fun τ : Wave × Wave × Wave => (τ.1, τ.2.1)),
          (D x.1 * E x.2 + E x.1 * D x.2)
        = ∑ τ ∈ S, (D τ.1 * E τ.2.1 + E τ.1 * D τ.2.1) :=
      Finset.sum_image fun a ha b hb hab => hinj3 ha hb hab
    have hbound := selected_pair_ED_sum G.modes _ hsub3 E D hEnn hDnn
    rw [hE, hD] at hbound
    rw [← himg]
    exact hbound
  rw [hsplit] at hstep
  linarith

/-- Continuity in time of the triad-internal forcing. -/
theorem continuous_triadSelfForcing (τ : Wave × Wave × Wave) :
    Continuous fun t => G.triadSelfForcing t τ := by
  have hpair : ∀ (a b : Wave) (m : Wave),
      ∀ i, Continuous fun t => leray m (pairAdvection a b (G.u t a) (G.u t b)) i := by
    intro a b m i
    refine continuous_leray_of (fun j => ?_) m i
    show Continuous fun t =>
      (Complex.I * dotb (G.u t a) (wC b)) * G.u t b j + (Complex.I * dotb (G.u t b) (wC a))
        * G.u t a j
    have hd : ∀ (c d : Wave), Continuous fun t => dotb (G.u t c) (wC d) := by
      intro c d
      exact continuous_finset_sum _ fun m _ => (G.continuous_u c m).mul continuous_const
    exact ((continuous_const.mul (hd a b)).mul (G.continuous_u b j)).add
      ((continuous_const.mul (hd b a)).mul (G.continuous_u a j))
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · exact Complex.continuous_re.comp (continuous_herm_of
      (fun i => (hpair τ.2.1 τ.2.2 τ.1 i).neg)
      (continuous_cross_of (G.continuous_u τ.2.1) (G.continuous_u τ.2.2)))
  · exact Complex.continuous_re.comp (continuous_herm_of (G.continuous_u τ.1)
      (continuous_cross_of (fun i => (hpair τ.1 (-τ.2.2) τ.2.1 i).neg)
        (G.continuous_u τ.2.2)))
  · exact Complex.continuous_re.comp (continuous_herm_of (G.continuous_u τ.1)
      (continuous_cross_of (G.continuous_u τ.2.1)
        (fun i => (hpair τ.1 (-τ.2.1) τ.2.2 i).neg)))

/-- **The triad-internal Waleffe network forcing is paid outright by the
classical energy expenditure**: for any selection `S` of resonant triads of the
retained modes,

  `∫_{t₀}^{t₁} ∑_{τ∈S} |F_τ^{int}| dt ≤ 3 E(t₀)²/ν`,

a bound involving only the initial energy and the viscosity, hence uniform in
the Galerkin cutoff, in the frequency range and in the number of triads. -/
theorem selected_triad_internal_integrated_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (S : Finset (Wave × Wave × Wave)) (hS : S ⊆ triads G.modes)
    (hsym : ∀ k ∈ G.modes, -k ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    (∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|) ≤ 3 * G.energy t₀ ^ 2 / G.nu := by
  have hcontL : Continuous fun t => ∑ τ ∈ S, |G.triadSelfForcing t τ| :=
    continuous_finset_sum _ fun τ _ => continuous_abs.comp (G.continuous_triadSelfForcing τ)
  have hcontR : Continuous fun t => 3 * (2 * G.energy t * G.dissipation t) :=
    continuous_const.mul ((continuous_const.mul G.continuous_energy).mul G.continuous_dissipation)
  have hmono : (∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|)
      ≤ ∫ t in t₀..t₁, 3 * (2 * G.energy t * G.dissipation t) := by
    refine intervalIntegral.integral_mono_on ht (hcontL.intervalIntegrable _ _)
      (hcontR.intervalIntegrable _ _) ?_
    intro t _
    have := G.selected_triad_internal_le t S hS hsym l (hbel t)
    linarith
  have hpull : (∫ t in t₀..t₁, 3 * (2 * G.energy t * G.dissipation t))
      = 3 * ∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t :=
    intervalIntegral.integral_const_mul _ _
  have hpay := G.integral_energy_dissipation_le hnu ht
  rw [hpull] at hmono
  have : 3 * (∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t)
      ≤ 3 * (G.energy t₀ ^ 2 / G.nu) := by linarith
  calc (∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|)
      ≤ 3 * ∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t := hmono
    _ ≤ 3 * (G.energy t₀ ^ 2 / G.nu) := this
    _ = 3 * G.energy t₀ ^ 2 / G.nu := by ring


/-! ### Reduction of the Round 105 weighted positive forcing wall -/

/-- The genuinely external part of the network forcing of a triad: what is left
of `F_τ` after the triad's own convolution terms are removed. -/
def externalTriadForcing (t : ℝ) (τ : Wave × Wave × Wave) : ℝ :=
  G.force3 τ.1 τ.2.1 τ.2.2 t - G.triadSelfForcing t τ

theorem force3_internal_external (t : ℝ) (τ : Wave × Wave × Wave) :
    G.force3 τ.1 τ.2.1 τ.2.2 t = G.triadSelfForcing t τ + G.externalTriadForcing t τ := by
  simp [externalTriadForcing]

theorem continuous_externalTriadForcing (τ : Wave × Wave × Wave) :
    Continuous fun t => G.externalTriadForcing t τ :=
  (G.continuous_force3 τ.1 τ.2.1 τ.2.2).sub (G.continuous_triadSelfForcing τ)

/-- **The Round 105 weighted positive network-forcing wall reduces to the
external cross-triad residue.**  For bounded weights `0 ≤ w_τ ≤ W`, the weighted
positive forcing expenditure over `[t₀,t₁]` is bounded by the initial energy and
the viscosity plus the integrated external residue:

  `∑_τ w_τ ∫ (F_τ)₊ ≤ W (3E(t₀)²/ν + ∫ ∑_τ |F_τ^{ext}|)`.

The first summand is paid; nothing else about the nonlinearity is used. -/
theorem weightedPositiveForcing_le_external (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (w : Wave × Wave × Wave → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hwW : ∀ τ ∈ triads G.modes, w τ ≤ W)
    (hsym : ∀ k ∈ G.modes, -k ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    weightedPositiveForcing G w t₀ t₁
      ≤ W * (3 * G.energy t₀ ^ 2 / G.nu
          + ∫ t in t₀..t₁, ∑ τ ∈ triads G.modes, |G.externalTriadForcing t τ|) := by
  classical
  set S := triads G.modes with hSdef
  have hintI : ∀ τ : Wave × Wave × Wave,
      IntervalIntegrable (fun t => |G.triadSelfForcing t τ|) volume t₀ t₁ :=
    fun τ => (continuous_abs.comp (G.continuous_triadSelfForcing τ)).intervalIntegrable _ _
  have hintE : ∀ τ : Wave × Wave × Wave,
      IntervalIntegrable (fun t => |G.externalTriadForcing t τ|) volume t₀ t₁ :=
    fun τ => (continuous_abs.comp (G.continuous_externalTriadForcing τ)).intervalIntegrable _ _
  have hcell : ∀ τ ∈ S, w τ * (∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
      ≤ W * ((∫ t in t₀..t₁, |G.triadSelfForcing t τ|)
          + ∫ t in t₀..t₁, |G.externalTriadForcing t τ|) := by
    intro τ hτ
    have hmaxint : IntervalIntegrable (fun t => max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
        volume t₀ t₁ :=
      (((G.continuous_force3 τ.1 τ.2.1 τ.2.2).max continuous_const)).intervalIntegrable _ _
    have hsumint : IntervalIntegrable
        (fun t => |G.triadSelfForcing t τ| + |G.externalTriadForcing t τ|) volume t₀ t₁ :=
      (hintI τ).add (hintE τ)
    have hIle : (∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
        ≤ ∫ t in t₀..t₁, (|G.triadSelfForcing t τ| + |G.externalTriadForcing t τ|) := by
      refine intervalIntegral.integral_mono_on ht hmaxint hsumint ?_
      intro t _
      rw [G.force3_internal_external t τ]
      calc max (G.triadSelfForcing t τ + G.externalTriadForcing t τ) 0
          ≤ |G.triadSelfForcing t τ + G.externalTriadForcing t τ| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ ≤ |G.triadSelfForcing t τ| + |G.externalTriadForcing t τ| := abs_add_le _ _
    have hI0 : 0 ≤ ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 :=
      intervalIntegral.integral_nonneg ht fun t _ => le_max_right _ _
    have hsplit : (∫ t in t₀..t₁, (|G.triadSelfForcing t τ| + |G.externalTriadForcing t τ|))
        = (∫ t in t₀..t₁, |G.triadSelfForcing t τ|)
          + ∫ t in t₀..t₁, |G.externalTriadForcing t τ| :=
      intervalIntegral.integral_add (hintI τ) (hintE τ)
    have h1 : w τ * (∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
        ≤ W * (∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0) :=
      mul_le_mul_of_nonneg_right (hwW τ hτ) hI0
    have h2 : W * (∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
        ≤ W * ∫ t in t₀..t₁, (|G.triadSelfForcing t τ| + |G.externalTriadForcing t τ|) :=
      mul_le_mul_of_nonneg_left hIle hW
    rw [hsplit] at h2
    linarith
  have hsum := Finset.sum_le_sum hcell
  have hexpand : ∑ τ ∈ S, W * ((∫ t in t₀..t₁, |G.triadSelfForcing t τ|)
        + ∫ t in t₀..t₁, |G.externalTriadForcing t τ|)
      = W * ((∑ τ ∈ S, ∫ t in t₀..t₁, |G.triadSelfForcing t τ|)
          + ∑ τ ∈ S, ∫ t in t₀..t₁, |G.externalTriadForcing t τ|) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hswapI : (∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|)
      = ∑ τ ∈ S, ∫ t in t₀..t₁, |G.triadSelfForcing t τ| :=
    intervalIntegral.integral_finset_sum fun τ _ => hintI τ
  have hswapE : (∫ t in t₀..t₁, ∑ τ ∈ S, |G.externalTriadForcing t τ|)
      = ∑ τ ∈ S, ∫ t in t₀..t₁, |G.externalTriadForcing t τ| :=
    intervalIntegral.integral_finset_sum fun τ _ => hintE τ
  have hpay : (∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|)
      ≤ 3 * G.energy t₀ ^ 2 / G.nu :=
    G.selected_triad_internal_integrated_le hnu ht S (Finset.Subset.refl _) hsym l hbel
  rw [hexpand] at hsum
  rw [← hswapI, ← hswapE] at hsum
  have hmul : W * ((∫ t in t₀..t₁, ∑ τ ∈ S, |G.triadSelfForcing t τ|)
        + ∫ t in t₀..t₁, ∑ τ ∈ S, |G.externalTriadForcing t τ|)
      ≤ W * (3 * G.energy t₀ ^ 2 / G.nu
          + ∫ t in t₀..t₁, ∑ τ ∈ S, |G.externalTriadForcing t τ|) :=
    mul_le_mul_of_nonneg_left (by linarith) hW
  have hwp : weightedPositiveForcing G w t₀ t₁
      = ∑ τ ∈ S, w τ * ∫ t in t₀..t₁, max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := rfl
  rw [hwp]
  linarith

end GalerkinFlow

end ClayNS.Waleffe
