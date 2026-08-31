/-
# The self-phase Waleffe forcing is paid by the classical energy expenditure

`WaleffeSelfForcingSign.lean` computes the self slot of the Waleffe network
forcing exactly: for a helical resonant triad `k = p + q`,

  `Re⟪f_k^{(p,q)} , u_p × u_q⟫ = (λ_q − λ_p) ‖P_k(u_p × u_q)‖²`.

This file closes the *weld* between that exact self term and the ordinary
Navier–Stokes energy budget, on the literal projected Galerkin carrier, and with
no cutoff-dependent constant:

* `nsq_leray_cross_le` — the projected cross mass obeys
  `‖P_k(u_p × u_q)‖² ≤ ‖u_p‖² ‖u_q‖²` (the Leray projection is a contraction,
  composed with the complex Lagrange identity `nsq_cross_le`);
* `abs_helical_le_wlen` — a Beltrami mode has `|λ_p| ≤ |p|`, so the helicity gap
  of a pair is at most `|p| + |q|`;
* `self_phase_ED_bound` — hence the **modal kernel bound**
  `|λ_q − λ_p| ‖P_k(u_p×u_q)‖² ≤ D_p E_q + E_p D_q`
  with `E_p = ‖u_p‖²` and `D_p = |p|² ‖u_p‖²`; the one frequency power of the
  gap is absorbed by one of the two frequency powers of the dissipation because
  the Fourier lattice is integral (`one_le_wsq`);
* `selected_pair_ED_sum` — for **any** Boolean selection `χ` of ordered pairs
  of retained modes (resonance, helicity class, shell or gap restrictions may
  all live inside `χ`),
  `∑_{(p,q)∈χ} (D_p E_q + E_p D_q) ≤ 2 (∑ E)(∑ D)`: no cardinality and no
  cutoff factor;
* `GalerkinFlow.selected_self_phase_le` — therefore the whole selected self-phase
  network is bounded by `2 E(t) 𝔇(t)` at every time;
* `GalerkinFlow.selected_self_phase_integrated_le` — and its time integral is
  paid outright by the energy identity of `WaleffeGalerkinEnergy.lean`:
  `∫_{t₀}^{t₁} ∑_{(p,q)∈χ} |λ_q − λ_p| ‖P_{K(p,q)}(u_p×u_q)‖² dt ≤ E(t₀)²/ν`,
  a bound depending only on the initial energy and the viscosity — in
  particular uniform in the Galerkin cutoff.

Nothing here is a postulate or a bookkeeping flag: every step is a proof about
the literal `GalerkinFlow` carrier of the project.  What is *not* covered is the
genuinely external cross-triad forcing (convolution pairs outside the triad);
that remains open.
-/
import RequestProject.NavierStokes.WaleffeGalerkinEnergy

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-! ## Integrality of the Fourier lattice -/

/-- A nonzero integer wavevector has `|k|² ≥ 1`. -/
theorem one_le_wsq {k : Wave} (hk : k ≠ 0) : 1 ≤ wsq k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext fun i => h i)
  have hz : (1 : ℤ) ≤ (k i) ^ 2 := by
    rcases lt_trichotomy (k i) 0 with h | h | h
    · nlinarith
    · exact absurd h hi
    · nlinarith
  have h1 : (1 : ℝ) ≤ ((k i : ℝ)) ^ 2 := by exact_mod_cast hz
  have hsum : ((k i : ℝ)) ^ 2 ≤ wsq k :=
    Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- On the integer lattice one frequency power is dominated by two. -/
theorem wlen_le_wsq {k : Wave} (hk : 1 ≤ wsq k) : wlen k ≤ wsq k := by
  have h : Real.sqrt (wsq k) ≤ Real.sqrt (wsq k ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rw [Real.sqrt_sq (by linarith)] at h
  exact h

theorem wsq_nonneg' (k : Wave) : 0 ≤ wsq k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The squared norm of a wavevector, as a complex 3-vector. -/
theorem nsq_wC (k : Wave) : nsq (wC k) = wsq k := by
  simp only [nsq, wC, wsq, Complex.normSq_apply, Complex.intCast_re, Complex.intCast_im]
  norm_num
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The projected cross mass -/

theorem nsq_const_mul (c : ℂ) (v : Fin 3 → ℂ) :
    nsq (fun i => c * v i) = Complex.normSq c * nsq v := by
  simp [nsq, Complex.normSq_mul, Finset.mul_sum]

/-- **The projected cross mass is dominated by the product of the modal
energies**: `‖P_k(u × v)‖² ≤ ‖u‖² ‖v‖²`.  Leray contraction composed with the
complex Lagrange identity. -/
theorem nsq_leray_cross_le (k : Wave) (hk : wsq k ≠ 0) (u v : Fin 3 → ℂ) :
    nsq (leray k (cross u v)) ≤ nsq u * nsq v :=
  le_trans (nsq_leray_le k (cross u v) hk) (nsq_cross_le u v)

/-! ## The helical eigenvalue is bounded by the frequency -/

/-- A Beltrami mode `i p × u_p = λ_p u_p` with `u_p ≠ 0` has `|λ_p| ≤ |p|`. -/
theorem abs_helical_le_wlen {p : Wave} {up : Fin 3 → ℂ} {lp : ℝ} (hup : nsq up ≠ 0)
    (hp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i) :
    |lp| ≤ wlen p := by
  have hpos : 0 < nsq up := lt_of_le_of_ne (nsq_nonneg up) (Ne.symm hup)
  have hval : nsq (cross (wC p) up) = lp ^ 2 * nsq up := by
    have h : (fun i => (-Complex.I) * (lp : ℂ) * up i)
        = fun i => ((-Complex.I) * (lp : ℂ)) * up i := by
      funext i; ring
    rw [hp, h, nsq_const_mul]
    congr 1
    simp [Complex.normSq_apply]
    ring
  have hle : nsq (cross (wC p) up) ≤ nsq (wC p) * nsq up := nsq_cross_le _ _
  rw [hval, nsq_wC] at hle
  have hsq : lp ^ 2 ≤ wsq p := le_of_mul_le_mul_right (by linarith) hpos
  have : |lp| ≤ Real.sqrt (wsq p) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rwa [wlen]

/-! ## The modal energy/dissipation kernel bound -/

/-- **The self-phase kernel bound.**  For a pair of nonzero (integer) modes
carrying Beltrami eigenvalues, the exact self term of the Waleffe network
forcing is bounded by the modal energy–dissipation kernel

  `|λ_q − λ_p| ‖P_k(u_p × u_q)‖² ≤ D_p E_q + E_p D_q`,

with `E_p = ‖u_p‖²`, `D_p = |p|² ‖u_p‖²`.  The single frequency power carried by
the helicity gap is absorbed by one of the two powers of the dissipation,
because on the integer lattice `|p| ≤ |p|²`. -/
theorem self_phase_ED_bound {k p q : Wave} (hk : wsq k ≠ 0) (hp : 1 ≤ wsq p) (hq : 1 ≤ wsq q)
    {up uq : Fin 3 → ℂ} {lp lq : ℝ}
    (hbp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hbq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    |lq - lp| * nsq (leray k (cross up uq))
      ≤ (wsq p * nsq up) * nsq uq + nsq up * (wsq q * nsq uq) := by
  have hEp := nsq_nonneg up
  have hEq := nsq_nonneg uq
  have hmass : nsq (leray k (cross up uq)) ≤ nsq up * nsq uq := nsq_leray_cross_le k hk up uq
  have hmass0 : 0 ≤ nsq (leray k (cross up uq)) := nsq_nonneg _
  rcases eq_or_ne (nsq up) 0 with hup | hup
  · have : nsq (leray k (cross up uq)) = 0 := le_antisymm (by rw [hup] at hmass; linarith) hmass0
    rw [this, hup]
    simp
  rcases eq_or_ne (nsq uq) 0 with huq | huq
  · have : nsq (leray k (cross up uq)) = 0 := le_antisymm (by rw [huq] at hmass; linarith) hmass0
    rw [this, huq]
    simp
  have hlp : |lp| ≤ wlen p := abs_helical_le_wlen hup hbp
  have hlq : |lq| ≤ wlen q := abs_helical_le_wlen huq hbq
  have hgap : |lq - lp| ≤ wsq p + wsq q := by
    have h1 : |lq - lp| ≤ |lq| + |lp| := abs_sub _ _
    have h2 := wlen_le_wsq hp
    have h3 := wlen_le_wsq hq
    linarith
  have hgap0 : 0 ≤ |lq - lp| := abs_nonneg _
  have hchain : |lq - lp| * nsq (leray k (cross up uq)) ≤ (wsq p + wsq q) * (nsq up * nsq uq) := by
    calc |lq - lp| * nsq (leray k (cross up uq))
        ≤ |lq - lp| * (nsq up * nsq uq) := by
          exact mul_le_mul_of_nonneg_left hmass hgap0
      _ ≤ (wsq p + wsq q) * (nsq up * nsq uq) := by
          exact mul_le_mul_of_nonneg_right hgap (by positivity)
  nlinarith [hchain]

/-- **The literal self slot of the Waleffe network forcing obeys the modal
energy–dissipation kernel bound.**  Combining the exact self-forcing law
`pair_self_forcing_signed_square` with `self_phase_ED_bound`:
`|Re⟪f_k^{(p,q)}, u_p × u_q⟫| ≤ D_p E_q + E_p D_q`. -/
theorem abs_pair_self_forcing_le_ED {p q k : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hp : 1 ≤ wsq p) (hq : 1 ≤ wsq q) {up uq : Fin 3 → ℂ} {lp lq : ℝ}
    (hbp : cross (wC p) up = fun i => (-Complex.I) * (lp : ℂ) * up i)
    (hbq : cross (wC q) uq = fun i => (-Complex.I) * (lq : ℂ) * uq i) :
    |(herm (fun i => -(leray k (pairAdvection p q up uq) i)) (cross up uq)).re|
      ≤ (wsq p * nsq up) * nsq uq + nsq up * (wsq q * nsq uq) := by
  rw [pair_self_forcing_signed_square hpq hk up uq lp lq hbp hbq, abs_mul,
    abs_of_nonneg (nsq_nonneg (leray k (cross up uq)))]
  exact self_phase_ED_bound hk hp hq hbp hbq

/-! ## Summing an arbitrary selection of ordered pairs -/

/-- **The selected-pair energy–dissipation summation.**  For any Boolean
selection `χ` of ordered pairs of retained modes,

  `∑_{(p,q)∈χ} (D_p E_q + E_p D_q) ≤ 2 (∑ E)(∑ D)`.

No cardinality, resonance count or cutoff factor enters: the selection may be
arbitrary. -/
theorem selected_pair_ED_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (chi : Finset (ι × ι))
    (hsub : chi ⊆ s ×ˢ s) (E D : ι → ℝ) (hE : ∀ i ∈ s, 0 ≤ E i) (hD : ∀ i ∈ s, 0 ≤ D i) :
    ∑ x ∈ chi, (D x.1 * E x.2 + E x.1 * D x.2) ≤ 2 * (∑ i ∈ s, E i) * (∑ i ∈ s, D i) := by
  have hnn : ∀ x ∈ s ×ˢ s, 0 ≤ D x.1 * E x.2 + E x.1 * D x.2 := by
    intro x hx
    rw [Finset.mem_product] at hx
    have := mul_nonneg (hD x.1 hx.1) (hE x.2 hx.2)
    have := mul_nonneg (hE x.1 hx.1) (hD x.2 hx.2)
    linarith
  have hstep : ∑ x ∈ chi, (D x.1 * E x.2 + E x.1 * D x.2)
      ≤ ∑ x ∈ s ×ˢ s, (D x.1 * E x.2 + E x.1 * D x.2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hnn x hx
  have hprod : ∑ x ∈ s ×ˢ s, (D x.1 * E x.2 + E x.1 * D x.2)
      = 2 * (∑ i ∈ s, E i) * (∑ i ∈ s, D i) := by
    rw [Finset.sum_product]
    have : ∀ p ∈ s, ∑ q ∈ s, (D p * E q + E p * D q)
        = D p * (∑ q ∈ s, E q) + E p * (∑ q ∈ s, D q) := by
      intro p _
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  linarith

/-! ## The payment on a Galerkin flow -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- Every retained mode of a Galerkin flow is a nonzero lattice point, hence has
`|k|² ≥ 1`. -/
theorem one_le_wsq_of_mem {k : Wave} (hk : k ∈ G.modes) : 1 ≤ wsq k :=
  one_le_wsq (by rintro rfl; exact G.zero_not_mem hk)

theorem wsq_ne_zero_of_mem {k : Wave} (hk : k ∈ G.modes) : wsq k ≠ 0 := by
  have := G.one_le_wsq_of_mem hk
  linarith

/-- **The selected self-phase network is bounded by `2 E 𝔇` at every time.**
`χ` is an arbitrary selection of ordered pairs of retained modes, `K` assigns to
each selected pair the mode it forces (any assignment with a nonzero output
frequency), and `l` is the helical eigenvalue label of the flow. -/
theorem selected_self_phase_le (t : ℝ) (chi : Finset (Wave × Wave))
    (hchi : chi ⊆ G.modes ×ˢ G.modes) (K : Wave × Wave → Wave)
    (hK : ∀ x ∈ chi, wsq (K x) ≠ 0) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    ∑ x ∈ chi, |l x.2 - l x.1| * nsq (leray (K x) (cross (G.u t x.1) (G.u t x.2)))
      ≤ 2 * G.energy t * G.dissipation t := by
  classical
  set E : Wave → ℝ := fun p => nsq (G.u t p) with hEdef
  set D : Wave → ℝ := fun p => wsq p * nsq (G.u t p) with hDdef
  have hterm : ∀ x ∈ chi,
      |l x.2 - l x.1| * nsq (leray (K x) (cross (G.u t x.1) (G.u t x.2)))
        ≤ D x.1 * E x.2 + E x.1 * D x.2 := by
    intro x hx
    have hmem := Finset.mem_product.mp (hchi hx)
    exact self_phase_ED_bound (hK x hx) (G.one_le_wsq_of_mem hmem.1) (G.one_le_wsq_of_mem hmem.2)
      (hbel x.1 hmem.1) (hbel x.2 hmem.2)
  have hsum := Finset.sum_le_sum hterm
  have hED := selected_pair_ED_sum G.modes chi hchi E D
    (fun i _ => nsq_nonneg _) (fun i _ => mul_nonneg (wsq_nonneg' i) (nsq_nonneg _))
  have hE : ∑ i ∈ G.modes, E i = G.energy t := rfl
  have hD : ∑ i ∈ G.modes, D i = G.dissipation t := rfl
  rw [hE, hD] at hED
  linarith

/-! ### Continuity of the selected self-phase network -/

theorem continuous_leray_of {v : ℝ → Fin 3 → ℂ} (hv : ∀ i, Continuous fun t => v t i)
    (k : Wave) (i : Fin 3) : Continuous fun t => leray k (v t) i := by
  show Continuous fun t => v t i - (herm (wC k) (v t) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ)
  have hherm : Continuous fun t => herm (wC k) (v t) :=
    continuous_herm_of (f := fun _ => wC k) (fun _ => continuous_const) hv
  exact (hv i).sub ((hherm.div_const _).mul continuous_const)

theorem continuous_nsq_of {v : ℝ → Fin 3 → ℂ} (hv : ∀ i, Continuous fun t => v t i) :
    Continuous fun t => nsq (v t) :=
  continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (hv i)

theorem continuous_selected_self_phase (chi : Finset (Wave × Wave)) (K : Wave × Wave → Wave)
    (l : Wave → ℝ) :
    Continuous fun t =>
      ∑ x ∈ chi, |l x.2 - l x.1| * nsq (leray (K x) (cross (G.u t x.1) (G.u t x.2))) := by
  refine continuous_finset_sum _ fun x _ => continuous_const.mul ?_
  exact continuous_nsq_of
    (continuous_leray_of (continuous_cross_of (G.continuous_u x.1) (G.continuous_u x.2)) (K x))

/-- The energy–dissipation product is paid by the initial energy: for `t₀ ≤ t₁`,
`∫ 2 E 𝔇 ≤ E(t₀)²/ν`. -/
theorem integral_energy_dissipation_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) :
    (∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t) ≤ G.energy t₀ ^ 2 / G.nu := by
  have hcont : Continuous fun t => 2 * G.energy t * G.dissipation t :=
    (continuous_const.mul G.continuous_energy).mul G.continuous_dissipation
  have hcont' : Continuous fun t => 2 * G.energy t₀ * G.dissipation t :=
    continuous_const.mul G.continuous_dissipation
  have hmono : (∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t)
      ≤ ∫ t in t₀..t₁, 2 * G.energy t₀ * G.dissipation t := by
    refine intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable _ _)
      (hcont'.intervalIntegrable _ _) ?_
    intro t hts
    have hE : G.energy t ≤ G.energy t₀ := G.energy_le_initial hts.1
    have hD : 0 ≤ G.dissipation t := G.dissipation_nonneg t
    nlinarith
  have hpull : (∫ t in t₀..t₁, 2 * G.energy t₀ * G.dissipation t)
      = 2 * G.energy t₀ * ∫ t in t₀..t₁, G.dissipation t := by
    rw [intervalIntegral.integral_const_mul]
  have hdiss := G.integral_dissipation_le t₀ t₁ hnu
  have hE0 : 0 ≤ G.energy t₀ := G.energy_nonneg t₀
  have hbound : 2 * G.energy t₀ * (∫ t in t₀..t₁, G.dissipation t)
      ≤ 2 * G.energy t₀ * (G.energy t₀ / (2 * G.nu)) := by
    exact mul_le_mul_of_nonneg_left hdiss (by linarith)
  have hval : 2 * G.energy t₀ * (G.energy t₀ / (2 * G.nu)) = G.energy t₀ ^ 2 / G.nu := by
    field_simp
  rw [hpull] at hmono
  linarith [hval ▸ hbound]

/-- **The self-phase Waleffe forcing is paid outright by the classical energy
expenditure.**  For an arbitrary selection `χ` of ordered pairs of retained
modes, an arbitrary forced-mode assignment `K` with nonzero output frequency,
and a time-independent helical labelling `l` of the flow,

  `∫_{t₀}^{t₁} ∑_{(p,q)∈χ} |λ_q − λ_p| ‖P_{K(p,q)}(u_p × u_q)‖² dt ≤ E(t₀)²/ν`.

The right-hand side involves only the initial energy and the viscosity: it is
uniform in the Galerkin cutoff, in the cardinality of the selection and in the
frequency range. -/
theorem selected_self_phase_integrated_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (chi : Finset (Wave × Wave)) (hchi : chi ⊆ G.modes ×ˢ G.modes) (K : Wave × Wave → Wave)
    (hK : ∀ x ∈ chi, wsq (K x) ≠ 0) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    (∫ t in t₀..t₁,
        ∑ x ∈ chi, |l x.2 - l x.1| * nsq (leray (K x) (cross (G.u t x.1) (G.u t x.2))))
      ≤ G.energy t₀ ^ 2 / G.nu := by
  have hcont := G.continuous_selected_self_phase chi K l
  have hcont2 : Continuous fun t => 2 * G.energy t * G.dissipation t :=
    (continuous_const.mul G.continuous_energy).mul G.continuous_dissipation
  have hmono : (∫ t in t₀..t₁,
      ∑ x ∈ chi, |l x.2 - l x.1| * nsq (leray (K x) (cross (G.u t x.1) (G.u t x.2))))
      ≤ ∫ t in t₀..t₁, 2 * G.energy t * G.dissipation t := by
    refine intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) ?_
    intro t _
    exact G.selected_self_phase_le t chi hchi K hK l (hbel t)
  exact le_trans hmono (G.integral_energy_dissipation_le hnu ht)

/-! ### The literal triad self-forcing form -/

/-- The selected self-phase sum written with the **literal** self slot of the
Waleffe network forcing, `Re⟪f_{p+q}^{(p,q)}, u_p × u_q⟫`. -/
theorem selected_triad_self_forcing_eq (t : ℝ) (chi : Finset (Wave × Wave))
    (hchi : chi ⊆ G.modes ×ˢ G.modes) (hK : ∀ x ∈ chi, wsq (x.1 + x.2) ≠ 0) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    ∑ x ∈ chi, |(herm (fun i => -(leray (x.1 + x.2)
        (pairAdvection x.1 x.2 (G.u t x.1) (G.u t x.2)) i))
          (cross (G.u t x.1) (G.u t x.2))).re|
      = ∑ x ∈ chi, |l x.2 - l x.1| *
          nsq (leray (x.1 + x.2) (cross (G.u t x.1) (G.u t x.2))) := by
  refine Finset.sum_congr rfl fun x hx => ?_
  have hmem := Finset.mem_product.mp (hchi hx)
  rw [pair_self_forcing_signed_square rfl (hK x hx) (G.u t x.1) (G.u t x.2) (l x.1) (l x.2)
    (hbel x.1 hmem.1) (hbel x.2 hmem.2), abs_mul,
    abs_of_nonneg (nsq_nonneg (leray (x.1 + x.2) (cross (G.u t x.1) (G.u t x.2))))]

/-- **The literal selected triad self-forcing is bounded by `2 E 𝔇`.** -/
theorem selected_triad_self_forcing_le (t : ℝ) (chi : Finset (Wave × Wave))
    (hchi : chi ⊆ G.modes ×ˢ G.modes) (hK : ∀ x ∈ chi, wsq (x.1 + x.2) ≠ 0) (l : Wave → ℝ)
    (hbel : ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    ∑ x ∈ chi, |(herm (fun i => -(leray (x.1 + x.2)
        (pairAdvection x.1 x.2 (G.u t x.1) (G.u t x.2)) i))
          (cross (G.u t x.1) (G.u t x.2))).re|
      ≤ 2 * G.energy t * G.dissipation t := by
  rw [G.selected_triad_self_forcing_eq t chi hchi hK l hbel]
  exact G.selected_self_phase_le t chi hchi (fun x => x.1 + x.2) hK l hbel

/-- **The literal selected triad self-forcing expenditure is paid by the initial
energy**: `∫ ∑_{(p,q)∈χ} |Re⟪f_{p+q}^{(p,q)}, u_p×u_q⟫| dt ≤ E(t₀)²/ν`, uniformly
in the Galerkin cutoff. -/
theorem selected_triad_self_forcing_integrated_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (chi : Finset (Wave × Wave)) (hchi : chi ⊆ G.modes ×ˢ G.modes)
    (hK : ∀ x ∈ chi, wsq (x.1 + x.2) ≠ 0) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ p ∈ G.modes,
      cross (wC p) (G.u t p) = fun i => (-Complex.I) * (l p : ℂ) * G.u t p i) :
    (∫ t in t₀..t₁, ∑ x ∈ chi, |(herm (fun i => -(leray (x.1 + x.2)
        (pairAdvection x.1 x.2 (G.u t x.1) (G.u t x.2)) i))
          (cross (G.u t x.1) (G.u t x.2))).re|)
      ≤ G.energy t₀ ^ 2 / G.nu := by
  have hfun : (fun t => ∑ x ∈ chi, |(herm (fun i => -(leray (x.1 + x.2)
      (pairAdvection x.1 x.2 (G.u t x.1) (G.u t x.2)) i))
        (cross (G.u t x.1) (G.u t x.2))).re|)
      = fun t => ∑ x ∈ chi, |l x.2 - l x.1| *
          nsq (leray (x.1 + x.2) (cross (G.u t x.1) (G.u t x.2))) := by
    funext t
    exact G.selected_triad_self_forcing_eq t chi hchi hK l (hbel t)
  rw [hfun]
  exact G.selected_self_phase_integrated_le hnu ht chi hchi (fun x => x.1 + x.2) hK l hbel

end GalerkinFlow

end ClayNS.Waleffe
