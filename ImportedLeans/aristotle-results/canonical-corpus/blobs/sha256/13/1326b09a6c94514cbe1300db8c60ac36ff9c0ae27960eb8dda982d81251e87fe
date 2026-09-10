/-
# Paying the whole signed Gram sum of `F_s`: the spacetime remainder energy
# `R_F = ∫_t ∫_s ‖F_s‖²` is finite, cutoff-uniformly, on a Wiener input

`SignedRemainderTTStar.lean` proved the exact signed `TT*` identity

  `∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'})`,

paid its diagonal (`resDiag_le_energy_cube`) and left the *off-diagonal*
(phase-carrying) part of the signed Gram sum unpaid.  It also recorded that the
naive absolute-value route — majorize `‖F_s‖` first, integrate in `s` after —
fails, because the surviving scalar heat mass `W_s = ∑_p e^{-sν|p|²}|p|` is not
square-integrable at `s = 0`.

This file closes that gap in the only order that works: **integrate in `s`
first, majorize afterwards.**  The `s`-integration is the exact resolvent
identity, so no information is lost; the resulting denominators
`λ_p + λ_{p'} ≥ 2ν|p||p'|` are exactly what cancels the two output derivatives
carried by the relocated inner kernel (`nrm_innerForcing_le_conv`).  What
remains is a plain discrete Young convolution, with no fibre cardinality, no
shell multiplicity, no cutoff dependence and — crucially — no small-`s`
divergence.

The results:

* `herm_re_le_nrm_mul`, `two_nu_wlen_mul_le_pairRate` — Cauchy–Schwarz and the
  AM–GM lower bound `λ_p + λ_{p'} ≥ 2ν|p||p'|` for the literal viscous pair
  rates.
* `resForm_le_sq` — the *whole* signed resolvent Gram form (diagonal **and**
  off-diagonal) of any cell family is bounded by `(∑_p ‖G_p‖/|p|)² / (2ν)`.
* `integral_nsq_Fs_le_profile` — for each output `k`,
  `∫_0^∞ ‖F_s(k)‖² ds ≤ 9 (∑_p B_p ‖u_{k−p}‖)² / (2ν)` whenever the inner
  forcing obeys the relocated cell bound `‖N_p‖ ≤ 3|p| B_p`.
* `sum_integral_nsq_Fs_le_profile` — summed over the outputs by discrete Young:
  `∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 (∑_p B_p)² E / (2ν)`.
* `sum_conv_le_wienerA_sq`, `sum_integral_nsq_Fs_le_wiener` — with the literal
  physical inner forcing `N_p = ∑_{a+b=p} PureCommutator`, `B_p` is the leg-norm
  convolution and `∑_p B_p ≤ ‖u‖_A²`, giving the closed bound

    `∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 ‖u‖_A⁴ E / (2ν)`,

  with `‖u‖_A = ∑_k ‖u_k‖` the discrete Wiener-algebra norm of `WienerBudget`.
* `spacetime_remainder_le` — the spacetime form `R_F ≤ 9 M (t₁−t₀)/(2ν)` on a
  time interval on which `‖u(t)‖_A⁴ E(t) ≤ M`.

**Honest status.**  This is an unconditional, cutoff-uniform bound for the
object the resolvent/flux architecture leaves open, in terms of the Wiener norm
and the energy.  It is *not* an energy-only bound, and cannot be made one by
rearranging this argument: `WaleffeWienerSupercritical.wiener_norm_not_controlled_by_energy`
exhibits transverse fields of unit energy and arbitrarily large Wiener norm.  So
the remaining input on this route is precisely a truncation-uniform spacetime
Wiener bound `∫ ‖u‖_A⁴ E dt`, which is supercritical and is not supplied by the
energy inequality.  Package A and the literal Clay periodic target are not
closed and nothing is claimed for them.
-/
import RequestProject.NavierStokes.SignedRemainderTTStar

noncomputable section

open MeasureTheory Set

namespace ClayNS.TTStar

open ClayNS.Waleffe ClayNS.Resolvent

/-! ## 1.  Two elementary inputs -/

/-- Cauchy–Schwarz for the real part of the Hermitian form. -/
theorem herm_re_le_nrm_mul (u v : Fin 3 → ℂ) : (herm u v).re ≤ nrm u * nrm v := by
  have h1 : (herm u v).re ≤ ‖herm u v‖ := Complex.re_le_norm _
  have h2 : ‖herm u v‖ ^ 2 ≤ (nrm u * nrm v) ^ 2 := by
    have hns : Complex.normSq (herm u v) ≤ nsq u * nsq v := normSq_herm_le u v
    have hnorm : ‖herm u v‖ ^ 2 = Complex.normSq (herm u v) := Complex.sq_norm _
    rw [hnorm, mul_pow, nrm_sq, nrm_sq]
    exact hns
  have h3 : 0 ≤ nrm u * nrm v := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have h4 : ‖herm u v‖ ≤ nrm u * nrm v := by
    nlinarith [norm_nonneg (herm u v), h2, h3]
  linarith

/-- **AM–GM on the literal viscous pair rates.**  The resolvent denominator of
two cells at the same output dominates `2ν|p||p'|`: this is the factor that pays
the two output derivatives of the relocated inner kernel. -/
theorem two_nu_wlen_mul_le_pairRate {nu : ℝ} (hnu : 0 ≤ nu) (k p p' : Wave) :
    2 * nu * (wlen p * wlen p')
      ≤ viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p') := by
  have hsq : 2 * (wlen p * wlen p') ≤ wsq p + wsq p' := by
    have h := sq_nonneg (wlen p - wlen p')
    have e1 : wlen p ^ 2 = wsq p := wlen_sq p
    have e2 : wlen p' ^ 2 = wsq p' := wlen_sq p'
    nlinarith [h, e1, e2]
  have hrest : (0 : ℝ) ≤ wsq (k - p) + wsq (k - p') := by
    have := wsq_nonneg' (k - p)
    have := wsq_nonneg' (k - p')
    linarith
  rw [viscousPairRate, viscousPairRate]
  nlinarith [hsq, hrest, hnu]

/-! ## 2.  The whole signed resolvent Gram form, diagonal and off-diagonal -/

/-- A single resolvent Gram entry is bounded by the product of the
frequency-normalized cell masses. -/
theorem resTerm_le {nu : ℝ} (hnu : 0 < nu) {k p p' : Wave} (G : Wave → Fin 3 → ℂ)
    (hp : wsq p ≠ 0) (hp' : wsq p' ≠ 0) :
    (herm (G p) (G p')).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ (nrm (G p) / wlen p) * (nrm (G p') / wlen p') / (2 * nu) := by
  have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero hp
  have hlp' : 0 < wlen p' := wlen_pos_of_wsq_ne_zero hp'
  have hden0 : 0 < 2 * nu * (wlen p * wlen p') := by positivity
  have hden : 2 * nu * (wlen p * wlen p')
      ≤ viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p') :=
    two_nu_wlen_mul_le_pairRate hnu.le k p p'
  have hnum : (herm (G p) (G p')).re ≤ nrm (G p) * nrm (G p') :=
    herm_re_le_nrm_mul _ _
  have hnumnn : 0 ≤ nrm (G p) * nrm (G p') :=
    mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hpos : 0 < viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p') :=
    lt_of_lt_of_le hden0 hden
  have hstep1 : (herm (G p) (G p')).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ (nrm (G p) * nrm (G p'))
        / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')) :=
    (div_le_div_iff_of_pos_right hpos).mpr hnum
  have hstep2 : (nrm (G p) * nrm (G p'))
        / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ (nrm (G p) * nrm (G p')) / (2 * nu * (wlen p * wlen p')) :=
    div_le_div_of_nonneg_left hnumnn hden0 hden
  have heq : (nrm (G p) * nrm (G p')) / (2 * nu * (wlen p * wlen p'))
      = (nrm (G p) / wlen p) * (nrm (G p') / wlen p') / (2 * nu) := by
    field_simp
  linarith [hstep1, hstep2, heq.le, heq.ge]

/-- **The whole signed resolvent Gram form is paid.**  Both the diagonal and the
off-diagonal (phase-carrying) part of the exact `TT*` expansion are bounded by
the square of the frequency-normalized cell mass, with no cardinality anywhere. -/
theorem resForm_le_sq {nu : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (G : Wave → Fin 3 → ℂ) (k : Wave) (hp : ∀ p ∈ modes, wsq p ≠ 0) :
    ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ (∑ p ∈ modes, nrm (G p) / wlen p) ^ 2 / (2 * nu) := by
  have hmain : ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ ∑ p ∈ modes, ∑ p' ∈ modes,
          (nrm (G p) / wlen p) * (nrm (G p') / wlen p') / (2 * nu) :=
    Finset.sum_le_sum fun p hpm => Finset.sum_le_sum fun p' hp'm =>
      resTerm_le hnu G (hp p hpm) (hp p' hp'm)
  have hfac : ∑ p ∈ modes, ∑ p' ∈ modes,
        (nrm (G p) / wlen p) * (nrm (G p') / wlen p') / (2 * nu)
      = (∑ p ∈ modes, nrm (G p) / wlen p) ^ 2 / (2 * nu) := by
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
  linarith [hmain, hfac.le, hfac.ge]

/-! ## 3.  The remainder budget at one output, then summed -/

/-- The frequency-normalized outer cell mass is controlled by the profile of the
inner forcing bound: the `|p|` of the relocated inner kernel is cancelled. -/
theorem cell_ratio_le {N u : Wave → Fin 3 → ℂ} {k p : Wave} (B : Wave → ℝ)
    (hk : wsq k ≠ 0) (hp : wsq p ≠ 0)
    (hN : nrm (N p) ≤ 3 * wlen p * B p) :
    nrm (outerCellVec N u k p) / wlen p ≤ 3 * (B p * nrm (u (k - p))) := by
  have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero hp
  have h1 : nrm (outerCellVec N u k p) ≤ nrm (cross (N p) (u (k - p))) :=
    nrm_leray_le k _ hk
  have h2 : nrm (cross (N p) (u (k - p))) ≤ nrm (N p) * nrm (u (k - p)) :=
    nrm_cross_le _ _
  have hq : 0 ≤ nrm (u (k - p)) := nrm_nonneg _
  have h3 : nrm (outerCellVec N u k p) ≤ 3 * wlen p * B p * nrm (u (k - p)) := by
    nlinarith [h1, h2, hN, hq]
  rw [div_le_iff₀ hlp]
  nlinarith [h3, hlp]

/-- **The remainder budget at one output.**  The whole `s`-integral of the
squared signed remainder — diagonal and off-diagonal — is bounded by the square
of a convolution, with no heat mass and hence no small-`s` divergence. -/
theorem integral_nsq_Fs_le_profile {nu : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k : Wave) (B : Wave → ℝ)
    (hk : wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p) :
    (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2 / (2 * nu) := by
  have hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (k - p) := by
    intro p hpm
    rw [viscousPairRate]
    have h1 : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
    have h2 : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
    have : 0 < wsq p + wsq (k - p) := by linarith
    exact mul_pos hnu this
  rw [integral_nsq_Fs_eq_resForm modes N u k hrate]
  have hgram := resForm_le_sq hnu modes (fun p => outerCellVec N u k p) k hp
  have hratio : ∑ p ∈ modes, nrm (outerCellVec N u k p) / wlen p
      ≤ ∑ p ∈ modes, 3 * (B p * nrm (u (k - p))) :=
    Finset.sum_le_sum fun p hpm => cell_ratio_le B hk (hp p hpm) (hN p hpm)
  have hnn : 0 ≤ ∑ p ∈ modes, nrm (outerCellVec N u k p) / wlen p :=
    Finset.sum_nonneg fun p _ => div_nonneg (nrm_nonneg _) (wlen_nonneg p)
  have hsum3 : ∑ p ∈ modes, 3 * (B p * nrm (u (k - p)))
      = 3 * ∑ p ∈ modes, B p * nrm (u (k - p)) := by
    rw [Finset.mul_sum]
  have hsq : (∑ p ∈ modes, nrm (outerCellVec N u k p) / wlen p) ^ 2
      ≤ 9 * (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2 := by
    have h := hratio
    rw [hsum3] at h
    nlinarith [h, hnn]
  have h2nu : 0 < 2 * nu := by linarith
  calc ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (outerCellVec N u k p) (outerCellVec N u k p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ (∑ p ∈ modes, nrm (outerCellVec N u k p) / wlen p) ^ 2 / (2 * nu) := hgram
    _ ≤ 9 * (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2 / (2 * nu) :=
        (div_le_div_iff_of_pos_right h2nu).mpr hsq

/-- **The summed remainder budget.**  Discrete Young in the outer convolution
variable: no outer fibre count, no shell multiplicity, no cutoff dependence. -/
theorem sum_integral_nsq_Fs_le_profile {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (N u : Wave → Fin 3 → ℂ) (B : Wave → ℝ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hB : ∀ p, 0 ≤ B p)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * (∑ p ∈ modes, B p) ^ 2 * energy modes u / (2 * nu) := by
  classical
  have h2nu : 0 < 2 * nu := by linarith
  have hpt : ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ ∑ k ∈ outs, 9 * (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2 / (2 * nu) :=
    Finset.sum_le_sum fun k hkm =>
      integral_nsq_Fs_le_profile hnu modes N u k B (hk k hkm) hp hN
  have hyoung := sum_sq_conv_le modes outs B (fun q => nrm (u q)) hB
    (by
      intro q hq
      simp [hsupp q hq, nrm, nsq])
  have hgsum : ∑ q ∈ modes, nrm (u q) ^ 2 = energy modes u := by
    simp [energy, nrm_sq]
  have hfactor : ∑ k ∈ outs, 9 * (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2 / (2 * nu)
      = 9 * (∑ k ∈ outs, (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2) / (2 * nu) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hgsum] at hyoung
  have hfin : 9 * (∑ k ∈ outs, (∑ p ∈ modes, B p * nrm (u (k - p))) ^ 2) / (2 * nu)
      ≤ 9 * ((∑ p ∈ modes, B p) ^ 2 * energy modes u) / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    linarith [hyoung]
  have hgoal : 9 * ((∑ p ∈ modes, B p) ^ 2 * energy modes u) / (2 * nu)
      = 9 * (∑ p ∈ modes, B p) ^ 2 * energy modes u / (2 * nu) := by ring
  linarith [hpt, hfactor.le, hfactor.ge, hfin, hgoal.le, hgoal.ge]

/-! ## 4.  The literal physical inner forcing: the Wiener input -/

/-- The total mass of the leg-norm convolution over the retained modes is at
most the square of the Wiener-algebra norm. -/
theorem sum_conv_le_wienerA_sq (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ p ∈ modes, (∑ a ∈ modes, nrm (u a) * nrm (u (p - a)))
      ≤ wienerA modes u ^ 2 := by
  classical
  have hswap : ∑ p ∈ modes, (∑ a ∈ modes, nrm (u a) * nrm (u (p - a)))
      = ∑ a ∈ modes, nrm (u a) * ∑ p ∈ modes, nrm (u (p - a)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hshift : ∀ a : Wave, ∑ p ∈ modes, nrm (u (p - a)) ≤ wienerA modes u := by
    intro a
    have := sum_shift_le modes modes (fun q => nrm (u q)) (fun q => nrm_nonneg _)
      (by
        intro q hq
        simp [hsupp q hq, nrm, nsq]) a
    simpa [wienerA] using this
  rw [hswap]
  have hbd : ∑ a ∈ modes, nrm (u a) * ∑ p ∈ modes, nrm (u (p - a))
      ≤ ∑ a ∈ modes, nrm (u a) * wienerA modes u :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hshift a) (nrm_nonneg _)
  have hfin : ∑ a ∈ modes, nrm (u a) * wienerA modes u = wienerA modes u ^ 2 := by
    rw [← Finset.sum_mul]
    rw [sq]
    rfl
  linarith [hbd, hfin.le, hfin.ge]

/-- **The spacetime remainder energy is paid on a Wiener input.**  For the
literal physical carrier — inner forcing `N_p = ∑_{a+b=p}` of relocated pure
commutators, outer Leray-projected commutator with the remaining leg, heat
weights at the literal viscous pair rate — the entire heat-parameter integral of
the squared signed remainder, summed over the outputs, obeys

  `∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 ‖u‖_A⁴ E / (2ν)`,

with no cardinality, no shell count and no dependence on the truncation. -/
theorem sum_integral_nsq_Fs_le_wiener {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k))
      ≤ 9 * wienerA modes u ^ 4 * energy modes u / (2 * nu) := by
  classical
  set B : Wave → ℝ := fun p => ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) with hBdef
  have hBnn : ∀ p, 0 ≤ B p := fun p =>
    Finset.sum_nonneg fun a _ => mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hN : ∀ p ∈ modes, nrm (innerForcing modes u p) ≤ 3 * wlen p * B p := by
    intro p hpm
    exact nrm_innerForcing_le_conv modes (hp p hpm) hdiv
  have hmain := sum_integral_nsq_Fs_le_profile hnu modes outs (innerForcing modes u) u B
    hk hp hBnn hN hsupp
  have hsumB : ∑ p ∈ modes, B p ≤ wienerA modes u ^ 2 :=
    sum_conv_le_wienerA_sq modes u hsupp
  have hsumBnn : 0 ≤ ∑ p ∈ modes, B p := Finset.sum_nonneg fun p _ => hBnn p
  have hE : 0 ≤ energy modes u := energy_nonneg modes u
  have h2nu : 0 < 2 * nu := by linarith
  have hsq : (∑ p ∈ modes, B p) ^ 2 ≤ (wienerA modes u ^ 2) ^ 2 := by
    nlinarith [hsumB, hsumBnn]
  have hstep : 9 * (∑ p ∈ modes, B p) ^ 2 * energy modes u / (2 * nu)
      ≤ 9 * wienerA modes u ^ 4 * energy modes u / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    nlinarith [hsq, hE]
  linarith [hmain, hstep]

/-! ## 5.  The spacetime form -/

/-- **The spacetime remainder energy `R_F`.**  On a time interval on which the
Wiener–energy product is bounded by `M`, the spacetime remainder energy of the
signed heat-weighted remainder family is at most `9 M (t₁ − t₀)/(2ν)`.  The only
integrability hypothesis is that the spatial budget is interval-integrable in
time, which for a Galerkin flow is automatic from continuity of the flow. -/
theorem spacetime_remainder_le {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ) (t₀ t₁ M : ℝ)
    (ht : t₀ ≤ t₁)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hM : ∀ t ∈ Set.Icc t₀ t₁, wienerA modes (u t) ^ 4 * energy modes (u t) ≤ M)
    (hint : IntervalIntegrable
      (fun t => ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      volume t₀ t₁) :
    (∫ t in t₀..t₁, ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      ≤ 9 * M * (t₁ - t₀) / (2 * nu) := by
  have h2nu : 0 < 2 * nu := by linarith
  have hbound : ∀ t ∈ Set.Icc t₀ t₁,
      (∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
        ≤ 9 * M / (2 * nu) := by
    intro t htm
    have h1 := sum_integral_nsq_Fs_le_wiener hnu modes outs (u t) hk hp (hdiv t) (hsupp t)
    have h2 : 9 * wienerA modes (u t) ^ 4 * energy modes (u t) / (2 * nu)
        ≤ 9 * M / (2 * nu) := by
      refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
      have := hM t htm
      linarith
    linarith [h1, h2]
  have hconst : (∫ t in t₀..t₁, (9 * M / (2 * nu) : ℝ)) = 9 * M / (2 * nu) * (t₁ - t₀) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hmono := intervalIntegral.integral_mono_on ht hint
    (intervalIntegrable_const (c := 9 * M / (2 * nu))) hbound
  rw [hconst] at hmono
  have : 9 * M / (2 * nu) * (t₁ - t₀) = 9 * M * (t₁ - t₀) / (2 * nu) := by ring
  linarith [hmono, this.le, this.ge]

end ClayNS.TTStar
