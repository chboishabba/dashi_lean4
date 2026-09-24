/-
# The critical (`H^{1/2}`) energy balance of the Galerkin flow, and the barrier it
# would give

The estimates of `LatticeRieszConvolution.lean` are instantaneous.  This file
puts them inside the actual dynamics of the truncated Navier–Stokes system, so
that the remaining obligation becomes a single time integral.

* `GalerkinFlow.critEnergy` — `E₁₂(t) = ∑_k |k| ‖u_k(t)‖²`, the `H^{1/2}` energy;
* `GalerkinFlow.critEnergy_hasDerivAt` — the exact critical energy identity
  `E₁₂'(t) = −2ν D₁₂(t) + 2 P_crit(t)` on the literal Galerkin ODE, where
  `D₁₂ = ∑_k |k|³‖u_k‖²` and `P_crit = ∑_k |k| Re⟪u_k, f_k⟫`;
* `GalerkinFlow.critEnergy_balance` — its integrated form;
* `GalerkinFlow.critEnergy_differential_barrier` — the pointwise consequence of
  the cutoff-uniform absorption: `E₁₂' ≤ −ν D₁₂ + (4000/ν)·(enstrophy)²`;
* `GalerkinFlow.critEnergy_barrier_of_companion_budget` — **the conditional
  closure**: if the time-integrated companion `∫ (enstrophy)²` is bounded by `B`
  on `[t₀,t₁]`, then

    `E₁₂(t₁) + ν ∫ D₁₂ ≤ E₁₂(t₀) + (4000/ν)·B`,

  with a constant depending only on `ν` — in particular uniformly in the
  Galerkin cutoff, since every constant in the chain is absolute.

This isolates exactly what is missing.  Everything on the left of the last
statement is the `H^{1/2}` barrier the Clay target needs; the only unproved input
is a cutoff-uniform bound for `∫₀^T (enstrophy)² dt`, which the energy inequality
does **not** supply (it gives `∫ (enstrophy) ≤ E₀/ν`, one power short).  No claim
is made here that such a bound exists.
-/
import RequestProject.NavierStokes.LatticeRieszConvolution
import RequestProject.NavierStokes.WaleffeGalerkinEnergy
import RequestProject.NavierStokes.WaleffeSerrinReduction

noncomputable section

open Finset

namespace ClayNS.Waleffe

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The critical (`H^{1/2}`) energy of a Galerkin flow. -/
def critEnergy (t : ℝ) : ℝ := ∑ k ∈ G.modes, wlen k * nsq (G.u t k)

/-- The enstrophy in the form used by the companion bound. -/
def enstrophy (t : ℝ) : ℝ := ∑ a ∈ G.modes, (wlen a) ^ 2 * nsq (G.u t a)

theorem critEnergy_nonneg (t : ℝ) : 0 ≤ G.critEnergy t :=
  Finset.sum_nonneg fun k _ => mul_nonneg (wlen_nonneg' k) (nsq_nonneg _)

theorem enstrophy_nonneg (t : ℝ) : 0 ≤ G.enstrophy t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (nsq_nonneg _)

/-- **The critical energy identity.**  On the literal truncated system,
`d/dt ∑_k |k| ‖u_k‖² = −2ν ∑_k |k|³‖u_k‖² + 2 ∑_k |k| Re⟪u_k, f_k⟫`. -/
theorem critEnergy_hasDerivAt (t : ℝ) :
    HasDerivAt G.critEnergy (-2 * G.nu * G.critDiss t + 2 * G.critProd t) t := by
  have hterm : ∀ k ∈ G.modes,
      HasDerivAt (fun s => wlen k * nsq (G.u s k))
        (-2 * G.nu * (wlen k ^ 3 * nsq (G.u t k))
          + 2 * (wlen k * (herm (G.u t k) (G.force t k)).re)) t := by
    intro k hk
    have hd := nsq_hasDerivAt (fun s => G.u s k)
      (fun i => -((G.nu * wsq k : ℝ) : ℂ) * G.u t k i + G.force t k i) t
      (fun i => G.ode t k hk i)
    have hsplit : herm (G.u t k)
        (fun i => -((G.nu * wsq k : ℝ) : ℂ) * G.u t k i + G.force t k i)
        = -((G.nu * wsq k : ℝ) : ℂ) * (nsq (G.u t k) : ℂ) + herm (G.u t k) (G.force t k) := by
      rw [herm_add_right, herm_smul_right, herm_self]
    rw [hsplit] at hd
    have hre : (-((G.nu * wsq k : ℝ) : ℂ) * (nsq (G.u t k) : ℂ)
        + herm (G.u t k) (G.force t k)).re
        = -(G.nu * wsq k) * nsq (G.u t k) + (herm (G.u t k) (G.force t k)).re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hre] at hd
    have hscaled := hd.const_mul (wlen k)
    have hcube : wlen k * wsq k = wlen k ^ 3 := by
      rw [← wlen_sq k]; ring
    convert hscaled using 1
    rw [← hcube]
    ring
  have hsum : HasDerivAt G.critEnergy
      (∑ k ∈ G.modes, (-2 * G.nu * (wlen k ^ 3 * nsq (G.u t k))
        + 2 * (wlen k * (herm (G.u t k) (G.force t k)).re))) t := by
    have h := HasDerivAt.sum hterm
    have hfun : (∑ k ∈ G.modes, fun s => wlen k * nsq (G.u s k)) = G.critEnergy := by
      funext s; simp [critEnergy, Finset.sum_apply]
    rwa [hfun] at h
  have hsplit : ∑ k ∈ G.modes, (-2 * G.nu * (wlen k ^ 3 * nsq (G.u t k))
        + 2 * (wlen k * (herm (G.u t k) (G.force t k)).re))
      = -2 * G.nu * G.critDiss t + 2 * G.critProd t := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [critDiss, critDissipation, Finset.mul_sum]
    · rw [critProd, critProduction, Finset.mul_sum]
  rwa [hsplit] at hsum

theorem continuous_critEnergy : Continuous G.critEnergy :=
  continuous_finset_sum _ fun k _ => continuous_const.mul (G.continuous_nsq_u k)

theorem continuous_critDiss : Continuous (fun t => G.critDiss t) :=
  continuous_finset_sum _ fun k _ => continuous_const.mul (G.continuous_nsq_u k)

theorem continuous_enstrophy : Continuous G.enstrophy :=
  continuous_finset_sum _ fun k _ => continuous_const.mul (G.continuous_nsq_u k)

theorem continuous_critProd : Continuous (fun t => G.critProd t) := by
  refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
  exact Complex.continuous_re.comp
    (continuous_herm_of (fun i => G.continuous_u k i) (fun i => G.continuous_force k i))

/-- The integrated critical energy balance of the truncated system. -/
theorem critEnergy_balance (t₀ t₁ : ℝ) :
    G.critEnergy t₁ + 2 * G.nu * ∫ t in t₀..t₁, G.critDiss t
      = G.critEnergy t₀ + 2 * ∫ t in t₀..t₁, G.critProd t := by
  have hderiv : ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivAt G.critEnergy (-2 * G.nu * G.critDiss t + 2 * G.critProd t) t :=
    fun t _ => G.critEnergy_hasDerivAt t
  have hint : IntervalIntegrable (fun t => -2 * G.nu * G.critDiss t + 2 * G.critProd t)
      MeasureTheory.volume t₀ t₁ :=
    (((continuous_const.mul G.continuous_critDiss).add
      (continuous_const.mul G.continuous_critProd)).intervalIntegrable _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsplit : (∫ t in t₀..t₁, (-2 * G.nu * G.critDiss t + 2 * G.critProd t))
      = -2 * G.nu * (∫ t in t₀..t₁, G.critDiss t) + 2 * ∫ t in t₀..t₁, G.critProd t := by
    have h1 : IntervalIntegrable (fun t => -2 * G.nu * G.critDiss t)
        MeasureTheory.volume t₀ t₁ :=
      (continuous_const.mul G.continuous_critDiss).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t => 2 * G.critProd t) MeasureTheory.volume t₀ t₁ :=
      (continuous_const.mul G.continuous_critProd).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hftc
  linarith

/-- **The critical differential barrier.**  The cutoff-uniform absorption turns
the critical energy identity into a differential inequality whose only
uncontrolled term is the square of the enstrophy. -/
theorem critEnergy_differential_barrier (t : ℝ) (hnu : 0 < G.nu) :
    2 * G.critProd t ≤ G.nu * G.critDiss t + (4000 / G.nu) * (G.enstrophy t) ^ 2 := by
  have habs := G.abs_critProd_le_enstrophy_absorption t (theta := G.nu / 2) (by linarith)
  have hnrm : ∀ a : Wave, nrm (G.u t a) ^ 2 = nsq (G.u t a) := fun a => nrm_sq _
  have henst : (∑ a ∈ G.modes, (wlen a) ^ 2 * nrm (G.u t a) ^ 2) = G.enstrophy t := by
    rw [enstrophy]
    exact Finset.sum_congr rfl fun a _ => by rw [hnrm a]
  rw [henst] at habs
  have hle : G.critProd t ≤ |G.critProd t| := le_abs_self _
  have hcoef : (1 / (G.nu / 2)) * (1000 * (G.enstrophy t) ^ 2)
      = (2000 / G.nu) * (G.enstrophy t) ^ 2 := by
    field_simp
    ring
  rw [hcoef] at habs
  have hhalf : G.nu / 2 * G.critDiss t = (G.nu * G.critDiss t) / 2 := by ring
  rw [hhalf] at habs
  have hfin : (4000 / G.nu) * (G.enstrophy t) ^ 2
      = 2 * ((2000 / G.nu) * (G.enstrophy t) ^ 2) := by ring
  rw [hfin]
  linarith [hle, habs]

/-- **The conditional critical barrier.**  Given a bound `B` for the
time-integrated companion `∫ (enstrophy)²`, the critical energy and the critical
dissipation are controlled by the initial critical energy and `B`, with a
constant depending only on the viscosity — hence uniformly in the Galerkin
cutoff, every constant in the chain being absolute.

The hypothesis is exactly the remaining obligation; it is not proved here. -/
theorem critEnergy_barrier_of_companion_budget {t₀ t₁ B : ℝ} (ht : t₀ ≤ t₁) (hnu : 0 < G.nu)
    (hB : (∫ t in t₀..t₁, (G.enstrophy t) ^ 2) ≤ B) :
    G.critEnergy t₁ + G.nu * ∫ t in t₀..t₁, G.critDiss t
      ≤ G.critEnergy t₀ + (4000 / G.nu) * B := by
  have hbal := G.critEnergy_balance t₀ t₁
  have hintP : IntervalIntegrable (fun t => 2 * G.critProd t) MeasureTheory.volume t₀ t₁ :=
    ((continuous_const.mul G.continuous_critProd).intervalIntegrable _ _)
  have hintR : IntervalIntegrable
      (fun t => G.nu * G.critDiss t + (4000 / G.nu) * (G.enstrophy t) ^ 2)
      MeasureTheory.volume t₀ t₁ :=
    (((continuous_const.mul G.continuous_critDiss).add
      (continuous_const.mul (G.continuous_enstrophy.pow 2))).intervalIntegrable _ _)
  have hmono : (∫ t in t₀..t₁, 2 * G.critProd t)
      ≤ ∫ t in t₀..t₁, (G.nu * G.critDiss t + (4000 / G.nu) * (G.enstrophy t) ^ 2) :=
    intervalIntegral.integral_mono_on ht hintP hintR
      (fun t _ => G.critEnergy_differential_barrier t hnu)
  have hsplitR : (∫ t in t₀..t₁, (G.nu * G.critDiss t + (4000 / G.nu) * (G.enstrophy t) ^ 2))
      = G.nu * (∫ t in t₀..t₁, G.critDiss t)
        + (4000 / G.nu) * ∫ t in t₀..t₁, (G.enstrophy t) ^ 2 := by
    have h1 : IntervalIntegrable (fun t => G.nu * G.critDiss t) MeasureTheory.volume t₀ t₁ :=
      (continuous_const.mul G.continuous_critDiss).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t => (4000 / G.nu) * (G.enstrophy t) ^ 2)
        MeasureTheory.volume t₀ t₁ :=
      (continuous_const.mul (G.continuous_enstrophy.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hsplitP : (∫ t in t₀..t₁, 2 * G.critProd t) = 2 * ∫ t in t₀..t₁, G.critProd t :=
    intervalIntegral.integral_const_mul _ _
  rw [hsplitP, hsplitR] at hmono
  have hcoef : 0 < 4000 / G.nu := by positivity
  nlinarith [hbal, hmono, hB, hcoef]

/-! ## The unconditional small-critical-energy barrier -/

/-- Interpolation: the enstrophy squared is dominated by the critical energy
times the critical dissipation. -/
theorem enstrophy_sq_le_critEnergy_mul_critDiss (t : ℝ) :
    (G.enstrophy t) ^ 2 ≤ G.critEnergy t * G.critDiss t := by
  classical
  set f : Wave → ℝ := fun k => Real.sqrt (wlen k * nsq (G.u t k)) with hf
  set g : Wave → ℝ := fun k => Real.sqrt (wlen k ^ 3 * nsq (G.u t k)) with hg
  have hfg : ∀ k ∈ G.modes, f k * g k = (wlen k) ^ 2 * nsq (G.u t k) := by
    intro k _
    have h1 : 0 ≤ wlen k * nsq (G.u t k) := mul_nonneg (wlen_nonneg' k) (nsq_nonneg _)
    have hval : wlen k * nsq (G.u t k) * (wlen k ^ 3 * nsq (G.u t k))
        = ((wlen k) ^ 2 * nsq (G.u t k)) ^ 2 := by ring
    rw [hf, hg, ← Real.sqrt_mul h1, hval,
      Real.sqrt_sq (mul_nonneg (sq_nonneg _) (nsq_nonneg _))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq G.modes f g
  have hfsq : ∑ k ∈ G.modes, f k ^ 2 = G.critEnergy t := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    exact Real.sq_sqrt (mul_nonneg (wlen_nonneg' k) (nsq_nonneg _))
  have hgsq : ∑ k ∈ G.modes, g k ^ 2 = G.critDiss t := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg]
    exact Real.sq_sqrt (mul_nonneg (pow_nonneg (wlen_nonneg' k) 3) (nsq_nonneg _))
  have hleft : ∑ k ∈ G.modes, f k * g k = G.enstrophy t := by
    rw [enstrophy]
    exact Finset.sum_congr rfl hfg
  rw [hleft, hfsq, hgsq] at hcs
  exact hcs

/-- **The critical trilinear bound on the physical carrier.**
`|P_crit| ≤ 64 · √E₁₂ · D₁₂`, with an absolute constant and no cutoff dependence. -/
theorem abs_critProd_le_sqrt_critEnergy_mul_critDiss (t : ℝ) :
    |G.critProd t| ≤ 64 * Real.sqrt (G.critEnergy t) * G.critDiss t := by
  classical
  set E : Wave → ℝ := fun a => nrm (G.u t a) with hE
  have hE0 : ∀ a, 0 ≤ E a := fun a => nrm_nonneg _
  have hEsupp : ∀ a, a ∉ G.modes → E a = 0 := fun a ha => G.nrm_u_support t ha
  have hS : ∀ a ∈ G.modes, a ≠ 0 := by
    intro a ha h0
    exact G.wsq_ne_zero_of_mem ha (by rw [h0]; simp [wsq])
  have hgain : ∀ k ∈ G.modes, nrm (G.force t k) ≤ wlen k * cellMajorant G.modes E k :=
    fun k hk => G.nrm_force_le_output_gain t (G.wsq_ne_zero_of_mem hk)
  have hcs : |G.critProd t|
      ≤ Real.sqrt (G.critDiss t) * Real.sqrt (cellCompanion G.modes G.modes E) :=
    abs_critProduction_le_cellCompanion hE0 (fun k hk => G.wsq_ne_zero_of_mem hk) hgain
  have henst : (∑ a ∈ G.modes, (wlen a) ^ 2 * (E a) ^ 2) = G.enstrophy t := by
    rw [enstrophy]
    exact Finset.sum_congr rfl fun a _ => by rw [hE]; rw [nrm_sq]
  have hcomp : cellCompanion G.modes G.modes E ≤ 4000 * (G.enstrophy t) ^ 2 := by
    have h := cellCompanion_le_enstrophy_sq (S := G.modes) (T := G.modes) (E := E) hEsupp hS hS
    rwa [henst] at h
  have hinterp : (G.enstrophy t) ^ 2 ≤ G.critEnergy t * G.critDiss t :=
    G.enstrophy_sq_le_critEnergy_mul_critDiss t
  have hD0 : 0 ≤ G.critDiss t := critDissipation_nonneg _ _
  have hE12 : 0 ≤ G.critEnergy t := G.critEnergy_nonneg t
  have hchain : cellCompanion G.modes G.modes E ≤ 4096 * (G.critEnergy t * G.critDiss t) := by
    nlinarith [hcomp, hinterp, G.enstrophy_nonneg t]
  have hsqrt : Real.sqrt (cellCompanion G.modes G.modes E)
      ≤ 64 * (Real.sqrt (G.critEnergy t) * Real.sqrt (G.critDiss t)) := by
    have h1 : Real.sqrt (cellCompanion G.modes G.modes E)
        ≤ Real.sqrt (4096 * (G.critEnergy t * G.critDiss t)) := Real.sqrt_le_sqrt hchain
    have h2 : Real.sqrt (4096 * (G.critEnergy t * G.critDiss t))
        = 64 * (Real.sqrt (G.critEnergy t) * Real.sqrt (G.critDiss t)) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hE12]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hfin : Real.sqrt (G.critDiss t) * (64 * (Real.sqrt (G.critEnergy t)
      * Real.sqrt (G.critDiss t))) = 64 * Real.sqrt (G.critEnergy t) * G.critDiss t := by
    have hsq : Real.sqrt (G.critDiss t) * Real.sqrt (G.critDiss t) = G.critDiss t :=
      Real.mul_self_sqrt hD0
    calc Real.sqrt (G.critDiss t) * (64 * (Real.sqrt (G.critEnergy t)
          * Real.sqrt (G.critDiss t)))
        = 64 * Real.sqrt (G.critEnergy t)
            * (Real.sqrt (G.critDiss t) * Real.sqrt (G.critDiss t)) := by ring
      _ = 64 * Real.sqrt (G.critEnergy t) * G.critDiss t := by rw [hsq]
  calc |G.critProd t|
      ≤ Real.sqrt (G.critDiss t) * Real.sqrt (cellCompanion G.modes G.modes E) := hcs
    _ ≤ Real.sqrt (G.critDiss t) * (64 * (Real.sqrt (G.critEnergy t)
          * Real.sqrt (G.critDiss t))) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
    _ = 64 * Real.sqrt (G.critEnergy t) * G.critDiss t := hfin

/-- Below the critical threshold the production is paid outright by half the
viscous term. -/
theorem two_critProd_le_of_small (t : ℝ) (hnu : 0 < G.nu)
    (hsmall : G.critEnergy t ≤ (G.nu / 128) ^ 2) :
    2 * G.critProd t ≤ G.nu * G.critDiss t := by
  have hD0 : 0 ≤ G.critDiss t := critDissipation_nonneg _ _
  have hsq : Real.sqrt (G.critEnergy t) ≤ G.nu / 128 := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [Real.sqrt_sq (by positivity)] at h
  have habs := G.abs_critProd_le_sqrt_critEnergy_mul_critDiss t
  have hle : G.critProd t ≤ |G.critProd t| := le_abs_self _
  have hstep : 64 * Real.sqrt (G.critEnergy t) * G.critDiss t ≤ (G.nu / 2) * G.critDiss t := by
    refine mul_le_mul_of_nonneg_right ?_ hD0
    linarith [hsq]
  linarith [hle, habs, hstep]

/-- **The unconditional small-critical-energy barrier.**  If the critical energy
starts strictly below the absolute threshold `(ν/128)²`, it never reaches it. -/
theorem critEnergy_le_threshold (hnu : 0 < G.nu) {t₀ : ℝ}
    (hsmall : G.critEnergy t₀ < (G.nu / 128) ^ 2) {t : ℝ} (ht : t₀ ≤ t) :
    G.critEnergy t ≤ (G.nu / 128) ^ 2 := by
  classical
  set c := (G.nu / 128) ^ 2 with hc
  by_contra hcon
  push_neg at hcon
  set T := {s ∈ Set.Icc t₀ t | c ≤ G.critEnergy s} with hT
  have htmem : t ∈ T := by
    refine ⟨Set.mem_Icc.2 ⟨ht, le_rfl⟩, le_of_lt hcon⟩
  have hTne : T.Nonempty := ⟨t, htmem⟩
  have hTclosed : IsClosed T := by
    have h1 : T = Set.Icc t₀ t ∩ (G.critEnergy ⁻¹' Set.Ici c) := by
      ext s
      simp [hT, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    rw [h1]
    exact isClosed_Icc.inter (IsClosed.preimage G.continuous_critEnergy isClosed_Ici)
  have hTbdd : BddBelow T := ⟨t₀, fun s hs => (Set.mem_Icc.1 hs.1).1⟩
  set s := sInf T with hs
  have hsT : s ∈ T := hTclosed.csInf_mem hTne hTbdd
  have hs0 : t₀ ≤ s := (Set.mem_Icc.1 hsT.1).1
  have hsle : s ≤ t := (Set.mem_Icc.1 hsT.1).2
  have hbelow : ∀ x ∈ Set.Ico t₀ s, G.critEnergy x < c := by
    intro x hx
    by_contra hxc
    push_neg at hxc
    have hxT : x ∈ T := ⟨Set.mem_Icc.2 ⟨hx.1, le_trans (le_of_lt hx.2) hsle⟩, hxc⟩
    exact absurd (csInf_le hTbdd hxT) (not_le.2 hx.2)
  have hanti : AntitoneOn G.critEnergy (Set.Icc t₀ s) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ s)
      (G.continuous_critEnergy.continuousOn)
      (fun x _ => ((G.critEnergy_hasDerivAt x).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxlt : G.critEnergy x < c := hbelow x ⟨le_of_lt hx.1, hx.2⟩
    have hderiv : deriv G.critEnergy x = -2 * G.nu * G.critDiss x + 2 * G.critProd x :=
      (G.critEnergy_hasDerivAt x).deriv
    have hpay : 2 * G.critProd x ≤ G.nu * G.critDiss x :=
      G.two_critProd_le_of_small x hnu (le_of_lt hxlt)
    have hD0 : 0 ≤ G.critDiss x := critDissipation_nonneg _ _
    rw [hderiv]
    nlinarith [hpay, hD0, hnu]
  have hEs : G.critEnergy s ≤ G.critEnergy t₀ :=
    hanti (Set.mem_Icc.2 ⟨le_rfl, hs0⟩) (Set.mem_Icc.2 ⟨hs0, le_rfl⟩) hs0
  have hcs : c ≤ G.critEnergy s := hsT.2
  linarith [hsmall, hEs, hcs]

/-- **The small-critical-energy `H^{1/2}` barrier, unconditionally.**  If the
critical energy starts strictly below the absolute threshold `(ν/128)²`, then for
all later times the critical energy is nonincreasing and the critical
dissipation is paid by the initial critical energy — with constants depending
only on `ν`, hence uniformly in the Galerkin cutoff. -/
theorem critEnergy_barrier_of_small_data (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hsmall : G.critEnergy t₀ < (G.nu / 128) ^ 2) :
    G.critEnergy t₁ + G.nu * ∫ t in t₀..t₁, G.critDiss t ≤ G.critEnergy t₀ := by
  have hbal := G.critEnergy_balance t₀ t₁
  have hintP : IntervalIntegrable (fun t => 2 * G.critProd t) MeasureTheory.volume t₀ t₁ :=
    (continuous_const.mul G.continuous_critProd).intervalIntegrable _ _
  have hintD : IntervalIntegrable (fun t => G.nu * G.critDiss t) MeasureTheory.volume t₀ t₁ :=
    (continuous_const.mul G.continuous_critDiss).intervalIntegrable _ _
  have hmono : (∫ t in t₀..t₁, 2 * G.critProd t) ≤ ∫ t in t₀..t₁, G.nu * G.critDiss t := by
    refine intervalIntegral.integral_mono_on ht hintP hintD ?_
    intro x hx
    exact G.two_critProd_le_of_small x hnu
      (G.critEnergy_le_threshold hnu hsmall (Set.mem_Icc.1 hx).1)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  linarith [hbal, hmono]

/-- **The companion budget in the small-critical-data regime.**  Below the
absolute threshold the time-integrated square of the enstrophy — the quantity
whose cutoff-uniform bound the conditional barrier
`critEnergy_barrier_of_companion_budget` requires — is itself controlled by the
initial critical energy, with a constant depending only on `ν`. -/
theorem integral_enstrophy_sq_le_of_small_data (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hsmall : G.critEnergy t₀ < (G.nu / 128) ^ 2) :
    (∫ t in t₀..t₁, (G.enstrophy t) ^ 2) ≤ (G.nu / 128) ^ 2 * (G.critEnergy t₀ / G.nu) := by
  have hintE : IntervalIntegrable (fun t => (G.enstrophy t) ^ 2) MeasureTheory.volume t₀ t₁ :=
    (G.continuous_enstrophy.pow 2).intervalIntegrable _ _
  have hintD : IntervalIntegrable (fun t => (G.nu / 128) ^ 2 * G.critDiss t)
      MeasureTheory.volume t₀ t₁ :=
    (continuous_const.mul G.continuous_critDiss).intervalIntegrable _ _
  have hmono : (∫ t in t₀..t₁, (G.enstrophy t) ^ 2)
      ≤ ∫ t in t₀..t₁, (G.nu / 128) ^ 2 * G.critDiss t := by
    refine intervalIntegral.integral_mono_on ht hintE hintD ?_
    intro x hx
    have hthr : G.critEnergy x ≤ (G.nu / 128) ^ 2 :=
      G.critEnergy_le_threshold hnu hsmall (Set.mem_Icc.1 hx).1
    have hinterp : (G.enstrophy x) ^ 2 ≤ G.critEnergy x * G.critDiss x :=
      G.enstrophy_sq_le_critEnergy_mul_critDiss x
    have hD0 : 0 ≤ G.critDiss x := critDissipation_nonneg _ _
    nlinarith [hinterp, hthr, hD0]
  have hbar := G.critEnergy_barrier_of_small_data hnu ht hsmall
  have hE1 : 0 ≤ G.critEnergy t₁ := G.critEnergy_nonneg t₁
  have hD : (∫ t in t₀..t₁, G.critDiss t) ≤ G.critEnergy t₀ / G.nu := by
    rw [le_div_iff₀ hnu]
    nlinarith [hbar, hE1]
  rw [intervalIntegral.integral_const_mul] at hmono
  have hc : (0 : ℝ) ≤ (G.nu / 128) ^ 2 := sq_nonneg _
  nlinarith [hmono, hD, hc]

end GalerkinFlow

end ClayNS.Waleffe
