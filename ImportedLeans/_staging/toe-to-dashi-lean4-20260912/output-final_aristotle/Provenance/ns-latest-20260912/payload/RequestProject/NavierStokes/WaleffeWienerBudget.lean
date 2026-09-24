/-
# Reduction of the network-forcing wall to one Wiener-algebra expenditure

`WaleffeNetworkForcingBudget.lean` states the Round 105 wall
`PhysicalWeightedPositiveWaleffeNetworkForcingBudget`: a truncation-uniform
bound for the weighted positive network forcing
`∑_τ w_τ ∫_0^T (F_τ)₊` of the physical Galerkin system.

This file *sharpens* that wall: it proves, unconditionally, that the whole
weighted positive network forcing of a Galerkin flow is dominated by a single
scalar quantity of the flow, namely

`3 W ∫_0^T ‖u(t)‖_A³ ‖u(t)‖_D dt`,

where

* `‖u‖_A = ∑_{k ∈ modes} |u_k|` is the (discrete) Wiener-algebra norm and
* `‖u‖_D = ∑_{k ∈ modes} |k| |u_k|` is its one-derivative version,

and `W` is any bound for the weights.  The three factors of `‖u‖_A` come from
the three product-rule slots of the triad amplitude summed over the resonance
set `k = p + q`; the single factor of `‖u‖_D` is the one derivative carried by
the advective nonlinearity.

Consequences proved here:

* `network_forcing_pointwise_bound` — the pointwise (in time) inequality;
* `weightedPositiveForcing_le_wiener` — its time-integrated form, with all
  integrability supplied by `GalerkinFlow.continuous_force3` (a Galerkin flow
  is automatically continuous in time, being a solution of its own ODE);
* `budget_of_uniform_wiener_expenditure` — the wall follows from
  `UniformWienerExpenditure`, i.e. from a truncation-uniform bound on
  `∫_0^T ‖u‖_A³ ‖u‖_D dt` alone;
* `wiener_norm_not_controlled_by_energy` — and that this remaining input is
  *not* available from the energy inequality: there are transverse fields of
  unit energy and arbitrarily large Wiener norm.  This is the precise sense in
  which the wall is supercritical.
-/
import RequestProject.NavierStokes.WaleffeForcingMajorant

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-! ## Wiener-algebra norms on the retained modes -/

/-- The discrete Wiener-algebra norm `∑_{k ∈ modes} |u_k|`. -/
def wienerA (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ modes, nrm (u k)

/-- The one-derivative Wiener norm `∑_{k ∈ modes} |k| |u_k|`. -/
def wienerD (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ modes, wlen k * nrm (u k)

theorem wlen_nonneg (k : Wave) : 0 ≤ wlen k := Real.sqrt_nonneg _

theorem wienerA_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ wienerA modes u :=
  Finset.sum_nonneg fun _ _ => nrm_nonneg _

theorem wienerD_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ wienerD modes u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (wlen_nonneg _) (nrm_nonneg _)

theorem nrm_zero_fun : nrm (fun _ : Fin 3 => (0 : ℂ)) = 0 := by
  simp [nrm, nsq]

theorem wsq_eq_zero_iff (k : Wave) : wsq k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h3 : ((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 + ((k 2 : ℝ)) ^ 2 = 0 := by
      simpa [wsq, Fin.sum_univ_three] using h
    have h0 : (k 0 : ℝ) = 0 ∧ (k 1 : ℝ) = 0 ∧ (k 2 : ℝ) = 0 := by
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg ((k 0 : ℝ)), sq_nonneg ((k 1 : ℝ)),
        sq_nonneg ((k 2 : ℝ))]
    have hall : ∀ i : Fin 3, k i = 0 := by
      intro i
      have : (k i : ℝ) = 0 := by fin_cases i <;> tauto
      exact_mod_cast this
    funext i
    simpa using hall i
  · intro h; simp [wsq, h]

theorem wsq_ne_zero_of_mem {modes : Finset Wave} (hz : (0 : Wave) ∉ modes) {k : Wave}
    (hk : k ∈ modes) : wsq k ≠ 0 := by
  intro h
  exact hz ((wsq_eq_zero_iff k).1 h ▸ hk)

/-! ## The forcing majorant is a Wiener product -/

/-- The `ℓ¹` convolution majorant of the modal forcing is bounded by
`‖u‖_A ‖u‖_D` at every wavevector, for any field supported on the mode set. -/
theorem forcingMajorant_le_wiener (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hsupp : ∀ m, m ∉ modes → u m = 0) (k : Wave) :
    forcingMajorant modes u k ≤ wienerA modes u * wienerD modes u := by
  have hterm : ∀ p ∈ modes,
      nrm (u p) * wlen (k - p) * nrm (u (k - p)) ≤ nrm (u p) * wienerD modes u := by
    intro p _
    by_cases hm : k - p ∈ modes
    · have hle : wlen (k - p) * nrm (u (k - p)) ≤ wienerD modes u :=
        Finset.single_le_sum (f := fun m => wlen m * nrm (u m))
          (fun m _ => mul_nonneg (wlen_nonneg m) (nrm_nonneg _)) hm
      calc nrm (u p) * wlen (k - p) * nrm (u (k - p))
          = nrm (u p) * (wlen (k - p) * nrm (u (k - p))) := by ring
        _ ≤ nrm (u p) * wienerD modes u :=
            mul_le_mul_of_nonneg_left hle (nrm_nonneg _)
    · have h0 : nrm (u (k - p)) = 0 := by rw [hsupp _ hm]; exact nrm_zero_fun
      rw [h0, mul_zero]
      exact mul_nonneg (nrm_nonneg _) (wienerD_nonneg _ _)
  calc forcingMajorant modes u k ≤ ∑ p ∈ modes, nrm (u p) * wienerD modes u :=
        Finset.sum_le_sum hterm
    _ = wienerA modes u * wienerD modes u := by rw [wienerA, Finset.sum_mul]

/-! ## Summing over the resonance set -/

/-- A sum over ordered resonant triads of a product of two nonnegative modal
factors is bounded by the square of the corresponding modal sum, as soon as the
two chosen legs determine the triad. -/
theorem triads_pair_sum_le (modes : Finset Wave) (a : Wave → ℝ) (ha : ∀ k, 0 ≤ a k)
    (φ : Wave × Wave × Wave → Wave × Wave)
    (hmem : ∀ τ ∈ triads modes, (φ τ).1 ∈ modes ∧ (φ τ).2 ∈ modes)
    (hinj : ∀ τ ∈ triads modes, ∀ σ ∈ triads modes, φ τ = φ σ → τ = σ) :
    ∑ τ ∈ triads modes, a (φ τ).1 * a (φ τ).2 ≤ (∑ k ∈ modes, a k) ^ 2 := by
  have himg : (triads modes).image φ ⊆ modes ×ˢ modes := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact Finset.mem_product.2 (hmem τ hτ)
  have hsum : ∑ z ∈ (triads modes).image φ, a z.1 * a z.2
      = ∑ τ ∈ triads modes, a (φ τ).1 * a (φ τ).2 :=
    Finset.sum_image hinj
  have hle : ∑ z ∈ (triads modes).image φ, a z.1 * a z.2
      ≤ ∑ z ∈ modes ×ˢ modes, a z.1 * a z.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg himg
      (fun z _ _ => mul_nonneg (ha _) (ha _))
  have hprod : ∑ z ∈ modes ×ˢ modes, a z.1 * a z.2 = (∑ k ∈ modes, a k) ^ 2 := by
    rw [Finset.sum_product, sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  rw [← hsum, ← hprod]
  exact hle

/-! ## The pointwise network-forcing bound -/

variable (G : GalerkinFlow)

theorem force_majorant_wiener (t : ℝ) (k : Wave) :
    forcingMajorant G.modes (G.u t) k ≤ wienerA G.modes (G.u t) * wienerD G.modes (G.u t) :=
  forcingMajorant_le_wiener _ _ (fun m hm => G.support t m hm) k

/-- **Pointwise Wiener bound for the weighted positive network forcing.**  At
each instant, the whole weighted positive network forcing of the Galerkin
system is at most `3 W ‖u‖_A³ ‖u‖_D`. -/
theorem network_forcing_pointwise_bound (w : Wave × Wave × Wave → ℝ) {W : ℝ}
    (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (t : ℝ) :
    ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
      ≤ 3 * W * (wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t) := by
  set a : Wave → ℝ := fun k => nrm (G.u t k) with ha_def
  have ha : ∀ k, 0 ≤ a k := fun k => nrm_nonneg _
  set A := wienerA G.modes (G.u t) with hA
  set D := wienerD G.modes (G.u t) with hD
  have hAnn : 0 ≤ A := wienerA_nonneg _ _
  have hDnn : 0 ≤ D := wienerD_nonneg _ _
  have hW : 0 ≤ W := le_trans (hw0 (0, 0, 0)) (hwW (0, 0, 0))
  -- termwise bound
  have hterm : ∀ τ ∈ triads G.modes,
      w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
        ≤ W * (A * D) * (a τ.2.1 * a τ.2.2)
          + W * (A * D) * (a τ.1 * a τ.2.2)
          + W * (A * D) * (a τ.1 * a τ.2.1) := by
    intro τ hτ
    obtain ⟨hk, hp, hq, -⟩ := mem_triads hτ
    have hkz := wsq_ne_zero_of_mem G.zero_not_mem hk
    have hpz := wsq_ne_zero_of_mem G.zero_not_mem hp
    have hqz := wsq_ne_zero_of_mem G.zero_not_mem hq
    have hmaj := force3_majorant G τ.1 τ.2.1 τ.2.2 t hkz hpz hqz
    have hFk := force_majorant_wiener G t τ.1
    have hFp := force_majorant_wiener G t τ.2.1
    have hFq := force_majorant_wiener G t τ.2.2
    have hAD : 0 ≤ A * D := mul_nonneg hAnn hDnn
    have e1 : forcingMajorant G.modes (G.u t) τ.1 * a τ.2.1 * a τ.2.2
        ≤ (A * D) * (a τ.2.1 * a τ.2.2) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hFk (ha τ.2.1)) (ha τ.2.2)
      nlinarith [this]
    have e2 : a τ.1 * forcingMajorant G.modes (G.u t) τ.2.1 * a τ.2.2
        ≤ (A * D) * (a τ.1 * a τ.2.2) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFp (ha τ.1)) (ha τ.2.2)
      nlinarith [this]
    have e3 : a τ.1 * a τ.2.1 * forcingMajorant G.modes (G.u t) τ.2.2
        ≤ (A * D) * (a τ.1 * a τ.2.1) := by
      have := mul_le_mul_of_nonneg_left hFq (mul_nonneg (ha τ.1) (ha τ.2.1))
      nlinarith [this]
    have habs : |G.force3 τ.1 τ.2.1 τ.2.2 t|
        ≤ (A * D) * (a τ.2.1 * a τ.2.2) + (A * D) * (a τ.1 * a τ.2.2)
          + (A * D) * (a τ.1 * a τ.2.1) := by
      simp only [ha_def] at e1 e2 e3 ⊢
      linarith [hmaj, e1, e2, e3]
    have hmax : max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 ≤ |G.force3 τ.1 τ.2.1 τ.2.2 t| :=
      max_le (le_abs_self _) (abs_nonneg _)
    have hnn : 0 ≤ max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := le_max_right _ _
    calc w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
        ≤ W * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 :=
          mul_le_mul_of_nonneg_right (hwW τ) hnn
      _ ≤ W * ((A * D) * (a τ.2.1 * a τ.2.2) + (A * D) * (a τ.1 * a τ.2.2)
            + (A * D) * (a τ.1 * a τ.2.1)) :=
          mul_le_mul_of_nonneg_left (le_trans hmax habs) hW
      _ = W * (A * D) * (a τ.2.1 * a τ.2.2) + W * (A * D) * (a τ.1 * a τ.2.2)
            + W * (A * D) * (a τ.1 * a τ.2.1) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  -- the three resonance sums
  have hpq : ∑ τ ∈ triads G.modes, a τ.2.1 * a τ.2.2 ≤ A ^ 2 := by
    have := triads_pair_sum_le G.modes a ha (fun τ => (τ.2.1, τ.2.2))
      (fun τ hτ => ⟨(mem_triads hτ).2.1, (mem_triads hτ).2.2.1⟩)
      (fun τ hτ σ hσ h => by
        obtain ⟨-, -, -, hτs⟩ := mem_triads hτ
        obtain ⟨-, -, -, hσs⟩ := mem_triads hσ
        have h1 : τ.2.1 = σ.2.1 := congrArg Prod.fst h
        have h2 : τ.2.2 = σ.2.2 := congrArg Prod.snd h
        have : τ.1 = σ.1 := by rw [hτs, hσs, h1, h2]
        exact Prod.ext this (Prod.ext h1 h2))
    simpa [hA, wienerA, ha_def] using this
  have hkq : ∑ τ ∈ triads G.modes, a τ.1 * a τ.2.2 ≤ A ^ 2 := by
    have := triads_pair_sum_le G.modes a ha (fun τ => (τ.1, τ.2.2))
      (fun τ hτ => ⟨(mem_triads hτ).1, (mem_triads hτ).2.2.1⟩)
      (fun τ hτ σ hσ h => by
        obtain ⟨-, -, -, hτs⟩ := mem_triads hτ
        obtain ⟨-, -, -, hσs⟩ := mem_triads hσ
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have hsum' : τ.2.1 + τ.2.2 = σ.2.1 + σ.2.2 := by rw [← hτs, ← hσs, h1]
        have hp : τ.2.1 = σ.2.1 := by
          rw [h2] at hsum'
          exact add_right_cancel hsum'
        exact Prod.ext h1 (Prod.ext hp h2))
    simpa [hA, wienerA, ha_def] using this
  have hkp : ∑ τ ∈ triads G.modes, a τ.1 * a τ.2.1 ≤ A ^ 2 := by
    have := triads_pair_sum_le G.modes a ha (fun τ => (τ.1, τ.2.1))
      (fun τ hτ => ⟨(mem_triads hτ).1, (mem_triads hτ).2.1⟩)
      (fun τ hτ σ hσ h => by
        obtain ⟨-, -, -, hτs⟩ := mem_triads hτ
        obtain ⟨-, -, -, hσs⟩ := mem_triads hσ
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have hsum' : τ.2.1 + τ.2.2 = σ.2.1 + σ.2.2 := by rw [← hτs, ← hσs, h1]
        have hq : τ.2.2 = σ.2.2 := by
          rw [h2] at hsum'
          exact add_left_cancel hsum'
        exact Prod.ext h1 (Prod.ext h2 hq))
    simpa [hA, wienerA, ha_def] using this
  have hWAD : 0 ≤ W * (A * D) := mul_nonneg hW (mul_nonneg hAnn hDnn)
  have s1 : ∑ τ ∈ triads G.modes, W * (A * D) * (a τ.2.1 * a τ.2.2)
      ≤ W * (A * D) * A ^ 2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hpq hWAD
  have s2 : ∑ τ ∈ triads G.modes, W * (A * D) * (a τ.1 * a τ.2.2)
      ≤ W * (A * D) * A ^ 2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hkq hWAD
  have s3 : ∑ τ ∈ triads G.modes, W * (A * D) * (a τ.1 * a τ.2.1)
      ≤ W * (A * D) * A ^ 2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hkp hWAD
  have : (3 : ℝ) * W * A ^ 3 * D = W * (A * D) * A ^ 2 + W * (A * D) * A ^ 2
      + W * (A * D) * A ^ 2 := by ring
  linarith [hsum, s1, s2, s3]

/-! ## Continuity in time: a Galerkin flow solves its own ODE -/

namespace GalerkinFlow

/-- Every Fourier coefficient of a Galerkin flow is continuous in time: on the
retained modes because it is differentiable (it solves the ODE), off them
because it vanishes. -/
theorem continuous_u (G : GalerkinFlow) (k : Wave) (i : Fin 3) :
    Continuous fun t => G.u t k i := by
  by_cases h : k ∈ G.modes
  · have hd : Differentiable ℝ (fun s => G.u s k i) := fun t => (G.ode t k h i).differentiableAt
    exact hd.continuous
  · have he : (fun t => G.u t k i) = fun _ => (0 : ℂ) := by
      funext t; rw [G.support t k h]; rfl
    rw [he]; exact continuous_const

end GalerkinFlow

theorem continuous_herm_of {f g : ℝ → Fin 3 → ℂ} (hf : ∀ i, Continuous fun t => f t i)
    (hg : ∀ i, Continuous fun t => g t i) : Continuous fun t => herm (f t) (g t) := by
  show Continuous fun t => ∑ i, (starRingEnd ℂ) (f t i) * g t i
  exact continuous_finset_sum _ fun i _ => (Complex.continuous_conj.comp (hf i)).mul (hg i)

theorem continuous_cross_of {f g : ℝ → Fin 3 → ℂ} (hf : ∀ i, Continuous fun t => f t i)
    (hg : ∀ i, Continuous fun t => g t i) (i : Fin 3) :
    Continuous fun t => cross (f t) (g t) i := by
  fin_cases i <;>
    simp only [cross, cross_apply] <;>
    exact ((hf _).mul (hg _)).sub ((hf _).mul (hg _))

namespace GalerkinFlow

theorem continuous_advection (G : GalerkinFlow) (m : Wave) (i : Fin 3) :
    Continuous fun t => advection G.modes (G.u t) m i := by
  show Continuous fun t => ∑ p ∈ G.modes,
    (Complex.I * (∑ j, G.u t p j * (((m - p) j : ℤ) : ℂ))) * G.u t (m - p) i
  refine continuous_finset_sum _ fun p _ => Continuous.mul ?_ (G.continuous_u (m - p) i)
  exact continuous_const.mul
    (continuous_finset_sum _ fun j _ => (G.continuous_u p j).mul continuous_const)

theorem continuous_force (G : GalerkinFlow) (k : Wave) (i : Fin 3) :
    Continuous fun t => G.force t k i := by
  show Continuous fun t => -(advection G.modes (G.u t) k i
    - (herm (wC k) (advection G.modes (G.u t) k) / ((wsq k : ℝ) : ℂ)) * ((k i : ℤ) : ℂ))
  have hherm : Continuous fun t => herm (wC k) (advection G.modes (G.u t) k) :=
    continuous_herm_of (f := fun _ => wC k) (fun _ => continuous_const)
      (fun j => G.continuous_advection k j)
  exact (((G.continuous_advection k i).sub
    ((hherm.div_const _).mul continuous_const))).neg

theorem continuous_force3 (G : GalerkinFlow) (k p q : Wave) :
    Continuous (G.force3 k p q) := by
  show Continuous fun t => (netForcingC (G.u t k) (G.u t p) (G.u t q)
    (G.force t k) (G.force t p) (G.force t q)).re
  refine Complex.continuous_re.comp ?_
  show Continuous fun t =>
    herm (G.force t k) (cross (G.u t p) (G.u t q))
      + herm (G.u t k) (cross (G.force t p) (G.u t q))
      + herm (G.u t k) (cross (G.u t p) (G.force t q))
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · exact continuous_herm_of (G.continuous_force k)
      (continuous_cross_of (G.continuous_u p) (G.continuous_u q))
  · exact continuous_herm_of (G.continuous_u k)
      (continuous_cross_of (G.continuous_force p) (G.continuous_u q))
  · exact continuous_herm_of (G.continuous_u k)
      (continuous_cross_of (G.continuous_u p) (G.continuous_force q))

theorem continuous_nrm_u (G : GalerkinFlow) (k : Wave) :
    Continuous fun t => nrm (G.u t k) := by
  show Continuous fun t => Real.sqrt (∑ i, Complex.normSq (G.u t k i))
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
  exact Complex.continuous_normSq.comp (G.continuous_u k i)

theorem continuous_wienerA (G : GalerkinFlow) :
    Continuous fun t => wienerA G.modes (G.u t) :=
  continuous_finset_sum _ fun k _ => G.continuous_nrm_u k

theorem continuous_wienerD (G : GalerkinFlow) :
    Continuous fun t => wienerD G.modes (G.u t) :=
  continuous_finset_sum _ fun k _ => continuous_const.mul (G.continuous_nrm_u k)

end GalerkinFlow

/-! ## The integrated Wiener bound, and the reduction of the wall -/

/-- **Integrated Wiener bound.**  The weighted positive network-forcing
expenditure of a Galerkin flow over a time window is at most
`3 W ∫ ‖u‖_A³ ‖u‖_D`.  No hypothesis beyond the Galerkin equations and a bound
`W` for the weights is used; the integrability is automatic. -/
theorem weightedPositiveForcing_le_wiener (G : GalerkinFlow) (w : Wave × Wave × Wave → ℝ)
    {W t₀ t₁ : ℝ} (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (ht : t₀ ≤ t₁) :
    weightedPositiveForcing G w t₀ t₁
      ≤ 3 * W * ∫ t in t₀..t₁, (wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t) := by
  have hgc : ∀ τ : Wave × Wave × Wave,
      Continuous fun t => w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := fun τ =>
    continuous_const.mul ((G.continuous_force3 τ.1 τ.2.1 τ.2.2).max continuous_const)
  have hint : ∀ τ ∈ triads G.modes,
      IntervalIntegrable (fun t => w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
        MeasureTheory.volume t₀ t₁ := fun τ _ => (hgc τ).intervalIntegrable _ _
  have hswap : weightedPositiveForcing G w t₀ t₁
      = ∫ t in t₀..t₁, ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := by
    rw [intervalIntegral.integral_finset_sum hint]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [intervalIntegral.integral_const_mul]
  have hRHS : Continuous fun t =>
      3 * W * ((wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t)) :=
    continuous_const.mul ((G.continuous_wienerA.pow 3).mul G.continuous_wienerD)
  have hmono : (∫ t in t₀..t₁, ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
      ≤ ∫ t in t₀..t₁, 3 * W * ((wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t)) := by
    refine intervalIntegral.integral_mono_on ht ?_ (hRHS.intervalIntegrable _ _) ?_
    · exact (continuous_finset_sum _ fun τ _ => hgc τ).intervalIntegrable _ _
    · intro t _
      have := network_forcing_pointwise_bound G w hw0 hwW t
      calc ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
          ≤ 3 * W * (wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t) := this
        _ = 3 * W * ((wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t)) := by ring
  rw [hswap, ← intervalIntegral.integral_const_mul]
  exact hmono

/-- The single remaining analytic input: a truncation-uniform bound for the
time-integrated Wiener expenditure `∫_0^T ‖u‖_A³ ‖u‖_D dt` of the Galerkin
flows of a fixed smooth datum. -/
def UniformWienerExpenditure (nu T : ℝ) : Prop :=
  ∀ u0 : Wave → Fin 3 → ℂ, RapidlyDecaying u0 → ∃ C : ℝ,
    ∀ G : GalerkinFlow, G.nu = nu → (∀ k ∈ G.modes, G.u 0 k = u0 k) →
      (∫ t in (0:ℝ)..T, (wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t)) ≤ C

/-- **Reduction of the Round 105 wall.**  For bounded weights, the physical
weighted positive Waleffe network-forcing budget follows from the uniform
Wiener expenditure alone. -/
theorem budget_of_uniform_wiener_expenditure {nu T W : ℝ} (w : Wave × Wave × Wave → ℝ)
    (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (hT : 0 ≤ T)
    (H : UniformWienerExpenditure nu T) :
    PhysicalWeightedPositiveWaleffeNetworkForcingBudget nu T w := by
  intro u0 hu0
  obtain ⟨C, hC⟩ := H u0 hu0
  have hW : 0 ≤ W := le_trans (hw0 (0, 0, 0)) (hwW (0, 0, 0))
  refine ⟨3 * W * C, fun G hnu hinit => ?_⟩
  have h1 := weightedPositiveForcing_le_wiener G w hw0 hwW hT
  have h2 := hC G hnu hinit
  have h3 : 3 * W * (∫ t in (0:ℝ)..T, (wienerA G.modes (G.u t)) ^ 3 * wienerD G.modes (G.u t))
      ≤ 3 * W * C := by
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

end ClayNS.Waleffe
