/-
# Sharpened reduction: the residual input is a Serrin-type Wiener quantity

`WaleffeWienerBudget.lean` bounds the weighted positive network forcing by
`3 W ‖u‖_A³ ‖u‖_D`, where `‖u‖_D = ∑_k |k| |u_k|` still carries a full
derivative in `ℓ¹`.  That is wasteful: the resonance sums are convolutions, and
discrete Young `ℓ¹ ⋆ ℓ² → ℓ²` lets one keep only *one* `ℓ¹` factor per
convolution.

This file carries that out.  Writing

* `‖u‖_A = ∑_k |u_k|` (Wiener),
* `‖u‖_2 = (∑_k |u_k|²)^{1/2}` (energy),
* `‖u‖_{Ḣ¹} = (∑_k |k|² |u_k|²)^{1/2}` (Dirichlet),

the results are

* `forcing_l2_le` — `‖f‖_2 ≤ ‖u‖_A ‖u‖_{Ḣ¹}` for the literal projected
  nonlinearity (discrete Young);
* `network_forcing_serrin_bound` — the pointwise estimate
  `∑_τ w_τ (F_τ)₊ ≤ 3 W ‖u‖_A² ‖u‖_2 ‖u‖_{Ḣ¹}`;
* `weightedPositiveForcing_le_serrin` — its integrated form;
* `budget_of_uniform_serrin_expenditure` — the Round 105 wall follows from a
  truncation-uniform bound on `∫_0^T ‖u‖_A² ‖u‖_2 ‖u‖_{Ḣ¹} dt` alone.

The `Ḣ¹` factor is the one quantity the Navier–Stokes energy balance pays for
(time-integrated dissipation), and the `‖u‖_2` factor is bounded by the datum,
so the genuinely missing ingredient is only the *square of the Wiener norm*,
integrated in time: a Serrin-type `L⁴_t` condition in the Wiener algebra.  This
is a strictly stronger reduction than the one in `WaleffeWienerBudget.lean`:
no derivative is left in `ℓ¹`.
-/
import RequestProject.NavierStokes.WaleffeWienerBudget

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-! ## Energy and Dirichlet norms of a Fourier-lattice field -/

/-- The energy norm `(∑_k |u_k|²)^{1/2}` on the retained modes. -/
def wienerL2 (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  Real.sqrt (∑ k ∈ modes, nsq (u k))

/-- The Dirichlet norm `(∑_k |k|² |u_k|²)^{1/2}` on the retained modes. -/
def wienerH1 (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  Real.sqrt (∑ k ∈ modes, wsq k * nsq (u k))

theorem wsq_nonneg (k : Wave) : 0 ≤ wsq k := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem wienerL2_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ wienerL2 modes u := Real.sqrt_nonneg _

theorem wienerH1_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    0 ≤ wienerH1 modes u := Real.sqrt_nonneg _

/-! ## Translation and discrete Young inequalities -/

/-- Translating the index set can only lose mass, for a nonnegative summand
vanishing off the mode set. -/
theorem sum_translate_le (modes : Finset Wave) (g : Wave → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hsupp : ∀ m, m ∉ modes → g m = 0) (T : Wave → Wave) (hT : Function.Injective T) :
    ∑ q ∈ modes, g (T q) ≤ ∑ m ∈ modes, g m := by
  have himg : ∑ m ∈ modes.image T, g m = ∑ q ∈ modes, g (T q) :=
    Finset.sum_image fun x _ y _ h => hT h
  have hinter : ∑ m ∈ (modes.image T) ∩ modes, g m = ∑ m ∈ modes.image T, g m := by
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro x hx hnx
    have : x ∉ modes := by
      intro hm
      exact hnx (Finset.mem_inter.2 ⟨hx, hm⟩)
    exact hsupp x this
  have hsub : ∑ m ∈ (modes.image T) ∩ modes, g m ≤ ∑ m ∈ modes, g m :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun m _ _ => hg m
  rw [← himg, ← hinter]
  exact hsub

/-- The core convolution estimate: one `ℓ¹` factor and two `ℓ²` factors. -/
theorem double_sum_conv_le (modes : Finset Wave) (a b c : Wave → ℝ)
    (hb : ∀ m, 0 ≤ b m) (ha0 : ∀ m, m ∉ modes → a m = 0) :
    ∑ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q
      ≤ (∑ p ∈ modes, b p) * Real.sqrt (∑ k ∈ modes, (a k) ^ 2)
        * Real.sqrt (∑ q ∈ modes, (c q) ^ 2) := by
  set A2 := Real.sqrt (∑ k ∈ modes, (a k) ^ 2) with hA2
  set C2 := Real.sqrt (∑ q ∈ modes, (c q) ^ 2) with hC2
  have hA2n : 0 ≤ A2 := Real.sqrt_nonneg _
  have hC2n : 0 ≤ C2 := Real.sqrt_nonneg _
  have hinner : ∀ p ∈ modes, ∑ q ∈ modes, a (p + q) * c q ≤ A2 * C2 := by
    intro p _
    have hcs : ∑ q ∈ modes, a (p + q) * c q
        ≤ Real.sqrt (∑ q ∈ modes, (a (p + q)) ^ 2) * Real.sqrt (∑ q ∈ modes, (c q) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt modes (fun q => a (p + q)) c
    have hshift : ∑ q ∈ modes, (a (p + q)) ^ 2 ≤ ∑ k ∈ modes, (a k) ^ 2 :=
      sum_translate_le modes (fun m => (a m) ^ 2) (fun m => sq_nonneg _)
        (fun m hm => by show (a m) ^ 2 = 0; rw [ha0 m hm]; ring) (fun q => p + q)
        (fun x y h => by simpa using add_left_cancel h)
    have := Real.sqrt_le_sqrt hshift
    calc ∑ q ∈ modes, a (p + q) * c q
        ≤ Real.sqrt (∑ q ∈ modes, (a (p + q)) ^ 2) * C2 := hcs
      _ ≤ A2 * C2 := mul_le_mul_of_nonneg_right this hC2n
  have hstep : ∀ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q ≤ b p * (A2 * C2) := by
    intro p hp
    have hfac : ∑ q ∈ modes, a (p + q) * b p * c q
        = b p * ∑ q ∈ modes, a (p + q) * c q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left (hinner p hp) (hb p)
  calc ∑ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q
      ≤ ∑ p ∈ modes, b p * (A2 * C2) := Finset.sum_le_sum hstep
    _ = (∑ p ∈ modes, b p) * A2 * C2 := by rw [← Finset.sum_mul]; ring

/-- The mirrored convolution estimate, with the `ℓ¹` factor on the third leg. -/
theorem double_sum_conv_le' (modes : Finset Wave) (a b c : Wave → ℝ)
    (hc : ∀ m, 0 ≤ c m) (ha0 : ∀ m, m ∉ modes → a m = 0) :
    ∑ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q
      ≤ (∑ q ∈ modes, c q) * Real.sqrt (∑ k ∈ modes, (a k) ^ 2)
        * Real.sqrt (∑ p ∈ modes, (b p) ^ 2) := by
  have hswap : ∑ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q
      = ∑ q ∈ modes, ∑ p ∈ modes, a (q + p) * c q * b p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [add_comm q p]
    ring
  rw [hswap]
  exact double_sum_conv_le modes a c b hc ha0

/-! ## Summation over the resonance set -/

/-- A triple sum over ordered resonant triads is dominated by the corresponding
double sum over all pairs of retained modes. -/
theorem triads_triple_sum_le (modes : Finset Wave) (a b c : Wave → ℝ)
    (ha : ∀ m, 0 ≤ a m) (hb : ∀ m, 0 ≤ b m) (hc : ∀ m, 0 ≤ c m) :
    ∑ τ ∈ triads modes, a τ.1 * b τ.2.1 * c τ.2.2
      ≤ ∑ p ∈ modes, ∑ q ∈ modes, a (p + q) * b p * c q := by
  have hinj : ∀ τ ∈ triads modes, ∀ σ ∈ triads modes,
      (τ.2.1, τ.2.2) = (σ.2.1, σ.2.2) → τ = σ := by
    intro τ hτ σ hσ h
    obtain ⟨-, -, -, hτs⟩ := mem_triads hτ
    obtain ⟨-, -, -, hσs⟩ := mem_triads hσ
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : τ.1 = σ.1 := by rw [hτs, hσs, h1, h2]
    exact Prod.ext this (Prod.ext h1 h2)
  have heq : ∑ τ ∈ triads modes, a τ.1 * b τ.2.1 * c τ.2.2
      = ∑ z ∈ (triads modes).image (fun τ => (τ.2.1, τ.2.2)), a (z.1 + z.2) * b z.1 * c z.2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨-, -, -, hτs⟩ := mem_triads hτ
    rw [← hτs]
  have hsub : (triads modes).image (fun τ => (τ.2.1, τ.2.2)) ⊆ modes ×ˢ modes := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact Finset.mem_product.2 ⟨(mem_triads hτ).2.1, (mem_triads hτ).2.2.1⟩
  have hle : ∑ z ∈ (triads modes).image (fun τ => (τ.2.1, τ.2.2)), a (z.1 + z.2) * b z.1 * c z.2
      ≤ ∑ z ∈ modes ×ˢ modes, a (z.1 + z.2) * b z.1 * c z.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun z _ _ => mul_nonneg (mul_nonneg (ha _) (hb _)) (hc _)
  rw [heq]
  rw [Finset.sum_product] at hle
  exact hle

/-! ## Discrete Young for the projected nonlinearity -/

/-- The `ℓ²` norm of the forcing majorant on the retained modes. -/
def forcingL2 (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) : ℝ :=
  Real.sqrt (∑ k ∈ modes, (forcingMajorant modes u k) ^ 2)

/-- **Discrete Young for the nonlinearity.**  `‖f‖_2 ≤ ‖u‖_A ‖u‖_{Ḣ¹}`: only one
`ℓ¹` factor is needed, and the derivative is carried in `ℓ²`. -/
theorem forcingL2_le (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hsupp : ∀ m, m ∉ modes → u m = 0) :
    forcingL2 modes u ≤ wienerA modes u * wienerH1 modes u := by
  set b : Wave → ℝ := fun p => nrm (u p) with hb_def
  set g : Wave → ℝ := fun m => wlen m * nrm (u m) with hg_def
  have hbn : ∀ p, 0 ≤ b p := fun p => nrm_nonneg _
  have hgn : ∀ m, 0 ≤ g m := fun m => mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)
  have hg0 : ∀ m, m ∉ modes → g m = 0 := by
    intro m hm
    have : nrm (u m) = 0 := by rw [hsupp m hm]; exact nrm_zero_fun
    simp [hg_def, this]
  have hsqg : ∀ m, (g m) ^ 2 = wsq m * nsq (u m) := by
    intro m
    have h1 : (wlen m) ^ 2 = wsq m := Real.sq_sqrt (wsq_nonneg m)
    have h2 : (nrm (u m)) ^ 2 = nsq (u m) := Real.sq_sqrt (nsq_nonneg _)
    rw [hg_def]
    simp only
    rw [mul_pow, h1, h2]
  -- pointwise Cauchy–Schwarz on the convolution
  have hpt : ∀ k, (forcingMajorant modes u k) ^ 2
      ≤ (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * (g (k - p)) ^ 2 := by
    intro k
    have hsplit : forcingMajorant modes u k
        = ∑ p ∈ modes, Real.sqrt (b p) * (Real.sqrt (b p) * g (k - p)) := by
      rw [forcingMajorant]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hbp : Real.sqrt (b p) * Real.sqrt (b p) = b p :=
        Real.mul_self_sqrt (hbn p)
      calc nrm (u p) * wlen (k - p) * nrm (u (k - p))
          = b p * g (k - p) := by rw [hb_def, hg_def]; ring
        _ = (Real.sqrt (b p) * Real.sqrt (b p)) * g (k - p) := by rw [hbp]
        _ = Real.sqrt (b p) * (Real.sqrt (b p) * g (k - p)) := by ring
    rw [hsplit]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq modes (fun p => Real.sqrt (b p))
      (fun p => Real.sqrt (b p) * g (k - p))
    have e1 : ∑ p ∈ modes, (Real.sqrt (b p)) ^ 2 = ∑ p ∈ modes, b p :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (hbn p)
    have e2 : ∑ p ∈ modes, (Real.sqrt (b p) * g (k - p)) ^ 2
        = ∑ p ∈ modes, b p * (g (k - p)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_pow, Real.sq_sqrt (hbn p)]
    rw [e1, e2] at hcs
    exact hcs
  -- sum in k and use translation invariance
  have hsum : ∑ k ∈ modes, (forcingMajorant modes u k) ^ 2
      ≤ (∑ p ∈ modes, b p) ^ 2 * ∑ m ∈ modes, (g m) ^ 2 := by
    have h1 : ∑ k ∈ modes, (forcingMajorant modes u k) ^ 2
        ≤ ∑ k ∈ modes, (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * (g (k - p)) ^ 2 :=
      Finset.sum_le_sum fun k _ => hpt k
    have h2 : ∑ k ∈ modes, (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * (g (k - p)) ^ 2
        = (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * ∑ k ∈ modes, (g (k - p)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
    have h3 : ∀ p ∈ modes, b p * ∑ k ∈ modes, (g (k - p)) ^ 2
        ≤ b p * ∑ m ∈ modes, (g m) ^ 2 := by
      intro p _
      have hshift : ∑ k ∈ modes, (g (k - p)) ^ 2 ≤ ∑ m ∈ modes, (g m) ^ 2 :=
        sum_translate_le modes (fun m => (g m) ^ 2) (fun m => sq_nonneg _)
          (fun m hm => by show (g m) ^ 2 = 0; rw [hg0 m hm]; ring) (fun k => k - p)
          (fun x y h => by simpa using sub_left_injective h)
      exact mul_le_mul_of_nonneg_left hshift (hbn p)
    have h4 : ∑ p ∈ modes, b p * ∑ k ∈ modes, (g (k - p)) ^ 2
        ≤ ∑ p ∈ modes, b p * ∑ m ∈ modes, (g m) ^ 2 := Finset.sum_le_sum h3
    have hbnn : 0 ≤ ∑ p ∈ modes, b p := Finset.sum_nonneg fun p _ => hbn p
    have h5 : (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * ∑ m ∈ modes, (g m) ^ 2
        = (∑ p ∈ modes, b p) ^ 2 * ∑ m ∈ modes, (g m) ^ 2 := by
      rw [← Finset.sum_mul]; ring
    calc ∑ k ∈ modes, (forcingMajorant modes u k) ^ 2
        ≤ ∑ k ∈ modes, (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * (g (k - p)) ^ 2 := h1
      _ = (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * ∑ k ∈ modes, (g (k - p)) ^ 2 := h2
      _ ≤ (∑ p ∈ modes, b p) * ∑ p ∈ modes, b p * ∑ m ∈ modes, (g m) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 hbnn
      _ = (∑ p ∈ modes, b p) ^ 2 * ∑ m ∈ modes, (g m) ^ 2 := h5
  have hgsum : ∑ m ∈ modes, (g m) ^ 2 = ∑ m ∈ modes, wsq m * nsq (u m) :=
    Finset.sum_congr rfl fun m _ => hsqg m
  have hAnn : 0 ≤ wienerA modes u := wienerA_nonneg _ _
  rw [forcingL2]
  rw [hgsum] at hsum
  calc Real.sqrt (∑ k ∈ modes, (forcingMajorant modes u k) ^ 2)
      ≤ Real.sqrt ((wienerA modes u) ^ 2 * ∑ m ∈ modes, wsq m * nsq (u m)) :=
        Real.sqrt_le_sqrt (by simpa [wienerA, hb_def] using hsum)
    _ = wienerA modes u * wienerH1 modes u := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hAnn, wienerH1]

/-! ## The sharpened pointwise bound -/

theorem forcingMajorant_nonneg (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave) :
    0 ≤ forcingMajorant modes u k :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (nrm_nonneg _) (Real.sqrt_nonneg _)) (nrm_nonneg _)

theorem sqrt_sum_nrm_sq (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    Real.sqrt (∑ k ∈ modes, (nrm (u k)) ^ 2) = wienerL2 modes u := by
  rw [wienerL2]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (nsq_nonneg _)

/-- **Sharpened pointwise bound.**  At each instant the weighted positive
network forcing obeys `∑_τ w_τ (F_τ)₊ ≤ 3 W ‖u‖_A² ‖u‖_2 ‖u‖_{Ḣ¹}`: only two
Wiener factors survive, and the derivative sits in the Dirichlet norm. -/
theorem network_forcing_serrin_bound (G : GalerkinFlow) (w : Wave × Wave × Wave → ℝ)
    {W : ℝ} (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (t : ℝ) :
    ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
      ≤ 3 * W * (wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
        * wienerH1 G.modes (G.u t) := by
  classical
  set n : Wave → ℝ := fun k => nrm (G.u t k) with hn_def
  set FM : Wave → ℝ := fun k =>
    if k ∈ G.modes then forcingMajorant G.modes (G.u t) k else 0 with hFM_def
  have hn0 : ∀ m, 0 ≤ n m := fun m => nrm_nonneg _
  have hFM0 : ∀ m, 0 ≤ FM m := by
    intro m
    by_cases hm : m ∈ G.modes
    · simpa [hFM_def, hm] using forcingMajorant_nonneg G.modes (G.u t) m
    · simp [hFM_def, hm]
  have hnsupp : ∀ m, m ∉ G.modes → n m = 0 := by
    intro m hm
    have : G.u t m = 0 := G.support t m hm
    simp [hn_def, this, nrm, nsq]
  have hFMsupp : ∀ m, m ∉ G.modes → FM m = 0 := by
    intro m hm; simp [hFM_def, hm]
  have hW : 0 ≤ W := le_trans (hw0 (0, 0, 0)) (hwW (0, 0, 0))
  set A := wienerA G.modes (G.u t) with hA
  set L2 := wienerL2 G.modes (G.u t) with hL2
  set H1 := wienerH1 G.modes (G.u t) with hH1
  have hAnn : 0 ≤ A := wienerA_nonneg _ _
  have hL2nn : 0 ≤ L2 := wienerL2_nonneg _ _
  have hH1nn : 0 ≤ H1 := wienerH1_nonneg _ _
  have hnl1 : ∑ p ∈ G.modes, n p = A := rfl
  have hnl2 : Real.sqrt (∑ q ∈ G.modes, (n q) ^ 2) = L2 := sqrt_sum_nrm_sq _ _
  have hFMl2 : Real.sqrt (∑ k ∈ G.modes, (FM k) ^ 2) ≤ A * H1 := by
    have hcongr : ∑ k ∈ G.modes, (FM k) ^ 2
        = ∑ k ∈ G.modes, (forcingMajorant G.modes (G.u t) k) ^ 2 :=
      Finset.sum_congr rfl fun k hk => by simp [hFM_def, hk]
    rw [hcongr]
    exact forcingL2_le G.modes (G.u t) (fun m hm => G.support t m hm)
  -- termwise majorisation
  have hterm : ∀ τ ∈ triads G.modes,
      w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
        ≤ W * (FM τ.1 * n τ.2.1 * n τ.2.2) + W * (n τ.1 * FM τ.2.1 * n τ.2.2)
          + W * (n τ.1 * n τ.2.1 * FM τ.2.2) := by
    intro τ hτ
    obtain ⟨hk, hp, hq, -⟩ := mem_triads hτ
    have hkz := wsq_ne_zero_of_mem G.zero_not_mem hk
    have hpz := wsq_ne_zero_of_mem G.zero_not_mem hp
    have hqz := wsq_ne_zero_of_mem G.zero_not_mem hq
    have hmaj := force3_majorant G τ.1 τ.2.1 τ.2.2 t hkz hpz hqz
    have e1 : FM τ.1 = forcingMajorant G.modes (G.u t) τ.1 := by simp [hFM_def, hk]
    have e2 : FM τ.2.1 = forcingMajorant G.modes (G.u t) τ.2.1 := by simp [hFM_def, hp]
    have e3 : FM τ.2.2 = forcingMajorant G.modes (G.u t) τ.2.2 := by simp [hFM_def, hq]
    have hmax : max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 ≤ |G.force3 τ.1 τ.2.1 τ.2.2 t| :=
      max_le (le_abs_self _) (abs_nonneg _)
    have hnn : 0 ≤ max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := le_max_right _ _
    have hbig : max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
        ≤ FM τ.1 * n τ.2.1 * n τ.2.2 + n τ.1 * FM τ.2.1 * n τ.2.2
          + n τ.1 * n τ.2.1 * FM τ.2.2 := by
      rw [e1, e2, e3, hn_def]
      exact le_trans hmax hmaj
    calc w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
        ≤ W * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0 := mul_le_mul_of_nonneg_right (hwW τ) hnn
      _ ≤ W * (FM τ.1 * n τ.2.1 * n τ.2.2 + n τ.1 * FM τ.2.1 * n τ.2.2
            + n τ.1 * n τ.2.1 * FM τ.2.2) := mul_le_mul_of_nonneg_left hbig hW
      _ = W * (FM τ.1 * n τ.2.1 * n τ.2.2) + W * (n τ.1 * FM τ.2.1 * n τ.2.2)
            + W * (n τ.1 * n τ.2.1 * FM τ.2.2) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  -- the three resonance sums, each with one `ℓ¹` and two `ℓ²` factors
  have t1 : ∑ τ ∈ triads G.modes, FM τ.1 * n τ.2.1 * n τ.2.2 ≤ A * (A * H1) * L2 := by
    have h1 := triads_triple_sum_le G.modes FM n n hFM0 hn0 hn0
    have h2 := double_sum_conv_le G.modes FM n n hn0 hFMsupp
    have h3 : (∑ p ∈ G.modes, n p) * Real.sqrt (∑ k ∈ G.modes, (FM k) ^ 2)
        * Real.sqrt (∑ q ∈ G.modes, (n q) ^ 2) ≤ A * (A * H1) * L2 := by
      rw [hnl1, hnl2]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFMl2 hAnn) hL2nn
    linarith
  have t2 : ∑ τ ∈ triads G.modes, n τ.1 * FM τ.2.1 * n τ.2.2 ≤ A * L2 * (A * H1) := by
    have h1 := triads_triple_sum_le G.modes n FM n hn0 hFM0 hn0
    have h2 := double_sum_conv_le' G.modes n FM n hn0 hnsupp
    have h3 : (∑ q ∈ G.modes, n q) * Real.sqrt (∑ k ∈ G.modes, (n k) ^ 2)
        * Real.sqrt (∑ p ∈ G.modes, (FM p) ^ 2) ≤ A * L2 * (A * H1) := by
      rw [hnl1, hnl2]
      exact mul_le_mul_of_nonneg_left hFMl2 (mul_nonneg hAnn hL2nn)
    linarith
  have t3 : ∑ τ ∈ triads G.modes, n τ.1 * n τ.2.1 * FM τ.2.2 ≤ A * L2 * (A * H1) := by
    have h1 := triads_triple_sum_le G.modes n n FM hn0 hn0 hFM0
    have h2 := double_sum_conv_le G.modes n n FM hn0 hnsupp
    have h3 : (∑ p ∈ G.modes, n p) * Real.sqrt (∑ k ∈ G.modes, (n k) ^ 2)
        * Real.sqrt (∑ q ∈ G.modes, (FM q) ^ 2) ≤ A * L2 * (A * H1) := by
      rw [hnl1, hnl2]
      exact mul_le_mul_of_nonneg_left hFMl2 (mul_nonneg hAnn hL2nn)
    linarith
  have s1 : W * (∑ τ ∈ triads G.modes, FM τ.1 * n τ.2.1 * n τ.2.2) ≤ W * (A * (A * H1) * L2) :=
    mul_le_mul_of_nonneg_left t1 hW
  have s2 : W * (∑ τ ∈ triads G.modes, n τ.1 * FM τ.2.1 * n τ.2.2) ≤ W * (A * L2 * (A * H1)) :=
    mul_le_mul_of_nonneg_left t2 hW
  have s3 : W * (∑ τ ∈ triads G.modes, n τ.1 * n τ.2.1 * FM τ.2.2) ≤ W * (A * L2 * (A * H1)) :=
    mul_le_mul_of_nonneg_left t3 hW
  have hfin : W * (A * (A * H1) * L2) + W * (A * L2 * (A * H1)) + W * (A * L2 * (A * H1))
      = 3 * W * A ^ 2 * L2 * H1 := by ring
  linarith

/-! ## Integrated form and the reduction -/

namespace GalerkinFlow

theorem continuous_nsq_u (G : GalerkinFlow) (k : Wave) :
    Continuous fun t => nsq (G.u t k) :=
  continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (G.continuous_u k i)

theorem continuous_wienerL2 (G : GalerkinFlow) :
    Continuous fun t => wienerL2 G.modes (G.u t) :=
  Real.continuous_sqrt.comp (continuous_finset_sum _ fun k _ => G.continuous_nsq_u k)

theorem continuous_wienerH1 (G : GalerkinFlow) :
    Continuous fun t => wienerH1 G.modes (G.u t) :=
  Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun k _ => continuous_const.mul (G.continuous_nsq_u k))

end GalerkinFlow

/-- **Integrated sharpened bound.** -/
theorem weightedPositiveForcing_le_serrin (G : GalerkinFlow) (w : Wave × Wave × Wave → ℝ)
    {W t₀ t₁ : ℝ} (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (ht : t₀ ≤ t₁) :
    weightedPositiveForcing G w t₀ t₁
      ≤ 3 * W * ∫ t in t₀..t₁, (wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
          * wienerH1 G.modes (G.u t) := by
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
  have hRHS : Continuous fun t => 3 * W * ((wienerA G.modes (G.u t)) ^ 2
      * wienerL2 G.modes (G.u t) * wienerH1 G.modes (G.u t)) :=
    continuous_const.mul
      (((G.continuous_wienerA.pow 2).mul G.continuous_wienerL2).mul G.continuous_wienerH1)
  have hmono : (∫ t in t₀..t₁, ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0)
      ≤ ∫ t in t₀..t₁, 3 * W * ((wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
          * wienerH1 G.modes (G.u t)) := by
    refine intervalIntegral.integral_mono_on ht ?_ (hRHS.intervalIntegrable _ _) ?_
    · exact (continuous_finset_sum _ fun τ _ => hgc τ).intervalIntegrable _ _
    · intro t _
      have h := network_forcing_serrin_bound G w hw0 hwW t
      calc ∑ τ ∈ triads G.modes, w τ * max (G.force3 τ.1 τ.2.1 τ.2.2 t) 0
          ≤ 3 * W * (wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
              * wienerH1 G.modes (G.u t) := h
        _ = 3 * W * ((wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
              * wienerH1 G.modes (G.u t)) := by ring
  rw [hswap, ← intervalIntegral.integral_const_mul]
  exact hmono

/-- The residual input after the sharpened reduction: a truncation-uniform bound
for `∫_0^T ‖u‖_A² ‖u‖_2 ‖u‖_{Ḣ¹} dt`.  Two of its three factors (the energy and
the time-integrated Dirichlet norm) are what the Navier–Stokes energy balance
pays for; the remaining content is the time-integrated *square* of the Wiener
norm, a Serrin-type `L⁴_t` condition. -/
def UniformSerrinWienerExpenditure (nu T : ℝ) : Prop :=
  ∀ u0 : Wave → Fin 3 → ℂ, RapidlyDecaying u0 → ∃ C : ℝ,
    ∀ G : GalerkinFlow, G.nu = nu → (∀ k ∈ G.modes, G.u 0 k = u0 k) →
      (∫ t in (0:ℝ)..T, (wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
        * wienerH1 G.modes (G.u t)) ≤ C

/-- **Sharpened reduction of the Round 105 wall.** -/
theorem budget_of_uniform_serrin_expenditure {nu T W : ℝ} (w : Wave × Wave × Wave → ℝ)
    (hw0 : ∀ τ, 0 ≤ w τ) (hwW : ∀ τ, w τ ≤ W) (hT : 0 ≤ T)
    (H : UniformSerrinWienerExpenditure nu T) :
    PhysicalWeightedPositiveWaleffeNetworkForcingBudget nu T w := by
  intro u0 hu0
  obtain ⟨C, hC⟩ := H u0 hu0
  have hW : 0 ≤ W := le_trans (hw0 (0, 0, 0)) (hwW (0, 0, 0))
  refine ⟨3 * W * C, fun G hnu hinit => ?_⟩
  have h1 := weightedPositiveForcing_le_serrin G w hw0 hwW hT
  have h2 := hC G hnu hinit
  have h3 : 3 * W * (∫ t in (0:ℝ)..T, (wienerA G.modes (G.u t)) ^ 2 * wienerL2 G.modes (G.u t)
        * wienerH1 G.modes (G.u t)) ≤ 3 * W * C :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

end ClayNS.Waleffe
