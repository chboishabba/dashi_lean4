/-
# Charging the logarithmic scale loss to the scale-Gram expenditure

`BackwardKernelFluxDefect.lean` identifies the Navier–Stokes logarithmic defect
density read off the exact scale-derivative identity,

  `D_NS(r) = [F(r)]_+ / (r·𝒟(r))`,          (`ClayNS.nsLogDefect`)

and proves that a *uniform* bound on its total mass across the cascade range,
`Φ(b) − Φ(a) ≤ C`, gives `A_dyn` with the scale-independent constant `e^{−C}`.
What was missing is a mechanism producing that bound: the naive size estimate
costs a power of `M`.

This file supplies the **assembly** of the route the scale-Gram construction
opens: charge the positive part of the flux to the scale-generator expenditure
and a remainder,

  `[F(r)]_+ ≤ C_G·𝒢(r) + ℛ(r)`,          (`hFG` below)

use the probe coercivity of `PositiveParabolicEnergyScaleProbe.lean`,

  `c_*·𝒢(r) ≤ Δ_scale(r)`,               (`hcoer` below)

and then pay both pieces telescopically:

  `∫_a^b Δ_scale(r)/(r𝒟(r)) dr ≤ C_*`,   `∫_a^b ℛ(r)/(r𝒟(r)) dr ≤ C_rem`.

* `ClayNS.le_of_hasDerivAt_nonneg_on_Icc` — the calculus step: a nonnegative
  derivative on a closed interval makes the function increase across it;
* `ClayNS.scaleCharge_split_of_coercivity` — the coercivity converts the
  `𝒢`-splitting into a `Δ_scale`-splitting with constant `C_G/c_*`;
* `ClayNS.nsLogDefect_total_le_of_scaleGram_absorption` — **the charge**: the
  total logarithmic defect is at most `(C_G/c_*)·C_* + C_rem`, with no power of
  the scale range;
* `ClayNS.backward_kernel_defect_of_scaleGram_absorption` — the resulting
  bottom-scale bound;
* `ClayNS.clay_A_dyn_of_scaleGram_absorption` — **`A-charge` ⟹ `A_dyn`**, with
  the constants uniform along the singular sequence.

What is *not* proved here is the pair of analytic inputs `hFG` (the flux
splitting) and `hstar` (the telescopic payment of the scale-Gram expenditure);
they enter every statement below as explicit hypotheses.  Together they are the
theorem the plan calls `NavierStokesGaussianScaleCharge`, and they are the
remaining wall on the A side.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.BackwardKernelFluxDefect

open Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The calculus step -/

/-- A function with a nonnegative derivative at every point of a closed interval
increases across it. -/
theorem le_of_hasDerivAt_nonneg_on_Icc {H H' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r)
    (hnn : ∀ r ∈ Icc a b, 0 ≤ H' r) : H a ≤ H b := by
  have hcont : ContinuousOn H (Icc a b) := fun r hr =>
    ((hderiv r hr).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ interior (Icc a b), HasDerivAt H (H' r) r := fun r hr =>
    hderiv r (interior_subset hr)
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
    (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  · intro r hr
    exact ((hd r hr).differentiableAt).differentiableWithinAt
  · intro r hr
    rw [(hd r hr).deriv]
    exact hnn r (interior_subset hr)

/-! ## The coercivity converts a `𝒢`-splitting into a `Δ_scale`-splitting -/

/-- **From scale-generator cost to scale-Gram defect.**  If the positive part of
the flux is charged to the scale-generator cost `𝒢` and a remainder, and the
probe coercivity `c_*·𝒢 ≤ Δ_scale` holds, then the flux is charged to the
scale-Gram defect with constant `C_G/c_*`. -/
theorem scaleCharge_split_of_coercivity {F Gcal Delta Rem : ℝ → ℝ} {a b CG cstar : ℝ}
    (hCG : 0 ≤ CG) (hcstar : 0 < cstar)
    (hFG : ∀ r ∈ Icc a b, max (F r) 0 ≤ CG * Gcal r + Rem r)
    (hcoer : ∀ r ∈ Icc a b, cstar * Gcal r ≤ Delta r) :
    ∀ r ∈ Icc a b, max (F r) 0 ≤ (CG / cstar) * Delta r + Rem r := by
  intro r hr
  have h1 : CG * Gcal r ≤ (CG / cstar) * Delta r := by
    have h2 : (CG / cstar) * (cstar * Gcal r) ≤ (CG / cstar) * Delta r :=
      mul_le_mul_of_nonneg_left (hcoer r hr) (by positivity)
    have h3 : (CG / cstar) * (cstar * Gcal r) = CG * Gcal r := by
      field_simp
    linarith [h2, h3]
  linarith [hFG r hr]

/-! ## The charge -/

/-- **The logarithmic scale loss charged to the scale-Gram expenditure.**  If

* the positive part of the flux is charged pointwise,
  `[F(r)]_+ ≤ c⁻¹·Δ_scale(r) + ℛ(r)`,
* the scale-Gram expenditure is paid telescopically,
  `∫_a^b Δ_scale/(r𝒟) ≤ C_*` (as `Ψ(b) − Ψ(a) ≤ C_*` for a primitive `Ψ`),
* the remainder is paid, `∫_a^b ℛ/(r𝒟) ≤ C_rem`,

then the total Navier–Stokes logarithmic defect obeys

  `Φ(b) − Φ(a) ≤ c⁻¹·C_* + C_rem`,

with no power of the scale range `[a,b]`.  This is exactly the input
`ClayNS.backward_kernel_flux_defect_integrable` consumes. -/
theorem nsLogDefect_total_le_of_scaleGram_absorption
    {F Dsc Delta Rem Phi Psi Theta : ℝ → ℝ} {a b cinv Cstar Crem : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcinv : 0 ≤ cinv)
    (hD : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hsplit : ∀ r ∈ Icc a b, max (F r) 0 ≤ cinv * Delta r + Rem r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (nsLogDefect F Dsc r) r)
    (hPsi : ∀ r ∈ Icc a b, HasDerivAt Psi (Delta r / (r * Dsc r)) r)
    (hTheta : ∀ r ∈ Icc a b, HasDerivAt Theta (Rem r / (r * Dsc r)) r)
    (hstar : Psi b - Psi a ≤ Cstar) (hrem : Theta b - Theta a ≤ Crem) :
    Phi b - Phi a ≤ cinv * Cstar + Crem := by
  set H : ℝ → ℝ := fun r => cinv * Psi r + Theta r - Phi r with hH
  set H' : ℝ → ℝ := fun r =>
    cinv * (Delta r / (r * Dsc r)) + Rem r / (r * Dsc r) - nsLogDefect F Dsc r with hH'
  have hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r := fun r hr =>
    (((hPsi r hr).const_mul cinv).add (hTheta r hr)).sub (hPhi r hr)
  have hnn : ∀ r ∈ Icc a b, 0 ≤ H' r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have hrd : 0 < r * Dsc r := mul_pos hr0 (hD r hr)
    have hval : H' r = (cinv * Delta r + Rem r - max (F r) 0) / (r * Dsc r) := by
      simp only [hH', nsLogDefect]
      field_simp
    rw [hval]
    exact div_nonneg (by linarith [hsplit r hr]) hrd.le
  have hmain : H a ≤ H b := le_of_hasDerivAt_nonneg_on_Icc hab hderiv hnn
  have hexp : cinv * Psi a + Theta a - Phi a ≤ cinv * Psi b + Theta b - Phi b := hmain
  have hPsile : cinv * (Psi b - Psi a) ≤ cinv * Cstar :=
    mul_le_mul_of_nonneg_left hstar hcinv
  linarith [hexp, hPsile, hrem]

/-- **The bottom-scale defect produced by the scale charge.** -/
theorem backward_kernel_defect_of_scaleGram_absorption
    {F Dsc Dd Delta Rem Phi Psi Theta : ℝ → ℝ} {a b eps cinv Cstar Crem : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (heps : 0 ≤ eps) (hcinv : 0 ≤ cinv)
    (hD : ∀ r ∈ Icc a b, 0 < Dsc r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt Dsc (Dd r) r)
    (hexact : ∀ r ∈ Icc a b, r * Dd r = F r)
    (hsplit : ∀ r ∈ Icc a b, max (F r) 0 ≤ cinv * Delta r + Rem r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (nsLogDefect F Dsc r) r)
    (hPsi : ∀ r ∈ Icc a b, HasDerivAt Psi (Delta r / (r * Dsc r)) r)
    (hTheta : ∀ r ∈ Icc a b, HasDerivAt Theta (Rem r / (r * Dsc r)) r)
    (hstar : Psi b - Psi a ≤ Cstar) (hrem : Theta b - Theta a ≤ Crem)
    (hstart : eps ≤ Dsc b) :
    Real.exp (-(cinv * Cstar + Crem)) * eps ≤ Dsc a :=
  backward_kernel_flux_defect_integrable ha hab heps hD hderiv hPhi hexact
    (nsLogDefect_total_le_of_scaleGram_absorption ha hab hcinv hD hsplit hPhi hPsi hTheta
      hstar hrem)
    hstart

/-! ## `A-charge` ⟹ `A_dyn` -/

/-- **The A arrow, assembled.**  Along a singular sequence, if on each cascade
range the exact scale-derivative identity holds, the positive part of the flux
is charged to the scale-Gram defect with a constant `c⁻¹` independent of `k`,
and both the scale-Gram expenditure and the remainder are paid with constants
`C_*`, `C_rem` independent of `k`, then the velocity-scale defect gate `A_dyn`
holds. -/
theorem clay_A_dyn_of_scaleGram_absorption {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ}
    {t : ℕ → ℝ} {x : ℕ → E3} {F Qd Delta Rem Phi Psi Theta : ℕ → ℝ → ℝ}
    {eps cinv Cstar Crem : ℝ}
    (heps : 0 < eps) (hM : ∀ k, 0 < M k) (hcinv : 0 ≤ cinv)
    (hle : ∀ k, 1 / M k ≤ cascadeStart (M k))
    (hpos : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), 0 < QgradCyl (G k) (t k) (x k) r)
    (hderiv : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (fun s => QgradCyl (G k) (t k) (x k) s) (Qd k r) r)
    (hexact : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), r * Qd k r = F k r)
    (hsplit : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      max (F k r) 0 ≤ cinv * Delta k r + Rem k r)
    (hPhi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Phi k) (nsLogDefect (F k) (fun s => QgradCyl (G k) (t k) (x k) s) r) r)
    (hPsi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Psi k) (Delta k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hTheta : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Theta k) (Rem k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hstar : ∀ k, Psi k (cascadeStart (M k)) - Psi k (1 / M k) ≤ Cstar)
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  refine clay_A_dyn_of_uniform_log_defect (C := cinv * Cstar + Crem) heps hM hle hpos hderiv
    hPhi hexact (fun k => ?_) hstart
  have hak : (0 : ℝ) < 1 / M k := by have := hM k; positivity
  exact nsLogDefect_total_le_of_scaleGram_absorption hak (hle k) hcinv (hpos k) (hsplit k)
    (hPhi k) (hPsi k) (hTheta k) (hstar k) (hrem k)

end ClayNS
