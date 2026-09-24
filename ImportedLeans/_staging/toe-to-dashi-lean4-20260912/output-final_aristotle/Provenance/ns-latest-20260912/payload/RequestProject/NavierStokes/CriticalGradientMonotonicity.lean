/-
# The exact logarithmic-derivative identity for `Q_∇` (the `A₁` template)

The A-side frontier is `NSCriticalGradientAlmostMonotonicity`: a bound

  `r·Q_∇'(r) ≤ r·D(r)·Q_∇(r)`,   `∫_{1/M}^{M^{-2/3}} D(r) dr ≤ E_*`

with `E_*` uniform along the singular sequence.  `FrequencyAlmostMonotone.lean`
already proves that such a bound propagates the defect with the *single* factor
`e^{-E_*}` (critical exponent `p = 0`), and `OneStepDyadicNoGo.lean` proves that
no purely kinematic one-step inequality can exist.  This file supplies the first
step of the Lin/CKN template for the **actual** quantity

  `Q_∇(r) = r⁻¹ ∫_{t₀-r²}^{t₀} ∫_{B_r(x₀)} G`,   `G = |∇u|²`,

namely the exact differentiation identity, and then audits the only bound on the
total defect that is available without a Navier–Stokes cancellation.

## What is proved here

* `ClayNS.cylEnergy` — the *un-normalized* cylinder dissipation
  `E(r) = ∫_{t₀-r²}^{t₀}∫_{B_r(x₀)} G`, so that `Q_∇ = r⁻¹E`.
* `ClayNS.hasDerivAt_QgradCyl_of_cylEnergy` and
  `ClayNS.rmul_QgradCylDeriv` — **the identity**

  `r·Q_∇'(r) = E'(r) − Q_∇(r)`.

  This is exactly the shape the frequency machinery consumes: the logarithmic
  derivative of the scale-invariant quantity is the *growth rate of the raw
  cylinder dissipation* minus the quantity itself.  No radial-boundary or
  bottom-time term is discarded — they are precisely the two contributions to
  `E'(r)`.
* `ClayNS.critical_frequency_of_dissipation_growth` — consequently the
  almost-monotonicity bound `r·Q_∇' ≤ r·D·Q_∇` is *equivalent* to the
  dissipation-growth bound `E'(r) ≤ (1 + r·D(r))·Q_∇(r)`.  This is the precise
  analytic statement `A₁` has to establish.
* `ClayNS.defect_propagates_of_dissipation_growth` — feeding it into the
  already-proved almost-monotonicity theorem.
* `ClayNS.totalDefect_le_of_dissipation` — the only bound on `∫D` available from
  size information alone: with `Q_∇ ≥ ε` on `[a,b]`,
  `∫_a^b D ≤ (E(b) − E(a))/(a·ε)`.
* `ClayNS.naive_defect_bound_degenerates` — **and it is not enough.**  At the
  cascade endpoints `a = 1/M`, `b ≍ M^{-2/3}` with `E(b) = b·Q_∇(b) ≍ b·ε`, that
  bound is `≍ M^{1/3} → ∞`.  So the total defect *cannot* be obtained by
  estimating `E'` by its size; `A₁` must exhibit a genuine cancellation in the
  local energy identity.  This is the exact residual gap, stated quantitatively.

`A₁` itself is **not** proved here, and the file makes no claim that it is.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FrequencyAlmostMonotone

open Filter Topology Set MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The un-normalized cylinder dissipation -/

/-- The raw (un-normalized) parabolic-cylinder integral
`E(r) = ∫_{t₀-r²}^{t₀} ∫_{B_r(x₀)} G`.  The scale-invariant quantity is
`Q_∇(r) = r⁻¹E(r)`. -/
def cylEnergy (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (r : ℝ) : ℝ :=
  ∫ s in (t0 - r ^ 2)..t0, ∫ y in Metric.ball x0 r, G s y

lemma QgradCyl_eq_inv_mul_cylEnergy (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (r : ℝ) :
    QgradCyl G t0 x0 r = r⁻¹ * cylEnergy G t0 x0 r := rfl

/-- The derivative of `Q_∇` expressed through the derivative `Ed` of the raw
cylinder dissipation. -/
def QgradCylDeriv (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (Ed : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(r ^ 2)⁻¹ * cylEnergy G t0 x0 r + r⁻¹ * Ed r

/-! ## The differentiation identity -/

/-- **Differentiating the scale-invariant gradient energy.**  If the raw
cylinder dissipation is differentiable at `r ≠ 0`, so is `Q_∇`. -/
theorem hasDerivAt_QgradCyl_of_cylEnergy (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {Ed : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hE : HasDerivAt (cylEnergy G t0 x0) (Ed r) r) :
    HasDerivAt (QgradCyl G t0 x0) (QgradCylDeriv G t0 x0 Ed r) r := by
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  simpa [QgradCylDeriv, QgradCyl_eq_inv_mul_cylEnergy] using hinv.mul hE

/-- **The exact logarithmic-derivative identity.**

`r·Q_∇'(r) = E'(r) − Q_∇(r)`.

The left-hand side is the logarithmic defect the cascade consumes; the
right-hand side collects *both* the radial-boundary and the bottom-time
contributions into the single derivative of the raw cylinder dissipation, with
nothing discarded. -/
theorem rmul_QgradCylDeriv (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (Ed : ℝ → ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    r * QgradCylDeriv G t0 x0 Ed r = Ed r - QgradCyl G t0 x0 r := by
  have h2 : (r : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [QgradCylDeriv, QgradCyl_eq_inv_mul_cylEnergy]
  field_simp
  ring

/-- **The `A₁` statement is exactly a dissipation-growth bound.**  For the actual
`Q_∇`, the almost-monotonicity inequality `r·Q_∇'(r) ≤ r·D(r)·Q_∇(r)` holds
precisely when the raw cylinder dissipation grows no faster than
`(1 + r·D(r))·Q_∇(r)`. -/
theorem critical_frequency_of_dissipation_growth (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {Ed D : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hgrowth : Ed r ≤ (1 + r * D r) * QgradCyl G t0 x0 r) :
    r * QgradCylDeriv G t0 x0 Ed r ≤ r * D r * QgradCyl G t0 x0 r := by
  rw [rmul_QgradCylDeriv G t0 x0 Ed hr]
  nlinarith [hgrowth]

/-- Conversely the dissipation-growth bound is *necessary*. -/
theorem dissipation_growth_of_critical_frequency (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {Ed D : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hfreq : r * QgradCylDeriv G t0 x0 Ed r ≤ r * D r * QgradCyl G t0 x0 r) :
    Ed r ≤ (1 + r * D r) * QgradCyl G t0 x0 r := by
  rw [rmul_QgradCylDeriv G t0 x0 Ed hr] at hfreq
  nlinarith [hfreq]

/-! ## Feeding the almost-monotonicity machinery -/

/-- **The defect propagates once the dissipation-growth bound is available.**
This is the exact conditional form of `A₁`: the growth bound on `E'` over the
scale range, with total defect `Φ(b) − Φ(a)`, moves the defect from the energy
scale `b` down to the velocity scale `a` with the single factor
`e^{−(Φ(b)−Φ(a))}`. -/
theorem defect_propagates_of_dissipation_growth (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {Ed D Phi : ℝ → ℝ} {a b eps : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 < QgradCyl G t0 x0 r)
    (hE : ∀ r ∈ Icc a b, HasDerivAt (cylEnergy G t0 x0) (Ed r) r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (D r) r)
    (hgrowth : ∀ r ∈ Icc a b, Ed r ≤ (1 + r * D r) * QgradCyl G t0 x0 r)
    (hstart : eps ≤ QgradCyl G t0 x0 b) :
    Real.exp (-(Phi b - Phi a)) * eps ≤ QgradCyl G t0 x0 a := by
  have hrne : ∀ r ∈ Icc a b, r ≠ 0 := fun r hr => ne_of_gt (lt_of_lt_of_le ha hr.1)
  exact almostMonotone_defect_propagates (H := QgradCyl G t0 x0)
    (H' := QgradCylDeriv G t0 x0 Ed) ha hab hpos
    (fun r hr => hasDerivAt_QgradCyl_of_cylEnergy G t0 x0 (hrne r hr) (hE r hr))
    hPhi
    (fun r hr => critical_frequency_of_dissipation_growth G t0 x0 (hrne r hr) (hgrowth r hr))
    hstart

/-! ## The size-only bound on the total defect, and why it is insufficient -/

/-- **The total defect controlled by the raw dissipation.**  If the defect
density is taken in the crude form `D = E'/(r·Q_∇)` and `Q_∇ ≥ ε > 0` on the
range, then the total defect is at most `(∫E')/(a·ε)`.  Together with the
fundamental theorem of calculus this is `(E(b) − E(a))/(a·ε)`. -/
theorem totalDefect_le_of_dissipation {Ed Q D : ℝ → ℝ} {a b eps : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (heps : 0 < eps)
    (hQ : ∀ r ∈ Icc a b, eps ≤ Q r)
    (hEd0 : ∀ r ∈ Icc a b, 0 ≤ Ed r)
    (hDdef : ∀ r ∈ Icc a b, D r = Ed r / (r * Q r))
    (hDint : IntervalIntegrable D volume a b)
    (hEint : IntervalIntegrable Ed volume a b) :
    (∫ r in a..b, D r) ≤ (∫ r in a..b, Ed r) / (a * eps) := by
  have hae : (∫ r in a..b, Ed r) / (a * eps) = ∫ r in a..b, Ed r / (a * eps) := by
    rw [intervalIntegral.integral_div]
  rw [hae]
  refine intervalIntegral.integral_mono_on hab hDint (hEint.div_const _) ?_
  intro r hr
  have hrmem : r ∈ Icc a b := hr
  have hra : a ≤ r := hr.1
  have hrpos : 0 < r := lt_of_lt_of_le ha hra
  have hQr : eps ≤ Q r := hQ r hrmem
  have hQpos : 0 < Q r := lt_of_lt_of_le heps hQr
  have hEd : 0 ≤ Ed r := hEd0 r hrmem
  rw [hDdef r hrmem]
  refine div_le_div_of_nonneg_left hEd (by positivity) ?_
  nlinarith [hra, hQr, heps, ha]

/-- **The size-only bound degenerates.**  At the cascade endpoints `a = 1/M`
and `b = M^{-2/3}`, with the raw dissipation of its expected size
`E(b) = b·Q_∇(b) = b·ε`, the bound of `totalDefect_le_of_dissipation` equals
`M^{1/3}`, which tends to infinity.  Hence no uniform `E_*` can be extracted by
estimating `E'` by its size: `A₁` must use a cancellation in the Navier–Stokes
local energy identity. -/
theorem naive_defect_bound_degenerates {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun M : ℝ => (M ^ (-(2 : ℝ) / 3) * eps) / ((1 / M) * eps)) atTop atTop := by
  have hev : (fun M : ℝ => (M ^ (-(2 : ℝ) / 3) * eps) / ((1 / M) * eps))
      =ᶠ[atTop] fun M : ℝ => M ^ ((1 : ℝ) / 3) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    have hMne : M ≠ 0 := ne_of_gt hM
    have hpow : M ^ (-(2 : ℝ) / 3) * M = M ^ ((1 : ℝ) / 3) := by
      nth_rewrite 2 [← Real.rpow_one M]
      rw [← Real.rpow_add hM]
      norm_num
    have hcancel : (M ^ (-(2 : ℝ) / 3) * eps) / ((1 / M) * eps)
        = M ^ (-(2 : ℝ) / 3) * M := by field_simp
    rw [hcancel, hpow]
  exact Tendsto.congr' hev.symm (tendsto_rpow_atTop (by norm_num))

end ClayNS
