/-
# What a velocity-scale defect costs: `Q_∇ ≤ A·r⁴`

The cascade calculus (`DyadicCascade.lean`) reduces `A_dyn` to a statement about
how the scale-invariant gradient energy

`Q_∇(G; x₀, t₀, r) = r⁻¹ ∫_{t₀−r²}^{t₀} ∫_{B_r(x₀)} G`

behaves as the radius shrinks.  This file records the elementary but decisive
bound in the other direction: if the density is bounded by `A` on the cylinder,
then

`Q_∇ ≤ A·|B₁|·r⁴`.

Two consequences are proved.

* `ClayNS.QgradCyl_le_of_bounded` — the bound itself.  In particular `Q_∇ → 0`
  as `r → 0` for any field with locally bounded gradient: the desired
  monotonicity of `r ↦ Q_∇(r)` (the zero-loss form of `A_cascade`,
  `ClayNS.ScaleMonotonicityGate`) is **false for regular fields**, so any proof
  of it must consume the Navier–Stokes dynamics near the singularity.  This is
  the `A`-side analogue of the sparse-island no-go on the `C` side.
* `ClayNS.sup_gradient_ge_of_velocityScale_defect` — the quantitative content of
  `A_dyn`: a defect `ε ≤ Q_∇(|∇u|²; x, t, 1/M)` at the velocity scale forces
  `sup |∇u|² ≥ ε·M⁴/|B₁|` on that cylinder, i.e. `|∇u| ≳ M²`.  This is exactly
  the KNSŠ scaling `‖∇u‖ ≍ ‖u‖²`, and it shows the gate is scale-consistent:
  it demands no more than the blow-up rate the rescaling predicts.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.EnergyScaleDefect
import RequestProject.NavierStokes.ScaleInvariantGradientEnergy

open MeasureTheory Metric Set

noncomputable section

namespace ClayNS

/-- **The `r⁴` bound.**  A density bounded by `A` on the parabolic cylinder has
scale-invariant gradient energy at most `A·|B₁|·r⁴`. -/
theorem QgradCyl_le_of_bounded (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) {r A : ℝ}
    (hr : 0 < r)
    (hint : ∀ s, IntegrableOn (G s) (ball x0 r) volume)
    (hintt : IntervalIntegrable (fun s => ∫ y in ball x0 r, G s y) volume (t0 - r ^ 2) t0)
    (hbd : ∀ s ∈ Icc (t0 - r ^ 2) t0, ∀ y ∈ ball x0 r, G s y ≤ A) :
    QgradCyl G t0 x0 r ≤ A * unitBallVol * r ^ 4 := by
  have hballfin : volume (ball x0 r) < ⊤ := measure_ball_lt_top
  have hconstint : IntegrableOn (fun _ : E3 => A) (ball x0 r) volume :=
    integrableOn_const (μ := volume) (s := ball x0 r) (C := A) hballfin.ne
  -- the spatial bound, at each time
  have hspace : ∀ s ∈ Icc (t0 - r ^ 2) t0,
      (∫ y in ball x0 r, G s y) ≤ A * (r ^ 3 * unitBallVol) := by
    intro s hs
    have hmono : (∫ y in ball x0 r, G s y) ≤ ∫ _y in ball x0 r, A :=
      setIntegral_mono_on (hint s) hconstint measurableSet_ball (fun y hy => hbd s hs y hy)
    have hconst : (∫ _y in ball x0 r, A) = (volume (ball x0 r)).toReal * A := by
      rw [setIntegral_const, smul_eq_mul]
      rfl
    rw [hconst, volume_ball_toReal x0 hr.le] at hmono
    linarith [hmono]
  -- integrate in time
  have hab : t0 - r ^ 2 ≤ t0 := by nlinarith
  have htime : (∫ s in (t0 - r ^ 2)..t0, ∫ y in ball x0 r, G s y)
      ≤ r ^ 2 * (A * (r ^ 3 * unitBallVol)) := by
    have hmono := intervalIntegral.integral_mono_on hab hintt
      (intervalIntegrable_const (c := A * (r ^ 3 * unitBallVol))) hspace
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have : t0 - (t0 - r ^ 2) = r ^ 2 := by ring
    rw [this] at hmono
    exact hmono
  have hrinv : (0:ℝ) < r⁻¹ := inv_pos.mpr hr
  have := mul_le_mul_of_nonneg_left htime hrinv.le
  calc QgradCyl G t0 x0 r
      = r⁻¹ * ∫ s in (t0 - r ^ 2)..t0, ∫ y in ball x0 r, G s y := rfl
    _ ≤ r⁻¹ * (r ^ 2 * (A * (r ^ 3 * unitBallVol))) := this
    _ = A * unitBallVol * r ^ 4 := by field_simp

/-- **The quantitative content of `A_dyn`.**  A defect at the velocity scale
`r = 1/M` forces the gradient density to reach `ε·M⁴/|B₁|` on the cylinder:
`|∇u| ≳ M²`, exactly the KNSŠ rate. -/
theorem sup_gradient_ge_of_velocityScale_defect (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {M A eps : ℝ} (hM : 0 < M)
    (hint : ∀ s, IntegrableOn (G s) (ball x0 (1 / M)) volume)
    (hintt : IntervalIntegrable (fun s => ∫ y in ball x0 (1 / M), G s y) volume
      (t0 - (1 / M) ^ 2) t0)
    (hbd : ∀ s ∈ Icc (t0 - (1 / M) ^ 2) t0, ∀ y ∈ ball x0 (1 / M), G s y ≤ A)
    (hdef : eps ≤ QgradCyl G t0 x0 (1 / M)) :
    eps * M ^ 4 ≤ A * unitBallVol := by
  have hr : 0 < 1 / M := by positivity
  have hle := QgradCyl_le_of_bounded G t0 x0 hr hint hintt hbd
  have h1 : eps ≤ A * unitBallVol * (1 / M) ^ 4 := le_trans hdef hle
  have hM4 : (0:ℝ) < M ^ 4 := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1 hM4.le
  have h3 : A * unitBallVol * (1 / M) ^ 4 * M ^ 4 = A * unitBallVol := by
    field_simp
  rw [h3] at h2
  exact h2

end ClayNS
