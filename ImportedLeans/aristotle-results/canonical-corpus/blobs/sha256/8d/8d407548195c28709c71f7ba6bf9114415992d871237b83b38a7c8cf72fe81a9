/-
# The velocity-scale defect gate `A_dyn`, stated exactly

`RequestProject/NavierStokes/ScaleInvariantGradientEnergy.lean` proves the
scale bookkeeping around the scale-invariant cylinder gradient energy

`Q_∇(G; x₀, t₀, r) = r⁻¹ ∫_{t₀-r²}^{t₀} ∫_{B_r(x₀)} G`,

in particular that a physical defect at the *velocity scale* `r = M⁻¹` is
literally a unit-scale defect for the KNSŠ-rescaled field.  This file states
the remaining dynamical gate itself — the hypothesis that a singular sequence
forces such a defect at the velocity scale `r = c/M_k` — and proves the two
implications that make it exactly the missing input:

* `ClayNS.unit_scale_defect_of_dynamicDefect` — the gate gives a uniform
  unit-scale gradient-energy defect for the rescaled fields, which is what the
  blow-up/contradiction machinery consumes;
* `ClayNS.unit_scale_flat_of_velocity_scale_flat` — the exact contrapositive:
  if the velocity-scale gradient energy tends to zero along the sequence, then
  the rescaled unit cylinders are asymptotically gradient-flat.

So the gate is neither more nor less than the assertion that the singular
dynamics push the Caffarelli–Kohn–Nirenberg defect all the way down to the
velocity scale `r ≍ M⁻¹`; the scaling bookkeeping around it is complete.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleInvariantGradientEnergy

open Filter Topology

noncomputable section

namespace ClayNS

/-- **The velocity-scale defect gate `A_dyn`.**  Along the singular sequence
`(x_k, t_k)` with velocity scale `M_k = ‖u(t_k)‖_∞ → ∞`, the scale-invariant
gradient energy stays bounded below on the cylinder of radius `c/M_k`, for some
fixed `c > 0`. -/
def DynamicVelocityScaleDefect (G : ℕ → ℝ → E3 → ℝ) (M : ℕ → ℝ) (t : ℕ → ℝ) (x : ℕ → E3) :
    Prop :=
  ∃ c > 0, ∃ eps > 0, ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (c / M k)

/-- The rescaling used by the gate: the KNSŠ rescaling at velocity scale
`M_k/c`, whose unit cylinder is the physical cylinder of radius `c/M_k`. -/
lemma inv_div (c : ℝ) {M : ℝ} (hM : 0 < M) (hc : 0 < c) : (M / c)⁻¹ = c / M := by
  field_simp

/-- **The gate delivers a uniform unit-scale defect.**  If the velocity-scale
defect holds, then the rescaled fields carry a unit-scale gradient-energy
defect with the same constant — which is exactly the constant-excluding input
that the ancient blow-up argument consumes. -/
theorem unit_scale_defect_of_dynamicDefect {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ}
    {x : ℕ → E3} (hM : ∀ k, 0 < M k)
    (hA : DynamicVelocityScaleDefect G M t x) :
    ∃ c > 0, ∃ eps > 0, ∀ k,
      eps ≤ QgradCyl (blowupDensity (G k) (M k / c) (t k) (x k)) 0 0 1 := by
  obtain ⟨c, hc, eps, heps, hk⟩ := hA
  refine ⟨c, hc, eps, heps, fun k => ?_⟩
  have hMc : 0 < M k / c := div_pos (hM k) hc
  refine unit_scale_defect_of_velocity_scale_defect (G k) hMc (t k) (x k) ?_
  rw [inv_div c (hM k) hc]
  exact hk k

/-- **The exact contrapositive of the gate.**  If the physical gradient energy
at the velocity scale `c/M_k` tends to zero, then the unit cylinders of the
rescaled fields become gradient-flat.  This is the precise sense in which
"`A_dyn` fails" means "the rescaled unit cylinder carries no gradient": any
further progress has to come from the Navier–Stokes dynamics near the singular
time, not from the scaling. -/
theorem unit_scale_flat_of_velocity_scale_flat {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ}
    {x : ℕ → E3} {c : ℝ} (hM : ∀ k, 0 < M k) (hc : 0 < c)
    (hflat : Tendsto (fun k => QgradCyl (G k) (t k) (x k) (c / M k)) atTop (𝓝 0)) :
    Tendsto (fun k => QgradCyl (blowupDensity (G k) (M k / c) (t k) (x k)) 0 0 1)
      atTop (𝓝 0) := by
  refine hflat.congr fun k => ?_
  have hMc : 0 < M k / c := div_pos (hM k) hc
  rw [QgradCyl_blowupDensity (G k) hMc (t k) (x k), inv_div c (hM k) hc]

end ClayNS
