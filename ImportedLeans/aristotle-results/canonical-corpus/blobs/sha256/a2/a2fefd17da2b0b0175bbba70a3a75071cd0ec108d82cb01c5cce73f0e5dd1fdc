# The revised blow-up route: defect (R1) + oscillation rigidity (R2)

This note records what is now formalized in Lean for the revised route

```
singularity  ⇒  bounded ancient whole-space limit carrying a
                constant-excluding defect  ⇒  ⊥
```

and states precisely which theorems remain open.  Everything referred to below
is proved without `sorry`, without postulates and with no axioms beyond
Lean/Mathlib's `propext`, `Classical.choice`, `Quot.sound`.

## Files

| file | content |
|---|---|
| `RequestProject/NavierStokes/BlowupOscillation.lean` | oscillation, the KNSŠ rescaling, the scale identities, the derivative package, defect stability under uniform limits, expanding-lattice periodicity |
| `RequestProject/NavierStokes/ScaleInvariantGradientEnergy.lean` | the scale-invariant cylinder gradient energy `Q_∇` and its KNSŠ-scale identity |
| `RequestProject/NavierStokes/AncientOscillationContraction.lean` | the oscillation-contraction iteration (D), the assembled route, increments, vanishing-mean rigidity, the `λ_k A_k` no-go |
| `RequestProject/NavierStokes/LocalizedPoincare.lean` | the localized Poincaré inequality at scale `L`, constant `3L²` |
| `RequestProject/NavierStokes/Increments.lean` | the exact PDE satisfied by `δ_h u` |

## §1–§3 — the defect is oscillation, and R1 is an original-scale statement

`oscOn f S` is `sup_{x,y∈S} ‖f x − f y‖` (the diameter of the image).  It is
invariant under `U ↦ U + b` (`oscOn_add_const`), so it is a legitimate
Galilean/constant-excluding quantity, and it vanishes on constants
(`oscOn_const`).

For the KNSŠ rescaling `u_M(y) = M⁻¹ u(x₀ + M⁻¹ y)` (`blowupSpace`):

* `oscOn_blowupSpace`:  `osc_{B_R} u_M = M⁻¹ · osc_{B_{R/M}(x₀)} u`  — this is
  the boxed identity of §2;
* `oscOn_blowupSpace_ge_iff`:  therefore the unit-scale defect
  `osc_{B_R} u_M ≥ c` is *equivalent* to the physical inequality
  `osc_{B_{R/M}(x₀)} u ≥ c·M`, which is the concrete statement (1) of §2;
* `flatMax_iff` and `tendsto_blowup_sub_center_of_flat`: the negation
  ("asymptotically flat velocity maximum") is exactly the vanishing of the
  rescaled oscillation, and on a flat maximum the rescaled fields converge to
  their own centre value uniformly on balls, i.e. locally to a constant.

So R1-osc has been reduced, with no loss, to an inequality about the physical
solution at the velocity scale.  The inequality itself is **not** proved: this
is target **A**.

## §4 — the derivative package

* `norm_fderiv_blowupSpace` / `one_le_norm_fderiv_blowupSpace_iff`: the scaling
  audit, `‖∇u_M(y)‖ = M⁻²‖∇u(x₀+M⁻¹y)‖`, so a derivative normalization costs
  `‖∇u‖ ≳ M²` while an oscillation normalization only costs `osc ≳ M`.
* `oscOn_ge_of_fderiv_lower`: the mean-value package — a derivative lower bound
  *plus* a Lipschitz bound on the derivative gives an oscillation lower bound
  `osc ≥ hA − Kh²`.
* `oscOn_blowup_ge_of_gradient_defect`: its scaled form.  From
  `‖∇u(x₀)e‖ ≥ c₁M²` and `‖∇u(z) − ∇u(x₀)‖ ≤ C M³ ‖z−x₀‖` on `B_{ρ/M}(x₀)`
  (with `ρ > c₁/2C`) one gets the **scale-independent** defect
  `osc_{B_ρ} u_M ≥ c₁²/(4C)`.  This closes the caveat of §4: the "useful
  derivative package" really does produce an `O(M)` oscillation.

## §5–§6 — the scale-invariant quantity and the seam

`QgradCyl G t₀ x₀ r = r⁻¹ ∫_{t₀−r²}^{t₀} ∫_{B_r(x₀)} G`.  With
`blowupDensity` the `M⁻⁴`-rescaled density,

* `integral_ball_comp_blowup` — the spatial change of variables (Jacobian `M⁻³`);
* `QgradCyl_blowupDensity` — **exact scale invariance**:
  `Q_∇(rescaled; 0,0,1) = Q_∇(original; x₀,t₀,M⁻¹)`;
* `gradDensity_blowupSpace` — the density of the rescaled *velocity* field is
  the rescaled density, so the identity applies to `|∇u|²`;
* `QgradCyl_of_density_zero` — `Q_∇` vanishes on gradient-free fields, hence it
  does exclude constants;
* `unit_scale_defect_of_velocity_scale_defect` — the hypothesis (R1-Q)
  `Q_∇(u; x_k,t_k,M_k⁻¹) ≥ ε₀` transfers verbatim to unit scale.

This isolates the seam of §6 exactly: all of the scaling bookkeeping is done,
and what is missing is the analytic statement
`SingularScaleVelocityScaleMatching` — that a singularity forces
`Q_∇ ≥ ε₀` *at the velocity scale* `r ≍ M_k⁻¹` (ε-regularity gives
non-smallness at *singular* scales, and the two scales are not automatically
comparable).

## §8–§10 — what survives of the periodic ancestry

* `blowupSpace_periodic`: the rescaled fields are `Mℤ³`-periodic — the period
  grows, the frequency lattice `(2π/M)ℤ³` refines, the Poincaré constant
  `4π²/M²` dies.
* `eq_zero_of_constant_of_vanishing_ball_average` and
  `false_of_unit_normalized_constant_with_vanishing_ball_average`: if the
  large-scale ball averages of the limit vanish, then a Liouville theorem
  producing merely *some* constant already contradicts `|U(0,0)| = 1`.  This is
  the weakening proposed in §8; whether the vanishing mean is actually
  inherited by the local limit (`AncientExpandingTorusMeanRigidity`, §9) is
  **not** proved and is a genuine open item — as §9 itself notes, for arbitrary
  bounded periodic sequences the implication is false, so Navier–Stokes
  dynamics must enter.
* `poincare_rate_mul_backward_lifetime`: the §10 computation, formalized.  With
  `λ = 4π²/(ML)²` and `A = M²t`, the dimensionless damping `λ·A = 4π²t/L²` is
  *independent of* `M`.  So the longer backward interval exactly compensates the
  vanishing spectral gap: **no free exponential annihilation** at this scaling.
  Any route of this kind must change the extraction so that `λ_k A_k → ∞`.

## §12–§13 — the localized coercivity

`scaledCube_poincare`:  for `C¹` `g` and a cube `Q_L` of side `L`,

```
∫_{Q_L} (g − ⟨g⟩_{Q_L})² ≤ 3 L² ∑_i ∫_{Q_L} (∂_i g)² .
```

This is the localized Poincaré inequality of §12–§13 with an explicit constant,
derived from the unit-cell inequality of `Poincare.lean` by the change of
variables `x = x₀ + L y` (`integral_scaledCube`, `parD_comp_scale`).  It is the
coercivity half of the differential inequality `D_R' + (c/R²) D_R ≤ error_R`.
The other half — vanishing of the boundary and pressure flux terms as `R → ∞`
for bounded ancient solutions (§14, `AncientBoundedVelocityPressureFluxVanishing`)
— is **not** proved.

## §15 — increments

`increment_transport` derives, from the momentum equation, the exact system

```
∂_t δ_h u_a + (u(·+h)·∇) δ_h u_a
  = −(δ_h u·∇) u_a − ∂_a δ_h p + ν Δ δ_h u_a ,
```

with `shift_momentum`/`shift_incompressible` (a spatial translate of a solution
is a solution) as the intermediate step, and
`spatially_constant_iff_shift_eq` recording that vanishing of all increments is
exactly spatial constancy.  The obstruction is visibly the stretching term
`δ_h u·∇u`; no contraction estimate for it is proved here.

## §17–§18 — the rigidity half, and the assembled graph

* `eq_zero_of_geometric_contraction` (**target D**): a nonnegative bounded
  function of the scale contracting by a fixed factor under `R ↦ θR` vanishes
  at every scale.
* `ancient_constant_of_oscillation_contraction`: hence a bounded field on
  `ℝ³ × (−∞,0]` satisfying
  `osc_{Q_{θR}} U ≤ (1−σ) osc_{Q_R} U` for all `R > 0` is **constant** there.
* `false_of_defect_and_oscillation_contraction`: contraction + an R1 defect at
  time `0` is contradictory.
* `oscOn_le_add_of_uniform_approx`, `oscOn_ge_of_uniform_limit` (**target B**):
  the oscillation is `2`-Lipschitz for the uniform distance, so a defect passes
  to uniform limits.
* `oscCyl_parRescale` and `contraction_of_unit_step`: the cylinder oscillation
  rescales as `osc_{Q_R} U_λ = λ · osc_{Q_{λR}} U`, so for any class of fields
  closed under the parabolic rescaling the contraction at *all* scales follows
  from a *single* unit-scale improvement `osc_{Q_θ} ≤ (1−σ) osc_{Q_1}`.  Item C
  is therefore one estimate, not a family.
* `clay_blowup_route_contradiction`: the whole graph of §18, assembled —
  physical velocity-scale defect (A) + uniform convergence to the ancient limit
  (B) + oscillation contraction (C) ⇒ ⊥.

## Status: the first unresolved theorems

The route is now closed **except** for two statements, exactly as the revised
plan predicts:

1. **A — `SingularScaleVelocityScaleMatching`.**  That a first singular time
   forces a non-degenerate constant-excluding defect *at the velocity scale*
   `r ≍ 1/‖u(t)‖_∞`, in either form
   `osc_{B_{R/M_k}(x_k)} u(t_k) ≥ c M_k` or
   `Q_∇(u; x_k, t_k, c/M_k) ≥ ε₀`.
   All of the reductions above are proved; the analytic input is not.
2. **C — `BoundedAncientBlowupClassOscillationContraction`.**  The
   scale-independent inequality `osc_{Q_{θR}} U ≤ (1−σ) osc_{Q_R} U` for the
   bounded ancient blow-up class — equivalently, by `contraction_of_unit_step`,
   the single unit-scale improvement `osc_{Q_θ} U ≤ (1−σ) osc_{Q_1} U` for that
   (rescaling-closed) class.  The localized Poincaré inequality is now
   available (`scaledCube_poincare`); what is missing is the flux/pressure
   control of §13–§14 that would make the localized energy inequality close.

B and D are proved.  Consequently no part of the Clay target is claimed here:
the periodic (torus) Liouville theorem of `AncientLiouville.lean` remains the
only *unconditional* rigidity theorem in the development, and the whole-space
statements above are all either scale identities, reductions, or explicitly
conditional on A and C.
