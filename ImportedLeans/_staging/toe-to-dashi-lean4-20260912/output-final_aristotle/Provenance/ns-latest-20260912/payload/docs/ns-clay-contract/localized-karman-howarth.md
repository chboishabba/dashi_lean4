# The localized Kármán–Howarth identity, and where the route stands after it

All statements below are machine-checked Lean 4 theorems in
`RequestProject/NavierStokes/`, with no `sorry`, no postulates and no added
axioms (`#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`).

## 1. What was asked

The `C_loc` gate: derive the localized Kármán–Howarth/Monin identity for

```
S₂,Φ(h,t) = ∫_cell Φ(x) |u(t,x+h) − u(t,x)|² dx
```

*without taking absolute values too early*, keeping the cutoff and pressure
errors explicit, and test whether those errors can vanish on an intermediate
scale.

## 2. What is now proved

### 2.1 The identity (`ClayNS.localized_karman_howarth`)

For a smooth `ℤ³`-periodic solution `(u,p)` of the zero-force Navier–Stokes
system and a smooth, time-independent, periodic cutoff `Φ`,

```
∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + 2∫∇Φ·F + 2ν∫qΔΦ − 2∫q(δ_h u·∇Φ)
```

exactly, with `q = ½|δ_h u|²`, `F = q·u(·+h) + δ_h p·δ_h u`, and
`F₃(h,t)_m = ∫Φ δ_h u_m |δ_h u|²`.  It is an identity, not an estimate.

Three structural features are visible in the statement.

* The dissipation `−2ν∫Φ|∇_x δ_h u|²` is manifestly nonpositive.
* The pressure occurs **only** inside `∫∇Φ·F` — only paired with a derivative
  of the cutoff.  There is no interior pressure term at all.  This is the
  concrete sense in which the increment route removes the pressure obstruction
  that appears at the velocity level.
* Every error term besides the dissipation carries a derivative of `Φ`, hence
  is supported where the cutoff varies.

Supporting pieces:

* `ClayNS.hasDerivAt_wIncrEnergy` — the cutoff-weighted increment energy
  balance, obtained by integrating the pointwise localized identity over the
  cell.
* `ClayNS.divH_strFlux_eq` — `∇_h·F₃ = 2∫Φ δ_h u·(δ_h u·∇)u + 2∫Φ δ_h u·∇q`;
  this is where incompressibility of `u` at the shifted point is used.
* `ClayNS.wTransport_eq_neg_wCutoffTransport` — because `δ_h u` is divergence
  free, `∫Φ δ_h u·∇q = −∫q (δ_h u·∇Φ)`, so the interior transport term is in
  fact another pure cutoff error.

### 2.2 The error is controlled by the derivatives of the cutoff
(`ClayNS.abs_khError_le`)

With `|∂_iΦ| ≤ G`, `|ΔΦ| ≤ H` and `|F| ≤ K_F`, `|q| ≤ K_q`, `|δ_h u| ≤ K_w`,

```
|E_cutoff + E_pressure| ≤ 6·G·K_F + 2|ν|·K_q·H + 6·G·K_q·K_w.
```

So the intermediate-scale criterion `1 ≪ R_k ≪ M_k` is exactly the requirement
that the cutoff family have `sup|∇Φ_R|, sup|ΔΦ_R| → 0` while the increment,
the increment flux and the increment pressure stay uniformly bounded.  Nothing
else about the geometry enters.

### 2.3 The homogeneous limit (`ClayNS.karman_howarth_torus`)

For `Φ ≡ 1` the error vanishes identically and the identity becomes the exact
Kármán–Howarth–Monin equation on the periodicity cell,

```
∂_t S₂ + ∇_h·F₃ = −2ν∫|∇_x δ_h u|².
```

## 3. Two negative findings about the hoped-for shortcut

The suggested best case was: obtain `∂_tS + ∇_h·(bS) = 2νΔ_hS` with `S ≥ 0`,
`S(0,t) = 0` and no positive source, and conclude `S ≡ 0` by a strong minimum
principle.  Both halves of that shortcut fail.

* `ClayNS.khm_balance_at_zero_separation` — at `h = 0` the balance is vacuous.
  `S₂(0,t) = 0` identically so `∂_tS₂(0) = 0`; `F₃` is cubic in the increment
  so `∇_h·F₃(0) = 0`; and the separation Laplacian
  `2νΔ_hS₂(0) = 4ν∫Φ|∇u|²` (`ClayNS.lapH_strFun_at_zero`) is *exactly*
  cancelled by the dissipation source.  The two sides reduce to `0 = 0`, so no
  information can be extracted at the interior zero itself.
* `ClayNS.parabolic_strong_minimum_no_go` — the sign of the identity makes `S₂`
  a **subsolution**, `∂_tS + ∇_h·(bS) − 2νΔ_hS ≤ 0`, which is the wrong side
  for a minimum principle.  For every `ν ≥ 0` the explicit witness
  `S(h) = h₀²` (with zero drift) is smooth, nonnegative, stationary, vanishes
  at `h = 0`, satisfies the subsolution inequality with room to spare, and is
  not identically zero.

Consequence: the rigidity step `C_DG` cannot be a one-line strong minimum
principle.  It has to be a genuine oscillation-decay / Harnack argument for
subsolutions, or the source must first be given the opposite sign.

## 4. The `A_dyn` side

`RequestProject/NavierStokes/DynamicDefectReduction.lean` states the gate
exactly (`ClayNS.DynamicVelocityScaleDefect`) and closes the scaling
bookkeeping around it in both directions:

* `ClayNS.unit_scale_defect_of_dynamicDefect` — the gate yields a uniform
  unit-scale gradient-energy defect for the rescaled fields, which is the
  constant-excluding input the blow-up argument consumes;
* `ClayNS.unit_scale_flat_of_velocity_scale_flat` — the exact contrapositive:
  if the velocity-scale gradient energy tends to zero, the rescaled unit
  cylinders are asymptotically gradient-flat.

So no part of `A_dyn` is scaling bookkeeping any more.  What is missing is
purely dynamical.

## 5. First unresolved theorem, stated precisely

With the above in place, the first target-critical statement that is **not**
proved, and that no supplied constructive material yields, is:

> **(A_dyn)** Let `u` be a smooth periodic Navier–Stokes solution with first
> singular time `T < ∞` and `M_k = ‖u(t_k)‖_∞ → ∞`, `t_k ↑ T`.  Then there
> exist `c, ε > 0` and singular points `x_k` with
> `Q_∇(u; x_k, t_k, c/M_k) ≥ ε` for all `k`.

Equivalently: the singular dynamics force the Caffarelli–Kohn–Nirenberg defect
to penetrate down to the velocity scale `r ≍ M_k⁻¹`.  Positivity and nesting of
the CKN defect alone do not move the defect inward, and the energy-only and
CKN-nesting no-gos already in the repository show that this cannot be repaired
by scaling or by the local energy inequality by itself.

The second unresolved statement is `C_loc` in its remaining form: the identity
of §2.1 and the bound of §2.2 are proved on the periodic cell, but the passage
to the whole-space ancient limit still needs a cutoff family and a field family
on the expanding tori for which the bound of §2.2 actually tends to zero at an
intermediate scale `1 ≪ R_k ≪ M_k`, together with a nonnegative localized
structure defect that still sees the unit-scale oscillation.

Neither gap is closed here, and the Clay periodic regularity target is
therefore not established.
