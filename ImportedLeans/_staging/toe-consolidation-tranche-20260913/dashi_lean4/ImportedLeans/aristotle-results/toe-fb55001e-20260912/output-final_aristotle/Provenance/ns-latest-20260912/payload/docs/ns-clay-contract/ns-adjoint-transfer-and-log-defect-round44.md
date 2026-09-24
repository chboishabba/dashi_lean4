# Round 44 — the adjoint weight, the stretching commutator, and the logarithmic defect

**Status of the Clay periodic Navier–Stokes regularity target: NOT PROVED.**
This note records what was added, what it settles, and what remains. Every
statement referenced below compiles in the project with no `sorry`, no
postulates, and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. C-side: the requested experiment, and its answer

The instruction was explicit: *derive the adjoint-weighted truncation identity
and inspect the `wᵀS(U)w` term before bounding it*; do **not** immediately
replace it by `|S||w|²`.

### 1.1 The critical estimate, and why it is not enough

`IncrementStretchingCritical.lean`

* `critical_holder_triple` — the exponent arithmetic
  `1/(5/2) + 1/(10/3) + 1/(10/3) = 1`, as a genuine measure-theoretic Hölder
  bound `∫_A |S·v| ≤ ‖S‖_{5/2}‖v‖_{10/3} μ(A)^{3/10}`.
* `increment_stretching_critical_estimate` — **(C-S)**:
  `|𝒮_k| ≤ 8‖S‖_{5/2}‖v_k‖_{10/3}|A_k|^{3/10}`.
* `incrStretch_truncation_abs_le` — the pointwise half: the KNSŠ normalization
  `q ≤ 2` supplies the constant `8`.
* `sublinear_recurrence_no_decay` / `critical_strain_recurrence_insufficient` —
  the **no-go**: a recurrence `Y_{n+1} ≤ Cbⁿ Y_n^{θ}` with `θ < 1` has no
  smallness threshold forcing `Y_n → 0`. The `Y_k^{3/5}` produced by (C-S) is
  sublinear, so a generic critical `L^{5/2}` strain bound cannot drive De
  Giorgi.

This confirms the cut proposed in the tranche: **pressure is no longer the
critical obstruction on C; the linear-in-truncation stretching source is.**

### 1.2 The adjoint weight kills the whole localization bill

`AdjointLocalizedIncrement.lean`

* `increment_convex_identity` — the *sharp* convex-composition identity, keeping
  the good term `−νβ''(q)|∇q|²` (the usual subsolution form throws it away; the
  De Giorgi budget needs it).
* `static_cutoff_localization_bill` — for an arbitrary weight, the identity
  exhibits the bill `β(q)·(∂_tΦ + u(·+h)·∇Φ + νΔΦ)`.
* `adjointOp`, `adjoint_localized_increment_identity` — **(Adj)**: if
  `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0`, the bill cancels *as one package*; no `∂_tΦ`,
  no `∇Φ·u(·+h)`, no `ΔΦ` term survives.
* `adjoint_localized_increment_residual` — an approximate weight pays exactly
  `|β(q)|·R`, `R` the adjoint residual, and nothing else.
* `adjoint_localized_increment_budget` — the rearranged budget: both good terms
  on the left, stretching + pressure work on the right.

### 1.3 The `wᵀSw` term **does** admit a further divergence representation

This is the substantive answer to the experiment.

`IncrementStretchingTransfer.lean`

* `incrStretch_weighted_transfer`, `incrStretch_localized_split` — with the De
  Giorgi weight `W = Φβ'(q)`,

  ```
  W·wᵀS(U)w = div( W(u·w)w ) − (u·w)(w·∇W) − W·Σ_{a,j} u_a w_j ∂_j w_a,
  ∇W = β'(q)∇Φ + Φβ''(q)∇q.
  ```

* `increment_stretching_transfer_budget` — the non-divergence remainder is
  bounded using **only amplitude bounds** `|u_a| ≤ A`, `|w_a| ≤ B` (KNSŠ gives
  `A = 1`, `B = 2`): **no** bound on `∇u`, **no** critical norm of the strain.
  The bound is

  ```
  ην·Φβ''(q)|∇q|² + (ν/2)·Φβ'(q)|∇w|²  +  C₁Φβ''(q) + C₂Φβ'(q) + C₃β'(q),
  C₁ = 27A²B⁴/(4ην),  C₂ = 9A²B²/(2ν),  C₃ = 9AB²G.
  ```

* `increment_stretching_transfer_cell_budget` — the same, integrated over the
  periodicity cell, where the transfer flux divergence vanishes.

For the quadratic entropy `β_k(q) = v_k²` (`β' = 2v_k`, `β'' = 2·1_{A_k}`) the
remainder is `C₁|A_k| + C₂∫v_k + C₃∫v_k` — **linear** in the truncation data,
not the sublinear `Y_k^{3/5}` of §1.1. `linear_budget_superlinear_recurrence`
records abstractly that a linear budget plus Chebyshev yields the superlinear
`Y_{n+1} ≲ bⁿ Y_n^{7/5}` the De Giorgi engine consumes.

### 1.4 The closed conditional budget

`AdjointCaccioppoliClosure.lean` — `adjoint_caccioppoli_linear_budget`:

```
∫ ∂_t(Φβ(q)) + (1−η)ν ∫ Φβ''(q)|∇q|² + (ν/2) ∫ Φβ'(q)|∇δ_hu|²
    ≤ C₁ ∫ Φβ''(q) + (C₂ + 3BG_p) ∫ Φβ'(q) + C₃ ∫ β'(q).
```

No cutoff bill (the adjoint weight), no strain norm (the commutator), pressure
entering only through the amplitude bound `G_p` on `∇δ_hp`.

### 1.5 What C still needs — `C*`

`FrontierGatesAdjoint.lean` states the two remaining inputs as `Prop`s and
proves the links.

* `AdjointDefectWeightGate` — existence of a nonnegative periodic `Φ` solving
  (Adj) exactly with bounded gradient and **positive at the defect point** (the
  positivity is what excludes the trivial `Φ ≡ 0`). This is a backward caloric
  transport kernel; it is not constructed here.
  `adjoint_caccioppoli_budget_of_weight_gate` proves that this gate is the only
  thing between the development and a defect-centred budget.
* `IncrementStretchingDepletionGate` — the extra level-set factor
  `|A_k|^{3/10+θ}`, `θ > 0`. `incrementStretchingDepletion_exponent_zero` proves
  the `θ = 0` case unconditionally, so the *entire* content of the gate is
  `θ > 0`.

The alternative branch — scale-uniform smallness `sup_R ‖S(U)‖_{L^{5/2}(Q_R)} ≤
ε_*` — is deliberately **not** assumed anywhere; it would be a very strong
theorem in its own right.

Also unresolved on the C side: the smallness input that launches the
recurrence, and the scale-invariance requirement recorded in
`RescalingAudit.lean`.

---

## 2. A-side

### 2.1 Coarse-grained resolution replaces the signed detector

`CoarseGrainedResolution.lean`

* `gradient_defect_coarse_resolution` — **(A-res)**
  `Q_∇(u;r) ≤ 2Q_∇(U^ℓ;r) + 2Q_∇(u−U^ℓ;r)`, from the pointwise
  `|∇u|² ≤ 2|∇U^ℓ|² + 2|∇(u−U^ℓ)|²`.
* `gradient_defect_dichotomy` — hence `Q_∇(u;r) ≥ ε` forces either
  `Q_∇(U^ℓ;r) ≥ ε/4` (resolved viscous dissipation) or
  `Q_∇(u−U^ℓ;r) ≥ ε/4` (a genuine subfilter-gradient defect). **No finite
  signed detector is required.** Gradient energy is constant-excluding, which
  is why `Q_∇` is the better observable.

### 2.2 The geometrically weighted telescope is *not* an A proof

`geometric_telescope_not_scale_exclusive` — with dyadic weights `w_k = r_k/r_0 ~
2^{-k}`, a fixed per-scale defect `ε` at *every* dyadic radius still has total
weighted cost `≤ 2ε`. A geometrically weighted ledger therefore cannot exclude a
bad scale at every dyadic radius; the almost-monotonicity input must be
controlled in *logarithmic* scale, i.e. with a roughly unweighted cost per
dyadic step.

### 2.3 The logarithmic defect — `A*`

`BackwardKernelFluxDefect.lean`

* `nsLogDefect` — the defect density is **identified**, not postulated:
  `D_NS(r) = [𝓕(r)+𝓛(r)]_+/(r·𝒟(r))`, with `𝒟` the backward-kernel dissipation
  and `𝓕+𝓛` the localized signed flux of the exact scale derivative (A-HK).
  `nsLogDefect_eq_log_density` makes `∫D_NS dr` literally the left-hand side of
  (A*).
* `scale_derivative_le_nsLogDefect` — (A-HK) gives almost-monotonicity with **no
  sign hypothesis on the flux**.
* `backward_kernel_flux_defect_propagates`, `backward_kernel_flux_defect_integrable`
  — a uniform logarithmic bound `C` propagates the defect to the bottom scale
  with constant `e^{−C}ε`, independent of the number of dyadic steps and hence
  of `M`.
* `clay_A_dyn_of_uniform_log_defect` — that constant yields
  `DynamicVelocityScaleDefect`, i.e. `A_dyn`.

Not proved: (A-HK) and (A*) themselves. That is the frontier item `A*`.

---

## 3. On the cited coarse-graining framework

The June 2026 coarse-graining/pressure-flux work is relevant to A as a
*decomposition philosophy*, not as a drop-in solution: its depletion theorem is
limited to a fixed finite chain and its authors do not claim uniform detector
constants, summable localization leakage, or control of backscatter in the
moving-chain limit; its detector-to-CKN interface is itself conditional.
Nothing from it is used as an input here. Section 2.1 replaces its signed
detector by the resolution dichotomy, and section 2.2 records why its weighted
telescope does not supply the missing almost-monotonicity.

---

## 4. The frontier, precisely

```
A* : BackwardKernelFluxDefectIntegrable — (A-HK) and the uniform logarithmic
     bound (A*). Everything downstream is proved.

C* : one of
       (i)  AdjointDefectWeightGate      (existence of the backward adjoint
                                          defect weight), or
       (ii) IncrementStretchingDepletionGate  (level-set exponent 3/10 + θ,
                                          θ > 0),
     plus the recurrence-launching smallness and the scale-invariance
     requirement of RescalingAudit.lean.
```

Neither is proved. The Clay periodic regularity target is therefore **not**
established by this development.
