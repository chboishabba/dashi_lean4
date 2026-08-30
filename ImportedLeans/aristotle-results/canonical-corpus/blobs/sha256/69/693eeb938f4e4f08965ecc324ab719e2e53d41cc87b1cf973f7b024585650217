# The complete list of unresolved obligations (Navier–Stokes lane)

This note answers the request "I don't just want the first unresolved — I want
all of them".  Every item below is either

* **OPEN** — not proved anywhere in this development, and stated as an explicit
  `Prop` in `RequestProject/NavierStokes/OpenGates.lean` (no axioms, no
  postulates, no `sorry`), or
* **DONE** — proved, sorry-free, with only `propext`, `Classical.choice`,
  `Quot.sound`.

The literal Clay periodic target `ClayNS.ClayPeriodicTargetB` is **not** proved.

---

## 1. Frontier gates (genuinely new PDE content required)

### A_dyn — velocity-scale reverse concentration  **OPEN**

`ClayNS.DynamicVelocityScaleDefect` (`DynamicDefectReduction.lean`) and its
oscillation form `ClayNS.PhysicalVelocityScaleDefectGate` (`OpenGates.lean`):

> `T < ∞` a first singular time, `M_k = ‖u(t_k)‖_∞ → ∞` ⟹ there are `c, ε > 0`
> with `Q_∇(u; x_k, t_k, c/M_k) ≥ ε`, equivalently
> `osc_{B_{c/M_k}(x_k)} u(t_k) ≥ ε M_k`.

What is proved around it: exact KNSŠ scaling of oscillation
(`oscOn_blowupSpace`, `oscOn_blowupSpace_ge_iff`), scale invariance of `Q_∇`
(`QgradCyl_blowupDensity`), the forward reduction
(`unit_scale_defect_of_velocity_scale_defect`) and the exact contrapositive
(`unit_scale_flat_of_velocity_scale_flat`).  No part of the gate is bookkeeping
any more; what is missing is dynamical.

### C₁ — localized increment defect transfer on the expanding tori  **OPEN**

`ClayNS.LocalizedDefectTransferGate`.  The Kármán–Howarth identity itself is
proved (`localized_karman_howarth`), with the explicit error bound
`abs_khError_le`, and — new in this pass — the pressure-gauge form
`abs_khError_le_gauge`, which needs only the *oscillation* of `δ_h p` on
`supp ∇Φ` and no `L^∞` pressure bound at all
(`wCutoffFlux_gauge`: `∫∇Φ·(c δ_h u) = 0` because `div δ_h u = 0`).

What remains is the simultaneous requirement: a cutoff family with
`‖∇Φ_k‖_∞, ‖ΔΦ_k‖_∞ → 0` on an intermediate scale `1 ≪ R_k ≪ M_k` for which

* the error really tends to zero, **and**
* the localized structure function retains a unit-scale defect.

A large box makes the first true and the second false; that tension is the
content of the gate.

### C₂ — ancient increment oscillation improvement  **OPEN**

`ClayNS.OscillationContractionGate`.  The reduction machinery is proved: a
single unit-scale improvement suffices (`contraction_of_unit_step`), and the
contraction implies constancy (`ancient_constant_of_oscillation_contraction`).
The strong-minimum shortcut is *refuted*: the Kármán–Howarth sign makes `S₂` a
subsolution, and `parabolic_strong_minimum_no_go` exhibits `S(h) = h₀²` as a
nonnegative stationary subsolution vanishing at `h = 0` and not identically
zero.  So C₂ must be a genuine decay/Harnack estimate for subsolutions.

### C_sparse — anti-concentration for the ancient defect  **OPEN, and now
constrained**

`ClayNS.CubicSparsePropagation` / `ClayNS.PolynomialSparsePropagation`.  The
proposal was: a positive local defect forces `∫_{B_R} S₂ ≳ Ψ(R)` with `Ψ`
growing fast enough to beat the inherited `O(M^{-2})` density dilution.

The requested falsifiable test of the linear skeleton has been carried out and
is **negative** (`LinearSkeletonPropagation.lean`):

* `heatGauss_heat_equation` — `S(t,h) = t^{-3/2}exp(−|h|²/(4κt))` is an exact,
  strictly positive solution of the drift-free skeleton `∂_t S = κΔ_h S`;
* `heatGauss_superpolynomial_decay` — its loss in separation is Gaussian:
  `r^n S(t, r e) → 0` for every `n`, so positivity does *not* travel outward
  with polynomial loss;
* `heatGauss_ball_subpolynomial` — `R^{-d}∫_{B_R} S → 0` for **every** `d > 0`;
* hence `no_cubic_growth_for_linear_skeleton` and
  `no_polynomial_growth_for_linear_skeleton`.

Conclusion: any proof of C_sparse must come entirely from the nonlinear
Kármán–Howarth structure (the flux bound `|F₃| ≤ 2S₂` and the ancestry), not
from the viscous part; the viscous part is provably against it.

---

## 2. Compactness gate

### B′ — extraction of a bounded ancient limit  **OPEN** (standard, not
formalized)

`ClayNS.BlowupLimitGate`: locally uniform convergence of the rescaled fields to
the time-`0` slice of a bounded ancient `U`.  The consequence the route uses —
persistence of the defect under uniform limits — is proved
(`oscOn_ge_of_uniform_limit`), as is the expanding-lattice periodicity of the
rescaled fields (`blowupSpace_periodic`).

**Proved link.**  `blowup_route_false_of_gates`: A + B′ + C₂ ⟹ `False`.  So the
three gates do exclude the blow-up scenario; nothing else is needed on that
branch.

---

## 3. Existence / continuation plumbing (no frontier content)

Local existence and window uniqueness are stated on finite windows via
`ClayNS.IsNSSolutionOn` (globally smooth fields, equations on `[0,T)`).
Continuation and no-blow-up are stated for `ClayNS.IsNSSolutionSlab`: smooth on
the open slab `{t < T}`, equations on `[0,T)`.  That is the honest notion — a
solution on `[0,T)` need not extend smoothly across `t = T`, so a glued family
of windows is a slab solution and not a globally smooth one.

| Gate | Lean name | Status |
| --- | --- | --- |
| Local existence | `LocalExistenceGate` | OPEN |
| Uniqueness on a window | `WindowUniquenessGate` | **DONE** — `windowUniquenessGate_holds` (`WindowUniqueness.lean`), windowed Grönwall on `[0,t]` |
| Continuation past `T` under a velocity bound | `ContinuationGate` | OPEN (the conditional enstrophy estimate is proved: `enstrophy_gronwall_integral`) |
| No velocity blow-up on a finite window | `NoVelocityBlowupGate` | OPEN — this is exactly what A + B′ + C₂ are meant to deliver |
| Assembly into `ClayPeriodicTargetB` | `GlobalAssemblyGate` | **DONE** — `globalAssemblyGate_holds` (`GlobalAssembly.lean`) |

The assembly proof has three parts, all sorry-free:

* **pressure normalization** — `exists_normalized_window`: subtracting `P(t,0)`
  changes neither velocity nor equations, and makes the pressure gauge unique;
* **gluing** — `glue_local`: around every spacetime point in the union of the
  windows, the glued field equals a single member of the family on an open
  neighbourhood (the index is clipped at `t = 0`, which is what makes this true
  at the initial time, where different members are unrelated for `t < 0`);
  hence `glue_isNSSolutionSlab` and `glue_isNSSolution`;
* **maximal time** — `windowLengths_unbounded`: if the reachable window lengths
  were bounded, gluing gives a slab solution up to the supremum, no-blow-up
  bounds its velocity there and continuation exceeds the supremum.

Consequence: `clayPeriodicTargetB_of_gates` — the literal Clay periodic target
follows from **local existence + continuation + no velocity blow-up** alone.

---

## 4. Smaller open questions recorded along the way

* Whether the vanishing large-box mean of the rescaled fields is inherited by
  the local ancient limit (§9 of `revised-blowup-route.md`).  It is *not*
  automatic: Fatou only gives `∫_{B_R} S ≤ liminf ∫_{B_R} S_k` and the
  pre-limit bound is `O(M_k^{-2} L_k³)`, which is large.
* A Calderón–Zygmund/BMO estimate for the increment pressure compatible with the
  cutoff derivative.  Today's gauge invariance reduces what is needed from an
  `L^∞` bound on `δ_h p` to an oscillation bound on `supp ∇Φ`; the estimate
  itself is still an input.
* The competition `ν/R²` versus `A²/ν` in the increment amplitude estimate
  (`incrEnergy_le_exp`): a one-step gain follows exactly when the local Reynolds
  number is small, and nothing downstream of the identities removes that
  condition.

---

## 5. Summary count

Frontier: **A_dyn, C₁, C₂** (with C_sparse as a proposed replacement for
C₁ + C₂, now known to be unobtainable from the linear part).  Compactness: B′.
Plumbing still open: **local existence** and **continuation**; window
uniqueness and global assembly are now proved, and no-blow-up is the frontier
route's own conclusion.  The first unresolved theorem on the critical path
remains **A_dyn**.
