# The modulus (Gram) tranche: C₄₅–C₄₇ and the A-side scale dichotomy

This note records the tranche that changes the De Giorgi variable of the
increment programme from the quadratic density `q = ½|δ_hu|²` to the **modulus**
`r = |δ_hu|`, and the A-side Gram dichotomy for the parabolic scaling orbit.
Everything listed here is proved in Lean, with no `sorry`, no postulates and no
axioms; the whole project still builds (`lake build RequestProject`).

## C-side

| Result | Lean name | File |
| --- | --- | --- |
| Lagrange identity `\|a\|²\|b\|² − ⟨a,b⟩² = \|a∧b\|²` in `ℝ³` | `ClayNS.lagrange_gram_three` | `IncrementModulusGram.lean` |
| **C₄₅** `\|∇δ_hu\|² − \|∇\|δ_hu\|\|² = \|δ_hu\|^{-2}∑_j\|δ_hu ∧ ∂_jδ_hu\|²` | `ClayNS.increment_modulus_gram_decomposition` | `IncrementModulusGram.lean` |
| Nonnegativity of the transverse surplus | `ClayNS.incrTransDissip_nonneg` | `IncrementModulusGram.lean` |
| `\|P_⊥(δ_hu·∇)δ_hu\|² ≤ \|δ_hu\|²(\|∇δ_hu\|² − \|∇\|δ_hu\|\|²)` | `ClayNS.incrTransportPerp_sq_le` | `IncrementModulusGram.lean` |
| Young absorption of the transverse pairing | `ClayNS.modulus_transverse_absorption` | `IncrementModulusGram.lean` |
| **C₄₆** `β'' + β'/(2q) = 0` for `β_λ(q) = (√(2q) − λ)_+`, on every level set | `ClayNS.modulus_entropy_ode`, `ClayNS.modEntropy_level_ode` | `IncrementModulusCancellation.lean` |
| Radial/transverse split, radial channel = single scalar factor `c₂ + c₁/R` | `ClayNS.increment_modulus_radial_stretching_split`, `ClayNS.increment_stretching_radial_split_gen` | `IncrementModulusCancellation.lean` |
| **C₄₇** exact cancellation of the radial stretching channel | `ClayNS.increment_modulus_radial_stretching_cancellation` | `IncrementModulusCancellation.lean` |
| Existence of a smooth weight realizing the modulus entropy (non-vacuity) | `ClayNS.exists_modulus_entropy_weight` | `IncrementModulusCancellation.lean` |
| Pointwise budget: source linear in `r`, no `θ` | `ClayNS.modulus_caccioppoli_source_bound` | `IncrementModulusCancellation.lean` |
| Integrated cell budget, assuming `δ_hu ≠ 0` | `ClayNS.modulus_caccioppoli_cell_budget` | `ModulusCaccioppoliCell.lean` |
| **Integrated cell budget, unconditional** (regularized modulus `r_ε`) | `ClayNS.modulusEps_caccioppoli_cell_budget` | `ModulusEpsCaccioppoli.lean` |

The headline of the tranche is the last line:

```
∫_cell r_ε^{-1}·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell (|∇δ_hu|² − |∇r_ε|²)/r_ε + (1/2ν)∫_cell r_ε|u|²,
        r_ε = √(|δ_hu|² + ε²),
```

for every `ε > 0`, every smooth periodic divergence-free `u` and every increment
step `h`.  It uses **no** bound on `∇u`, **no** critical `L^{5/2}` strain norm,
**no** level-set exponent and **no** non-degeneracy hypothesis.  The mechanism is
exactly the one the modulus variable exposes:

1. the marginal *radial* stretching channel carries the factor `β'' + β'/r_ε²`,
   which the regularized modulus entropy `β_ε(q) = √(2q+ε²)` annihilates
   identically;
2. the surviving *transverse* channel is matched, by the Lagrange/Gram identity,
   with the transverse viscous surplus `(|∇δ_hu|² − |∇r_ε|²)/r_ε` that the
   modulus chain rule produces and that the `q`-variable never sees;
3. Young's inequality then leaves a source **linear** in `r_ε`.

## The level-set (profile) form of the cancellation

`ModulusLevelSplit.lean` generalizes the tranche from the single entropy
`β(q) = r_ε` to an arbitrary smooth *profile* `ζ : ℝ → ℝ`, with entropy
`β(q) = ζ(r_ε)` and weight `W = ζ'(r_ε)/r_ε`.  The point is the identity

```
β'' + β'/r_ε² = ζ''(r_ε)/r_ε²,
```

so the marginal radial channel is governed by the **second derivative of the
profile alone**.

| Result | Lean name |
| --- | --- |
| Gradient of the profile weight, `∇W = (ζ''/r² − ζ'/r³)∇q` | `ClayNS.modProfileWeight_grad` |
| **The profile split**: divergence + transverse pairing + `ζ''`-residual | `ClayNS.increment_modulus_profile_split` |
| **Cancellation on the flat part**: `ζ''(r_ε) = 0` ⇒ radial channel gone | `ClayNS.increment_modulus_profile_cancellation_of_flat` |
| Young absorption with weight `ζ'(r_ε)` (needs only `ζ' ≥ 0`) | `ClayNS.modulusEps_profile_transverse_absorption` |
| **Integrated profile budget on the cell** | `ClayNS.modulusEps_profile_cell_budget` |

The budget reads

```
∫_cell (ζ'(r_ε)/r_ε)·δ_hu·(δ_hu·∇)u
    ≤ (ν/2)∫_cell ζ'(r_ε)·T_ε + (1/2ν)∫_cell ζ'(r_ε)|u|² + ∫_cell |Res_ζ|,
```

with `T_ε = |∇δ_hu|² − |∇r_ε|²` the transverse surplus and
`Res_ζ = (u·δ_hu)·((δ_hu·∇)q)·ζ''(r_ε)/r_ε²` the marginal residual.  For
`ζ = id` the residual vanishes identically
(`ClayNS.modProfileResidual_flat`, `ClayNS.modProfileWeight_one`) and the
statement collapses to `ClayNS.modulusEps_caccioppoli_cell_budget`.

The De Giorgi consequence is the precise one asked for by the tranche: for the
truncation `ζ_λ(r) = (r − λ)_+` the profile is **affine on the active set**, so
`ζ_λ'' = 0` there and the radial cancellation is *unchanged by the truncation
constant*.  For a smoothed truncation, `ζ_λ''` is supported in a thin annulus
`λ < r < λ + δ`, so the only place where the marginal channel can reappear is
that annulus — not the whole level set.

### What this does and does not settle

It removes the need for a stretching-depletion exponent `θ > 0`
(`ClayNS.IncrementStretchingDepletionGate`) *for the stretching source itself*:
the source is already linear in the modulus, which is the shape the De Giorgi
engine consumes.  It does **not** yet close the C side.  Still to be done in the
modulus variable:

* the localized (adjoint-weighted) time-derivative identity for `(r_ε − λ)_+`,
  i.e. the modulus analogue of `AdjointCaccioppoliClosure.lean`, including the
  pressure pairing;
* the level-set truncation and the De Giorgi recurrence run in `r` rather than
  in `q` (the recurrence itself, `DeGiorgiRecurrence.lean`, is variable
  agnostic);
* the limit `ε ↓ 0`, or a truncation that keeps the level sets away from the
  singular set `{δ_hu = 0}`.

## A-side

| Result | Lean name |
| --- | --- |
| Exact expansion `∫Γ\|Λu − cu\|² = B − 2cC + c²A` | `ClayNS.gram_deficit_identity` |
| Weighted Gram inequality `Δ = AB − C² ≥ 0` | `ClayNS.gramDefect_nonneg` |
| `∫Γ\|Λu − (C/A)u\|² = Δ/A` | `ClayNS.gram_orbit_distance` |
| **The dichotomy**: coercive scale cost, or `ε`-approximate self-similarity | `ClayNS.gaussianScaleGram_dichotomy` |

all in `GaussianScaleGram.lean`, with `Λu = u + (x−x₀)·∇u + 2(t−t₀)∂_tu`
(`ClayNS.scaleGen`).  The dichotomy is unconditional; what it does *not* supply
is the exclusion of the near-self-similar branch, which remains the A-side
obligation.

## The transverse surplus *is* the viscous coercivity

`ModulusViscousCoercivity.lean` closes the last gap in the pairing that C₄₇
asks for.  The budget above bounds the transverse stretching remainder by
`T_ε/r_ε`; this file shows that `T_ε/r_ε` is *exactly* what the viscous term
produces in the modulus variable, not a quantity that has been introduced by
hand.

| Result | Lean name |
| --- | --- |
| `Δq = |∇δ_hu|² + δ_hu·Δδ_hu` | `ClayNS.lap_incrQuad_eq` |
| `Δq = |∇r_ε|² + r_ε·Δr_ε` | `ClayNS.lap_incrQuad_eq_modulus` |
| **Pointwise**: `W_ε·(δ_hu·Δδ_hu) = Δr_ε − T_ε/r_ε` | `ClayNS.modulusEps_viscous_transverse_identity` |
| **Integrated**: `∫_cell W_ε·(δ_hu·Δδ_hu) = −∫_cell T_ε/r_ε` | `ClayNS.modulusEps_viscous_transverse_cell_identity` |
| **Viscous coercivity dominates the stretching** | `ClayNS.modulusEps_viscous_dominates_stretching` |

The last line reads

```
(ν/2)∫_cell T_ε/r_ε
    ≤ −ν∫_cell W_ε·(δ_hu·Δδ_hu) − ∫_cell W_ε·δ_hu·(δ_hu·∇)u
      + (1/2ν)∫_cell r_ε|u|²,
```

i.e. the viscous transverse coercivity absorbs the entire stretching source with
a fixed fraction (a half) to spare, uniformly in `ε`, leaving only a term linear
in `r_ε`.  This is the precise sense in which the modulus variable avoids the
lossy estimate `|wᵀSw| ≤ |S||w|²`.

## Audit of the adjoint defect-weight gate

While assembling the modulus tranche the pre-existing gate
`ClayNS.AdjointDefectWeightGate` (in `FrontierGatesAdjoint.lean`) was re-read
carefully.  As stated it asks for a nonnegative periodic weight `Φ` that solves
the backward adjoint transport–diffusion equation
`−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0` exactly, has a bounded gradient, and is positive
at the defect point.  The **constant weight `Φ ≡ 1` satisfies all of these**, so
the gate is a theorem, not an obstruction:

| Result | Lean name |
| --- | --- |
| The stated weight gate holds (constant weight) | `ClayNS.adjointDefectWeightGate_const` |
| The refined requirement: cell mass ≤ `θ · Φ(z₀)` | `ClayNS.ConcentratedAdjointWeightGate` |
| The constant weight realizes `θ = 1` exactly | `ClayNS.concentratedAdjointWeightGate_one` |

Consequently `ClayNS.adjoint_caccioppoli_budget_of_weight_gate` now delivers its
budget unconditionally — but in the *global*, unlocalized form, which is not
what the De Giorgi argument consumes.  The genuine remaining obligation is
**concentration**: a solution of the backward adjoint equation whose cell mass is
strictly smaller than its value at the defect point (`θ < 1`).  This is exactly
the property that the Carleman-type weights of the backward-uniqueness
literature are built to provide, and it is now recorded as a separate,
honestly-stated gate rather than being hidden inside a gate that is vacuously
satisfiable.
