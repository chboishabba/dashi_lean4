# The increment carrier: local energy, pressure cancellation, and what is left

This note records the pass that pushed the increment formulation
(`RequestProject/NavierStokes/Increments.lean`) through the localized `L²`
calculation, as the frontier analysis requested.  Everything cited here
compiles under `lake build RequestProject`, contains no `sorry`, no `axiom`,
no `postulate`, and every theorem was checked with `#print axioms` to depend
only on `propext`, `Classical.choice`, `Quot.sound`.

Files: `RequestProject/NavierStokes/IncrementLocalEnergy.lean` (pointwise) and
`RequestProject/NavierStokes/IncrementEnergyPeriodic.lean` (integrated on the
periodicity cell).

## 1. What was computed

Write `δ_h u = u(·+h) − u`, `δ_h p = p(·+h) − p`, `q = ½|δ_h u|²`.

**(a) The advective term cancels.**  The increment is transported by the
*shifted* field `u(·+h)`, which is divergence free, so
`(u(·+h)·∇)q = div(q·u(·+h))` (`incr_transport_divergence`).

**(b) The pressure cancels.**  The increment itself is divergence free
(`divg_incrVec`), hence `δ_h u·∇δ_h p = div(δ_h p·δ_h u)`
(`incr_pressure_divergence`): the pressure never produces an interior term,
only a flux.

**(c) The exact local energy identity** (`increment_local_energy_identity`):

    ∂_t q + div( q·u(·+h) + δ_h p·δ_h u ) = ν(Δq − |∇δ_h u|²) − δ_h u·(δ_h u·∇)u.

**(d) Localized by a cutoff** (`increment_localized_energy_identity`), for a
time-independent smooth `Φ`:

    ∂_t(Φq) + div( Φ·F − ν(Φ∇q − q∇Φ) ) = ∇Φ·F + νqΔΦ − νΦ|∇δ_h u|² − Φ·(stretching),

with `F = q·u(·+h) + δ_h p·δ_h u`.  Every term except the last is the good
dissipation, a divergence, or carries a derivative of the cutoff.

So the answer to the question posed by the frontier analysis is: **yes, the
advective and pressure terms cancel exactly, and the only interior obstruction
is the stretching term.**

## 2. The structure of the obstruction

Two exact facts were extracted about `δ_h u·(δ_h u·∇)u`.

**Strain only.**  `incrStretch_eq_strain`: the term contracts `δ_h u ⊗ δ_h u`
against `∇u`, so the antisymmetric (vorticity) half cancels identically; only
the strain enters.  With an entrywise bound `K` on `∇u`,
`|stretching| ≤ 3K|δ_h u|²` (`incrStretch_abs_le`), whence the localized
inequality `increment_localized_dissipation_le` in which the obstruction costs
`6K·Φq` against the dissipation `νΦ|∇δ_h u|²`.

**The derivative can be moved off `u`.**  `incrStretch_divergence_transfer`:
for divergence-free `u`,

    δ_h u·(δ_h u·∇)u = div( (u·δ_h u)·δ_h u ) − ∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a.

Up to one further *flux*, the derivative sits on the increment.  Young's
inequality (`incrTransfer_abs_le`) then gives, for every `ε > 0`,

    |∑ u_a δ_h u_j ∂_j δ_h u_a| ≤ (ε/2)|∇δ_h u|² + (1/2ε)|u|²|δ_h u|²,

and with `ε = ν` the amplitude form of the local energy inequality
(`increment_local_energy_amplitude_le`):

    ∂_t q + div( F + (u·δ_h u)δ_h u ) ≤ νΔq − (ν/2)|∇δ_h u|² + (|u|²/ν)·q.

**No bound on `∇u` is used anywhere in this line.**  This is a genuine
improvement on absolute-value estimates for the flux: the interior cost is
governed by the amplitude alone.

## 3. The integrated statements on the torus

Since the Clay target here is periodic, the same identities were integrated
over the periodicity cell, where every divergence disappears
(`cellInt_divg_eq_zero`, `cellInt_lap_eq_zero`):

* `hasDerivAt_incrEnergy`:
  `d/dt ∫½|δ_h u|² = −ν∫|∇δ_h u|² − ∫δ_h u·(δ_h u·∇)u`;
* `incrStretchInt_eq_neg_transferInt`: after integration the stretching term is
  exactly `+∫∑ u_a δ_h u_j ∂_j δ_h u_a`, so it never requires `∇u`;
* `deriv_incrEnergy_le_of_amplitude`: with `|u(t,·)| ≤ A`,
  `d/dt ∫½|δ_h u|² ≤ −(ν/2)∫|∇δ_h u|² + (A²/ν)∫½|δ_h u|²`;
* `incrEnergy_le_exp`: hence `∫½|δ_h u(t)|² ≤ e^{(A²/ν)(t−s)}∫½|δ_h u(s)|²` for
  `s ≤ t` — the `L²` modulus of continuity of a smooth periodic solution grows
  at most at the rate `A²/ν`, with no gradient hypothesis at all.

## 4. What this does and does not settle

It settles the mechanism question: the increment carrier does remove the
pressure and the transport term from the interior, and it does convert the
cubic obstruction into an amplitude-controlled one.  The surviving competition
at scale `R` is between the damping rate `ν/R²` (localized Poincaré,
`scaledCube_poincare`) and the coefficient `A²/ν`, i.e. between `1` and
`(AR/ν)²`.  So the increment route yields a one-step gain precisely when the
local Reynolds number `AR/ν` is small, and no absolute estimate downstream of
the identities above removes that condition.

It does **not** close either frontier theorem:

1. **A (velocity-scale defect).**  Nothing here produces a defect at the scale
   `r ≍ 1/‖u(t)‖_∞` from a first singular time; that remains the dynamical
   reverse-concentration statement, and the scaling bookkeeping for it is in
   `BlowupOscillation.lean` / `ScaleInvariantGradientEnergy.lean`.
2. **C (unit-scale oscillation improvement for the ancient class).**  For a
   normalized bounded ancient limit the ratio above is `O(1)` at unit scale, so
   the estimates proved here do not by themselves give a contraction factor
   `1 − σ`.  What is now precise is *which* additional structure has to be
   used: something beyond the amplitude bound (sign, decay, or class structure
   of the blow-up limit) is required to beat `(A/ν)²` at unit scale.

Nothing in this pass was assumed, postulated, or recorded as authority; the
Clay periodic target `ClayNS.ClayPeriodicTargetB` remains unproved.
