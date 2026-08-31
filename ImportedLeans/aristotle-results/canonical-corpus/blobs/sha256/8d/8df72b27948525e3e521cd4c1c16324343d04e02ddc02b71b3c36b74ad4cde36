# Rigidity branches for a hypothetical critical element

File: `RequestProject/NavierStokes/CriticalElementRigidity.lean`.
Whole project builds; no `sorry`, no postulate, no added axiom; every headline
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

## What was asked

The critical-element route reduces a hypothetical failure of a critical
spacetime bound to one minimal trajectory that keeps a fixed critical size and
is compact modulo the symmetries, and then splits into scenarios:

1. a soliton-like orbit at bounded frequency scale,
2. a frequency cascade,
3. finite-time concentration.

The suggested order of attack was to kill (1) via "nonzero compact orbit ⇒
positive dissipation floor ⇒ infinite dissipation, contradicting the finite
energy budget", then (2) by an `L²` collapse, leaving (3) for a
backward-uniqueness input.

## What is proved

Branches (1) and (2) are now closed on the literal Galerkin carrier
`ClayNS.Waleffe.GalerkinFlow`, **without any compactness or almost-periodicity
hypothesis**, because the dissipation floor is available by interpolation alone.

1. **Interpolation on the carrier.**
   `critEnergy_sq_le_energy_mul_dissipation`:
   `(∑_k |k| ‖u_k‖²)² ≤ (∑_k ‖u_k‖²)(∑_k |k|² ‖u_k‖²)`, i.e.
   `‖u‖_{Ḣ^{1/2}}⁴ ≤ ‖u‖_{L²}² ‖u‖_{Ḣ¹}²`. Cauchy–Schwarz on the finite mode set;
   an exact statement with no cutoff dependence.

2. **Dissipation floor.** `dissipation_ge_of_critEnergy_floor`: if the critical
   energy is at least `K > 0` and the energy at most `M`, then `𝔇 ≥ K²/M`. Since
   the energy is nonincreasing, along a trajectory `𝔇(t) ≥ K²/E(t₀)`.

3. **Bounded lifetime (soliton branch).**
   `lifetime_bound_of_critEnergy_floor`: if `K ≤ E₁₂(t)` throughout `[t₀,t₁]`
   then `t₁ − t₀ ≤ E(t₀)²/(2νK²)`, from the energy balance
   `E(t₁) + 2ν∫𝔇 = E(t₀)`. Hence `no_eternal_critical_element`: no trajectory
   keeps its critical energy above a fixed positive level for all forward time,
   and `exists_critEnergy_lt_of_long_interval`: on any longer interval the
   critical energy dips strictly below `K`.

4. **Measure form.** `volume_critEnergy_ge_le`: for every `T ≥ 0` and `K > 0`,
   `vol{t ∈ [0,T] : E₁₂(t) ≥ K} ≤ E(0)²/(2νK²)`, uniformly in `T` and in the
   Galerkin cutoff. This does not require the floor to be sustained on an
   interval, so it applies to a critical element that only concentrates on a
   time set of positive measure.

5. **A cutoff-uniform spacetime bound.** `integral_critEnergy_sq_le`:
   `∫_{t₀}^{t₁} (∑_k |k|‖u_k‖²)² dt ≤ E(t₀)²/(2ν)`, with no dependence on the
   terminal time or the cutoff — in continuum notation `u ∈ L⁴_t Ḣ^{1/2}_x` with
   the Leray energy constant. Chebyshev applied to it reproves item 4.

6. **What a defect estimate of the shape `Q ≤ C·E₁₂·𝔇` would need.**
   `integral_le_of_pointwise_critEnergy_dissipation_bound`: on a window where
   `E₁₂ ≤ K`, such a `Q` obeys `∫ Q ≤ C·K·E(t₀)/(2ν)`, cutoff-uniformly. So for
   a spacetime defect budget of that shape the energy side is settled here, and
   the whole missing input is the uniform-in-time critical bound `K` — which is
   precisely the quantity the rigidity scenarios are about.

7. **Cascade branch.** `lifetime_bound_of_frequency_cascade`: if in addition the
   energy of the concentrating profile obeys `E(t) ≤ C/N`, the same floor can be
   sustained only for a time `≤ C·E(t₀)/(2νK²N)`, which tends to `0` as the
   concentration scale `N → ∞`.

8. **The compactness route, recorded and compared.**
   `exists_floor_of_compact_orbit` (a continuous positive functional on a compact
   set has a positive floor along any orbit inside it),
   `false_of_positive_floor_of_budget` (a positive floor contradicts a finite
   time-integrated budget), and their instantiation
   `no_compact_orbit_of_positive_dissipation`. On this carrier that route is
   strictly weaker than item 3, which needs no compactness at all.

## What this does not close

Everything above is about the truncated (Galerkin) system, whose solutions are
in any case globally smooth; the content is that the constants are uniform in
the cutoff, in the terminal time and in the mode count. The statements control
the critical **energy** `∑_k |k| ‖u_k‖²`, not the missing spacetime estimate for
the mixed-helicity defect, and they say nothing about branch (3), finite-time
concentration, which is exactly where a backward-uniqueness argument would be
needed. Package A is not closed, no Clay-level claim is made, no target was
weakened and no axiom or conditional bridge was added.
