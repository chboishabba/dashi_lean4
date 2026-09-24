# The literal Galerkin trajectory: existence, invariants, and the exact Gram flux identity

This round closes, on the Lean side, the *real-analysis* leaf that the
resolvent/Gram lane had been carrying as an assumption: the existence of an
actual differentiable trajectory of the finite Galerkin system, and the
fundamental theorem of calculus for the flux observables built on it.

Everything below compiles with no `sorry` and no added axiom.

## 1. What was assumed before

The Waleffe/Galerkin lane is organised around the structure

```lean
structure GalerkinFlow where
  nu : ℝ ;  nu_nonneg : 0 ≤ nu ;  modes : Finset Wave ;  zero_not_mem : (0 : Wave) ∉ modes
  u : ℝ → Wave → Fin 3 → ℂ
  support : ∀ t k, k ∉ modes → u t k = 0
  transverse : ∀ t k, herm (wC k) (u t k) = 0
  reality : ∀ t k i, u t (-k) i = conj (u t k i)
  ode : ∀ t k, k ∈ modes → ∀ i,
    HasDerivAt (fun s => u s k i) (-((nu * wsq k : ℝ) : ℂ) * u t k i + modalForcing modes (u t) k i) t
```

Every downstream result in that lane — the triad amplitude ODE, the energy
balance, the Serrin reduction, the Gram flux consumers — is a theorem *about*
an inhabitant of this structure.  Nothing in the development constructed one.
In particular the time derivative, the global-in-time domain, and the
propagation of the kinematic constraints were all postulates.

## 2. What is now proved

`RequestProject/NavierStokes/GalerkinStateSpace.lean`

* `State modes := ↥modes → Fin 3 → ℂ`, a finite-dimensional real Banach space,
  with `spread` extending a state to the whole lattice by zero.
* `vfield modes nu` — the *literal* right-hand side of the truncated system,
  and `contDiff_vfield`: it is `C^∞`, being a degree-two polynomial in the real
  coordinates (the Leray projection contributes only the constants `1/|k|²`).
* the smooth energy cutoff `cut R` and the truncated field
  `tvfield modes nu R = cut R • vfield nu`.

`RequestProject/NavierStokes/GalerkinTruncatedField.lean`

* sublevel sets of the energy are compact, so `tvfield` has compact support,
  is globally bounded and globally Lipschitz;
* `exists_solution_tvfield` — Picard–Lindelöf then applies on an arbitrary time
  window, with no smallness restriction on its length.

`RequestProject/NavierStokes/GalerkinInvariants.lean`

* `transverse_of_solution` — the transversality scalar `⟪k, u_k⟫` obeys a
  *linear* damped scalar equation along the flow, so ODE uniqueness forces it
  to stay zero;
* `reality_of_solution` — the reflected trajectory solves the same equation
  with the same initial value, so ODE uniqueness forces reality to persist.

`RequestProject/NavierStokes/GalerkinExistence.lean`

* `en_hasDerivAt_of_solution` — the energy identity along the cut-off flow.
  Because transversality and reality persist, the projected nonlinearity is
  energy neutral and `d/dt E = −2·cut·ν·𝔇`.
* `en_le_exp_of_solution` — the a-priori bound `E(t) ≤ E(0) e^{2ν(∑|k|²)|t|}`,
  which depends only on the data, never on the solution.
* `exists_global_solution` — the cutoff is therefore never active on the window
  it was designed for; the local solutions glue and the **literal** system
  `u̇ = −ν|k|²u + f(u)` has a solution on all of `ℝ`, forwards and backwards,
  with transversality and reality for all time.
* `exists_galerkinFlow` — hence `GalerkinFlow` is inhabited by a genuine
  trajectory, for every admissible datum.
* `exists_nonzero_galerkinFlow` — and non-trivially so: the explicit symmetric
  pair `±(1,0,0)` with datum `(0,1,0)` gives a flow that is not identically
  zero.

`RequestProject/NavierStokes/GalerkinGramFlux.lean`

* `exists_damped_forced` — Duhamel: for a real rate `λ` and a *continuous*
  complex forcing `f`, `A(t) = e^{−λt}∫₀^t e^{λs}f(s)ds` is everywhere
  differentiable with `A' = −λA + f`.  This is the fundamental theorem of
  calculus for a continuous integrand, and it is what turns a formal algebraic
  tangent into an actual time derivative.
* continuity lemmas for every object built polynomially from the Fourier
  coefficients: the raw slot kernel, the Leray projection, the inner forcing,
  the outer cells, the Gram remainder and the resolvent form.
* `exists_outCell_family` — at every output frequency there is a genuine cell
  family obeying the literal damped tangent
  `dA_α = −ν(|p|²+|q|²)A_α + F_α` whose forcing is the literal outer cell
  family of the trajectory.
* `galerkin_gram_flux_identity` — the exact temporal identity, with **no**
  hypothesis left for the caller:

  `∫ D_Gram = 2·resForm(A(t₀)) − 2·resForm(A(t₁)) + 4·∫ resForm(A, F)`.

* `galerkin_signed_gram_bound` — the assembled bound of
  `SignedGramWienerAssembly.sum_gram_debt_le_wiener` on the literal
  trajectory, with all of its analytic hypotheses (kinematic constraints, cell
  tangent, five interval-integrability conditions) discharged, and with the
  Wiener–energy budget `M` produced by compactness of the window.

## 3. What this does *not* close

The bound of `galerkin_signed_gram_bound` is **not uniform in the Galerkin
truncation**.  The constant `M` is obtained from continuity of
`‖u(t)‖_A⁴ E(t)` on a compact window for a *fixed* finite mode set.  The
repository's own
`WaleffeWienerSupercritical.wiener_norm_not_controlled_by_energy`
exhibits, for every `M`, a kinematically admissible unit-energy field whose
Wiener–energy budget exceeds `M`.  So no energy-based, cutoff-uniform version
of `M` can be extracted from this route as it stands.

Consequently:

* the finite-dimensional calculus leaf (differentiable trajectory, cell
  tangent, integrability, FTOC) is now genuinely closed;
* the surviving obstruction is the *supercritical* spacetime Wiener input, i.e.
  exactly the step where the last phase information is discarded;
* no cutoff-uniform absorption, no Package-A object, and no Clay-level
  statement is claimed here.
