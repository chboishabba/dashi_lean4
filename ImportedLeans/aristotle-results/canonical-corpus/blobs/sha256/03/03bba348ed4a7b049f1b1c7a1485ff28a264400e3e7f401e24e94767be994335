# Navier–Stokes lane: closure audit and first unresolved theorem

This document records a full trace of the periodic Clay Navier–Stokes lane from
the declared target down to its leaves, distinguishing

* **genuine constructive Agda** — definitions and theorems with real proof
  terms;
* **conditional bridges** — theorems whose hypotheses are record fields holding
  the entire mathematical content;
* **postulates** — `postulate` blocks;
* **Boolean bookkeeping / receipts** — `Bool` constants together with `refl`
  proofs that they equal `true`/`false`.

Everything asserted below was checked against the sources; the Agda facts marked
*verified* were re-typechecked here under **two** toolchains — Agda 2.6.4.3 with
agda-stdlib 2.1, and Agda 2.7.0.1 with agda-stdlib 2.3 — in both cases with a
build-support shim, kept outside the project, for the module
`Data.Rational.Tactic.RingSolver` that the bundle imports but that no released
standard library provides (see §5).

## Verdict

**No machine-checkable proof of the periodic Clay target can be returned.** The
target-critical obligations do not compile as theorems; they do not exist as
Agda types at all at the frontier. The precise first unresolved theorem is
identified in §3.

## 1. What the declared target actually says

`DASHI/Physics/Closure/NSTriadKNFeffermanPeriodicClayStatementExact.agda`
defines

```agda
FeffermanPeriodicClayStatementB : FeffermanPeriodicClayCarrier → Set₁
```

The record `FeffermanPeriodicClayCarrier` supplies *every* mathematical notion
in the Clay problem as an abstract field: `Viscosity : Set`,
`PositiveViscosity : Viscosity → Set`, `DatumSmoothOnThreeTorus`,
`DatumDivergenceFree`, `VelocitySmoothOnThreeTorusTimesNonnegativeTime`,
`SolvesThreeDimensionalMomentumEquationWithZeroForce`,
`IncompressibleAtEveryNonnegativeTime`, `AttainsInitialDatumAtTimeZero`, …
None is tied to real numbers, function spaces, derivatives or the
Navier–Stokes operator.

*Verified consequence.* `DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit.agda`
(added by this audit, typechecks, no postulates) constructs the degenerate
carrier interpreting every predicate as `⊤` and exhibits a total inhabitant

```agda
trivialCarrierSatisfiesLiteralClayStatement :
  Clay.FeffermanPeriodicClayStatementB trivialCarrier
```

Hence inhabiting `FeffermanPeriodicClayStatementB` for *some* carrier proves
nothing about fluids. All mathematical force would sit in an analytic carrier
instance.

*Verified search.* Across all 12 038 `.agda` files of the supplied bundle, the only
occurrences of `FeffermanPeriodicClayCarrier` are its declaration and five
*parameter* positions (`NSTriadKNLuoClayEndToEndCompositionRound23Exact`,
`NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact`,
`NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact`,
`NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact`,
`NSTriadKNClayProofSearchRound85`). **No analytic carrier instance exists.**

## 2. The terminal composition is a conditional bridge

`NSTriadKNLuoClayEndToEndCompositionRound23Exact.agda` (typechecks) proves

```agda
inRepoPathClosesLiteralFeffermanPeriodicB :
  InRepoClayPathInputs legacy clay → Clay.FeffermanPeriodicClayStatementB clay
```

This is genuine Agda, but `InRepoClayPathInputs` is a record whose fields are
the mathematics:

* `legacyUniformPhysicalConstruction : Global.UniformGlobalPhysicalSolutionInputs legacy`;
* `legacyToLiteralAdapter`, `centeredDatum…`, and
* `restoreGalileanSolution` — the Galilean restoration is *assumed*, not derived.

Unrolling one level, `NSTriadKNLuoGlobalPhysicalSolutionReductionExact.agda`
defines `GlobalPhysicalSolutionPrimitiveInputs`, whose fields include

```agda
InfiniteMaximalTime : Set
infiniteMaximalTime : InfiniteMaximalTime          -- line 34
velocitySmoothFromSobolevAndParabolicBootstrap : …
pressureFromProjectedVelocity : …
velocityPressureSolveOriginalEquation : …
```

i.e. global existence, the parabolic bootstrap and the pressure recovery are all
assumed fields. The "reduction" theorem `globalPhysicalSolutionWitness` merely
repackages them into a record.

*Verified search.* `UniformGlobalPhysicalSolutionInputs`,
`GlobalPhysicalSolutionPrimitiveInputs` and `InRepoClayPathInputs` are never
inhabited anywhere in the bundle.

## 3. First unresolved theorem

Two readings, both recorded because they answer different questions.

### 3.1 In dependency order from the target

> **First unresolved theorem.** The inhabitation of
> `DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact.GlobalPhysicalSolutionPrimitiveInputs`
> for the physical carrier, and specifically its field
> `infiniteMaximalTime : InfiniteMaximalTime` — that the maximal existence time
> of the smooth periodic solution is infinite.

Everything strictly above this in the chain (adapter, mean-zero/Galilean
reduction, end-to-end composition, the literal statement type) is either record
plumbing or a conditional bridge. Nothing below it is inhabited. This field is
the Clay problem itself, so the repository's chain does not reduce the problem
to anything smaller at this level; the reduction work lives in the parallel
"physical" development audited next.

### 3.2 In the repository's own intended route (the informative answer)

The physical development has advanced to Round 106. Its own frontier module
`DASHI/Physics/Closure/NSTriadKNClayFrontierRound105Exact.agda` names exactly
two remaining theorem-sized obligations, and both are **Boolean constants set to
`false`**, not Agda types:

```agda
round105PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed : Bool   -- line 126
round105PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed = false  -- line 127
round105UniformGalerkinCriticalBarrierClosed : Bool                        -- line 129
round105UniformGalerkinCriticalBarrierClosed = false                       -- line 130
```

> **First unresolved theorem on the intended route.**
> `PhysicalWeightedPositiveWaleffeNetworkForcingBudget`: on the complete
> physical Galerkin network, the correctly weighted positive part of the
> Waleffe network forcing has a bound
> `∑_cells ∫₀^T (F_network)₊ ≤ endpoint data`, uniform in the shell cutoff, the
> Galerkin cutoff and the hypothetical maximal time.

Status of this obligation in the bundle:

* it has **no Agda type** anywhere — only the Boolean above;
* it has **no postulate** — so it cannot even be assumed and propagated;
* it has **no producer**;
* the module that would consume it,
  `NSTriadKNIntegratedHeterochiralPhasePaymentRound105Exact.agda`, proves only
  the finite list-arithmetic consequence
  `ν ∑ ∫ P_adverse ≤ 2 ∑ A₊(0) + 2 ∑ ∫ (F_network)₊`
  over abstract rational per-cell data (`finiteAdverseProductionPaidByInitialPhaseAndNetworkForcing`).

The second obligation, `B` (three-piece critical Sobolev/Simon upgrade on the
`G12` limit element), is likewise a Boolean `false`.

## 4. Status of the specific items requested

| Requested closure | Actual status in the bundle |
| --- | --- |
| Cutoff-uniform physical nine-owner absorption with `delta_NS > 0` | `NSTriadKNNineOwnerCriticalAbsorptionRound28Exact.nineOwnerStrictCriticalEstimate` and `nineOwnerRemainingViscosityPositive` are **genuine constructive Agda** and typecheck (verified). They are *rational arithmetic*: `ℚ`-valued `production`, `eta`, `dissipation`, `integralCritical`, and they take the nine owner estimates and the strict budget `∑ eta_i < 1` as **hypotheses** (`NineOwnerEstimateFamily`, `StrictAdmissibleOwnerBudget`). No module produces a `NineOwnerEstimateFamily` from PDE quantities, and `ℚ` cannot express a function-space norm. So `delta_NS > 0` is proved as algebra, never for a physical family. |
| Non-circular high–high estimate | Open. The bundle instead contains several **genuine no-go results** on this route (`…HHBadSuperlevelMonotonicityNoGoRound47Exact`, `…HHBadHeatHalfPositiveForcingNoGoRound50Exact`, `…WaleffePhaseLockingNoGoRound95Exact`, `…WaleffeLeithPointwiseMobilityNoGoRound104Exact`), and `NSTriadKNGlobalDangerBarrierEquivalenceRound105Exact` records that a bound on the global signed surplus is *equivalent* to the critical barrier, i.e. circular unless obtained independently. |
| `theta` preservation | Only receipts (`NSThetaImpliesTailDecayReceipt`, `NSThetaTailToBKMBridgeReceipt`, `FinalAnalyticWallsReceipt`): Boolean status records and conditional bridges. |
| Shell/Galerkin and Archimedean limits | Open; `ArchimedeanFlatLimitCandidatesReceipt` and the shell-limit items `L18`/`L19` of the ladder are unimplemented. `NSTriadKNCriticalCompactnessSerrinRound29Exact` proves only the `ℚ`-budget algebra and explicitly states that "the physical negative Sobolev estimate, Aubin–Lions–Simon compactness and periodic Serrin continuation remain separate producers". |
| BKM/Serrin continuation | Conditional bridge only. `NSTriadKNBKMContinuation.agda` stores `bkmIntegralFinite : Set` and `SmoothContinuationPast : Set` as abstract fields with the implications between them as further fields; the composition theorems just apply those fields. |
| Exact Fefferman witness | Not inhabited; see §1–§2. |

Quantitatively, the NS lane contains **53 `postulate` blocks across 31 files**
(chiefly the `…Boundary.agda` and `…PrimitiveEstimates.agda` modules, which are
explicitly labelled as open analytic obligations). The Round-23 Clay chain
itself is postulate-free — because it assumes its content through record fields
instead.

## 5. Compile status of the supplied Agda bundle

This section is a correction of a natural first impression. The failures listed
here are **not** standard-library version drift; they are defects that no
version of Agda accepts, and they mean that large parts of the bundle —
including the whole Round-102…106 frontier chain — have never been typechecked
in the form supplied.

**(a) A standard-library module that does not exist.** 1 320 of the 12 038 supplied
`.agda` files import `Data.Rational.Tactic.RingSolver`. That module is present
in **no** released agda-stdlib: 2.1, 2.2 and 2.3 all ship
`Data.Nat.Tactic.RingSolver` and `Data.Integer.Tactic.RingSolver` only, and the
bundle does not ship its own copy. Verification here therefore used a shim,
written for this audit and deliberately kept outside the project, that
reconstructs the module from the generic `Tactic.RingSolver` over
`Data.Rational.Properties.+-*-commutativeRing`.

**(b) Malformed ring-solver calls.** `Tactic.RingSolver.solve` requires its
first argument to be a list of *free variables* of the context. At least **227
files (223 of them in the Navier–Stokes lane)** call it with record projections
instead, e.g.

```agda
solve (eigenvalue x ∷ energy x ∷ transfer x ∷ [])
```

Every such call is rejected outright ("Malformed call to solve. First argument
should be a list of free variables"), under Agda 2.6.4.3 and 2.7.0.1 alike.
Repairing one is not mechanical: the ring identity has to be restated over
genuine `ℚ` variables (the solver quotes the goal without unfolding the
surrounding definitions) and then instantiated.

**(c) Consequence for the frontier.** The import closure of the frontier module
`NSTriadKNClayFrontierRound105Exact` contains 150 in-repo modules, **22** of
which carry malformed `solve` calls. So the Round-102…106 development — the
route on which the remaining obligations of §3.2 live — does not compile as
supplied.

**(d) Genuine defects repaired in this pass** (all three fixes preserve every
statement; they change only how the proofs are written):

* `DASHI/Physics/Closure/NSTriadKNComplex3FieldAlgebra.agda` — a scope error:
  inside the `where` block of `hermitianAddLeft`, `conjugateVectorAdd` was used
  at line 679 while its type signature appeared only at line 706. Agda has
  never permitted a forward reference in a `where` block without a preceding
  signature (confirmed on a minimal example). Fixed by moving the definition
  above its first use.
* `DASHI/Physics/Closure/NSTriadKNFiniteRadialTransferExteriorRound102Exact.agda`
  — malformed `solve` calls. Repaired: the four ring identities are now stated
  over `ℚ` variables (`headExteriorNil`, `headExteriorStep`, `defectStep`) and
  the recursions are threaded with `trans`/`cong` instead of `rewrite`. The
  module now typechecks.
* `DASHI/Physics/Closure/NSTriadKNThreeRadiusTransferExteriorRound102Exact.agda`
  — malformed `solve` calls **and** use of `_/_` without importing it.
  Repaired the same way (`threeRadiusStep`, `shiftDefectStep`, `shiftMinorStep`,
  `conservationStep`), plus the missing import. The module now typechecks.
* The missing `_/_` import was fixed in eight further Navier–Stokes modules
  where the same omission occurs.

The remaining 221 malformed files were not repaired: each needs its own
restatement, and doing so would not change any conclusion of §§1–4 — the
obligations at the frontier are Boolean constants, not theorems, so making the
chain compile would only confirm that they are set to `false`.

**(e) What does compile.** Under Agda 2.7.0.1 + agda-stdlib 2.3 + the shim, the
following were typechecked successfully in this pass:
`NSTriadKNFeffermanPeriodicClayStatementExact`,
`NSTriadKNLuoClayEndToEndCompositionRound23Exact` (the whole Round-23 Clay
chain), `NSTriadKNNineOwnerCriticalAbsorptionRound28Exact`,
`NSTriadKNBKMContinuation`, and the newly added
`DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit`.

## 6. Constructive material added by this pass

Every item below compiles and contains no `sorry`, no postulates and no axioms
beyond the standard ones.

1. `DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit.agda` (Agda, verified):
   the vacuity result of §1.
2. `RequestProject/NavierStokes/ClayPeriodic.lean` (Lean 4 + Mathlib, verified):
   * a genuinely analytic statement of the target — `ClayNS.IsNSSolution` writes
     `∂_t u + (u·∇)u = -∇p + νΔu`, `div u = 0` with Fréchet derivatives on
     `ℝ × ℝ³`, and `ClayNS.ClayPeriodicTargetB` is Fefferman's periodic
     alternative (B) with no mean-zero, uniqueness or energy hypothesis added;
   * `ClayNS.isNSSolution_const`, a non-vacuity check for the definitions;
   * **`ClayNS.isNSSolution_galileanShift`** — the L1 mean/Galilean restoration
     step, *derived* rather than assumed: if `(V,P)` solves the system then so
     does `u(t,x) = V(t, x - t·m) + m`, `p(t,x) = P(t, x - t·m)`. In the Agda
     development this same step is the assumed field `restoreGalileanSolution`
     of `InRepoClayPathInputs`;
   * `ClayNS.admissibleDatum_add_const` and
     `ClayNS.clayPeriodicTargetB_of_centred`, which turn that derivation into
     the reduction "solve the centred problem ⇒ solve the Clay problem".

3. `RequestProject/NavierStokes/PressurePoisson.lean` (Lean 4 + Mathlib,
   verified): **`ClayNS.pressure_poisson`** — for every smooth divergence-free
   solution of the momentum equation,

   `Δp = - ∑_{i,j} (∂_i u_j)(∂_j u_i)`.

   This is the pressure recovery that the Agda development assumes through the
   fields `pressureFromProjectedVelocity` and `PressurePoissonEquation` of
   `GlobalPhysicalSolutionPrimitiveInputs`.  The file also contains the
   supporting calculus that had to be built: commutation of derivatives with
   finite sums and with coordinate projections (`dvec_sum`, `dvec_coord`),
   symmetry of second derivatives in directional form (`dvec_comm`), the
   product rule, and `div ∂_t u = ∂_t div u`, `div Δu = Δ div u`,
   `div ∇p = Δp`, `div (u·∇)u = ∑ (∂_i u_j)(∂_j u_i) + (u·∇) div u`.

4. `RequestProject/NavierStokes/Vorticity.lean` (Lean 4 + Mathlib, verified):
   **`ClayNS.vorticity_equation`** — the vorticity transport equation

   `∂_t ω + (u·∇)ω = (ω·∇)u + ν Δω`,   `ω = curl u`,

   derived for every smooth divergence-free solution.  This is the analytic
   input of the Beale–Kato–Majda continuation criterion, which the Agda
   development carries as the abstract fields `bkmIntegralFinite` and
   `SmoothContinuationPast` of `NSTriadKNBKMContinuation.agda`.  The vortex
   stretching term comes out of an explicit algebraic identity
   (`ClayNS.stretching_identity`) in which incompressibility enters with the
   multiplier `ω_i`; it is stated and proved separately so that the role of the
   constraint is visible.

5. `RequestProject/NavierStokes/EnergyIdentity.lean` (Lean 4 + Mathlib,
   verified): **`ClayNS.local_energy_identity`** — the pointwise energy
   identity, for `e = ½|u|²`,

   `∂_t e + (u·∇)e = - u·∇p + ν ( Δe - ∑_{a,j} (∂_j u_a)² )`,

   derived from the momentum equation alone (no incompressibility needed), and
   **`ClayNS.pressure_work_divergence`** — with `div u = 0` the pressure work is
   a pure divergence, `u·∇p = div (p u)`.  Together these are the pointwise
   form of the a priori energy estimate on which Leray–Hopf theory, the
   Galerkin scheme and every absorption argument in the ladder depend; in the
   bundle the energy budget appears only as `ℚ`-valued record data.

6. `RequestProject/NavierStokes/EnergyIdentity.lean` also contains the general
   lemma from which both quadratic balances follow,
   **`ClayNS.transported_quadratic_identity`**: if every component of a field
   `W` is transported by `u` with source `S` and viscosity `ν`, then
   `q = ½|W|²` satisfies

   `∂_t q + (u·∇)q = W·S + ν ( Δq - ∑_{a,k} (∂_k W_a)² )`,

   and its second instance **`ClayNS.local_enstrophy_identity`** — for every
   smooth divergence-free solution, with `ω = curl u` and `E = ½|ω|²`,

   `∂_t E + (u·∇)E = ω·(ω·∇)u + ν ( ΔE - ∑_{a,k} (∂_k ω_a)² )`.

   The first right-hand term is the vortex-stretching production and the last
   is the enstrophy dissipation: this is exactly the pointwise balance whose
   integrated, cutoff-uniform form the ladder's nine-owner absorption arguments
   assert over rational cell data (`NSTriadKNNineOwnerCriticalAbsorptionRound28Exact`)
   without ever deriving it from a PDE.  Deriving the pointwise balance does
   *not* supply the absorption theorem: the gap is the uniform control of
   `∫ ω·(ω·∇)u` by the dissipation, which is precisely the critical obstruction.

These replace five target-critical placeholders by actual derivations.  What
they do **not** do is close §3: the missing content there is the passage from
pointwise identities to *uniform-in-cutoff* estimates in function-space norms
(integration over the torus, Sobolev/interpolation inequalities, compactness),
which is open mathematics, not missing plumbing.  In particular none of the
derivations above yields the cutoff-uniform bound
`PhysicalWeightedPositiveWaleffeNetworkForcingBudget` of §3.2, nor global
existence (`infiniteMaximalTime`) of §3.1.

## 7. Constructive material added by the continuation pass

The following Lean 4 + Mathlib modules were added after §6.  All of them build
inside the project (`lake build RequestProject`), contain no `sorry`, no
`axiom`, no `postulate` and no `@[implemented_by]`, and every theorem was
checked with `#print axioms` to depend only on `propext`, `Classical.choice`
and `Quot.sound`.  They move the development from *pointwise* identities to
*global* (integrated) balances on the torus — the level at which the Clay
ladder's estimates are actually formulated.

7. `RequestProject/NavierStokes/PeriodicIntegral.lean` — the analytic toolkit
   for the periodicity cell `[0,1]³`:
   * `ClayNS.cellInt`, with its linearity, monotonicity and positivity lemmas;
   * **`ClayNS.cellInt_divergence_eq_zero`** — the divergence theorem on the
     torus: for a `C¹` `ℤ³`-periodic triple of scalar fields, `∫_cell ∑ᵢ ∂ᵢ Fᵢ
     = 0`, obtained from Mathlib's divergence theorem on a box by cancelling
     the opposite faces;
   * `ClayNS.cellInt_dvec_eq_zero` — integration by parts in one direction;
   * **`ClayNS.hasDerivAt_cellInt`** — differentiation under the cell integral
     for a smooth spacetime field, and `ClayNS.continuous_cellInt`.

8. `RequestProject/NavierStokes/GlobalEnergy.lean` — the global balances:
   * **`ClayNS.global_quadratic_balance`** — for a quadratic density
     `q = ½|W|²` transported by a divergence-free periodic velocity with source
     `S`, `d/dt ∫_cell q = ∫_cell W·S − ν ∫_cell |∇W|²`.  This is the integrated
     counterpart of `transported_quadratic_identity` and is the single lemma
     from which the energy and enstrophy balances below are instances;
   * **`ClayNS.energy_balance`** — `d/dt ∫_cell ½|u|² = − ν ∫_cell |∇u|²`, with
     `ClayNS.cellInt_pressure_work_eq_zero` isolating the fact that the pressure
     work is a pure divergence and integrates away;
   * **`ClayNS.energy_antitone`**, **`ClayNS.energy_le_initial`** — the a priori
     energy inequality `E(t) ≤ E(0)`;
   * **`ClayNS.energy_dissipation_integral`** — the integrated (Leray) energy
     equality `E(t) + ν ∫₀ᵗ ∫_cell |∇u|² = E(0)`;
   * **`ClayNS.meanVel_const`** — conservation of the mean velocity, the
     invariant behind the Galilean/mean-zero reduction of §6.2;
   * **`ClayNS.enstrophy_balance`** — `d/dt ∫_cell ½|ω|² = ∫_cell ω·(ω·∇)u
     − ν ∫_cell |∇ω|²`.

9. `RequestProject/NavierStokes/Continuation.lean` — the conditional
   continuation estimates:
   * `ClayNS.stretching_bound` — the algebraic inequality
     `∑_a w_a ∑_j w_j D_{ja} ≤ 3M|w|²` for `|D_{ja}| ≤ M`;
   * **`ClayNS.enstrophy_production_le`** — `∫_cell ω·(ω·∇)u ≤ 6M · enstrophy`
     when `|∇u| ≤ M` at the time considered;
   * **`ClayNS.enstrophy_gronwall`** — `enstrophy(t) ≤ enstrophy(0)·e^{6Mt}`;
   * **`ClayNS.enstrophy_gronwall_integral`** — its BKM/Serrin-type
     time-integrated form `enstrophy(t) ≤ enstrophy(0)·exp(6 ∫₀ᵗ M)` for a
     continuous time-dependent gradient bound `M(s)`.

   These are *conditional*: they control the enstrophy while a gradient bound
   holds.  They do not supply the bound, which is the open part.

10. `RequestProject/NavierStokes/CellVanishing.lean` — the bridge from
    energy-norm statements to pointwise ones:
    **`ClayNS.eq_zero_of_cellInt_eq_zero`**, a continuous nonnegative periodic
    field with vanishing cell integral vanishes identically (vanishing on the
    closed cell, since the cell is the closure of its interior and Lebesgue
    measure is positive on open sets, plus invariance under the full lattice
    `ℤ³`).

11. `RequestProject/NavierStokes/Uniqueness.lean` — uniqueness, which every
    continuation and compactness step of the ladder silently uses:
    * **`ClayNS.difference_transport`** — the difference `w = u − v` of two
      solutions satisfies `∂_t w_a + (u·∇)w_a = −(w·∇)v_a − ∂_a(p−q) + νΔw_a`;
    * **`ClayNS.difference_energy_zero`** — by the energy method plus Grönwall,
      the cell energy of `w` vanishes for `t ≥ 0` when the data agree and `∇v`
      is bounded;
    * **`ClayNS.velocity_eq_of_same_datum`** — hence `u = v` pointwise.

12. `RequestProject/NavierStokes/ExactSolution.lean` — an exact witness that is
    not constant: **`ClayNS.isNSSolution_shearWave`** proves that
    `u(t,x) = e^{−4π²νt} sin(2πx₃) e₁`, `p = 0` is a global smooth
    `ℤ³`-periodic solution for every viscosity `ν`, with
    `ClayNS.admissibleDatum_shearWave` for its datum and
    `ClayNS.shearWave_ne_const` recording non-constancy.  This strengthens the
    non-vacuity check `isNSSolution_const` of §6.2 to a genuinely dissipative
    solution.

13. `RequestProject/NavierStokes/EnstrophyDissipation.lean` — the identification
    of the enstrophy with the energy dissipation:
    **`ClayNS.cellInt_gradSq_eq_two_enstrophy`** proves `∫_cell |∇u|² = 2 ∫_cell
    ½|ω|²` for smooth periodic divergence-free fields.  The proof is the
    pointwise algebraic identity `|ω|² = ∑_{p,q}(∂_p u_q)² − ∑_{p,q}(∂_p u_q)
    (∂_q u_p)` together with `ClayNS.cellInt_cross_gradient_eq_zero`, which
    observes that the cross term is `div ((u·∇)u)` when `div u = 0` and hence
    integrates to zero on the torus.  Consequences:
    **`ClayNS.energy_balance_enstrophy`** (`d/dt E = −2ν · enstrophy`) and
    **`ClayNS.energy_enstrophy_integral`** (`E(t) + 2ν ∫₀ᵗ enstrophy = E(0)`),
    which is the form in which the energy budget is used in the ladder.

### What this does *not* close

The verdict of §3 is unchanged.  None of the material above supplies

* global existence (`infiniteMaximalTime` of §3.1);
* the cutoff-uniform nine-owner absorption bound with `delta_NS > 0` of §3.2;
* a non-circular high-high estimate, `theta` preservation, or the shell/Galerkin
  and Archimedean limits;
* an unconditional BKM/Serrin continuation (items 9 above are conditional on a
  gradient bound that is exactly what has to be proved).

Accordingly **no machine-checkable proof of the periodic Clay target is
returned**, and the first unresolved theorem is still the one identified in §3.
