# Navier–Stokes four-lane dashboard (A/B/C/D)

Status: live worker dashboard, non-promoting.  Last updated by the
`master-20dd / lean-7f60` intake round.  Nothing here promotes a statement from
provenance, a Boolean ledger, a conditional compiler surface, a similarly named
theorem, or another prover's receipt.

```text
A  unforced whole-space R³ regularity    independent obligation; cut frozen below
B  unforced periodic T³ regularity       active; S2b is the immediate priority
C  forced whole-space R³ breakdown       released-proof verification / donor lane
D  forced periodic T³ breakdown          released-proof verification / donor lane
```

## 0. Transfer firewalls (load-bearing, not decoration)

```text
B  ⇏ A          A ⇏ B
C  ⇏ A, B       D ⇏ A, B
source presence ⇏ same-object payment
provenance / alignment / authority ⇏ mathematical obligation
```

* No transport theorem between lanes exists in this project, and none is
  asserted.  A lane-crossing use would require a *typed same-object* statement
  identifying the two carriers' objects, not a name match or a shared geometry.
* The machine-checked part of the last firewall is
  `RequestProject.NavierStokes.ProofDebtRouter.no_receipt_to_theorem`
  (`RequestProject/NavierStokes/ProofDebtRouterMirror.lean`): a fully aligned,
  fully provenanced deferred receipt can be manufactured for `False`, so a
  receipt can never pay a mathematical obligation.
* The canonical Agda four-lane owner
  `DASHI.Papers.NavierStokes.FourLaneProofProgramExact` records the same
  firewalls, with `periodicBToWholeSpaceATransferConstructed = false`,
  `wholeSpaceAToPeriodicBTransferConstructed = false`,
  `forcedCDDoesNotSettleUnforcedAB = true`.  These are its own status
  constants; this project reproduces them as *statements about the source*, not
  as theorems.

---

## 1. Lane A — unforced whole-space `R³`: current cut, frozen

Lane A receives no primary proof budget this round.  The Agda coordinator marks
`wholeSpaceACurrentTerminalCutFrozen = false`, i.e. upstream has *not* frozen a
cut; the freeze below is this project's own Lean-side cut, recovered from the
A-side files that build here.  It is recorded so that later rounds resume from
it instead of re-deriving it, and so that no B-lane progress can be mistaken for
A-lane progress.

### A producer → compiler → consumer

| role | object | Lean carrier | status |
|---|---|---|---|
| producer (open) | **A₁** dissipation-growth bound `E′(r) ≤ (1+rD(r))·Q_∇(r)` for the actual cylinder dissipation | `ClayNS.critical_frequency_of_dissipation_growth`, `ClayNS.dissipation_growth_of_critical_frequency` (`CriticalGradientMonotonicity.lean`) | **unpaid**; proved *equivalent* to the critical-frequency almost-monotonicity target |
| producer (open) | **A-single** scale-invariant mixed-moment contraction `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ K∫ρ_ν‖W_⊥‖²`, `K<1` | `ClayNS.physical_gauss_nearfar_strict_relative_contraction` (`PhysicalGaussianNearFarRelativeBound.lean`) | **unpaid**; the two-hypothesis gate was reduced to this single one |
| compiler | almost-monotonicity / defect propagation from A₁ | `ClayNS.defect_propagates_of_dissipation_growth`, `ClayNS.totalDefect_le_of_dissipation` | proved, conditional on the producer |
| consumer | ancient-Liouville / blow-up rigidity chain | `RequestProject/NavierStokes/AncientLiouville.lean`, `BlowupCompactness.lean`, `CriticalElementRigidity.lean` | proved, conditional on the producers |
| no-go (kept) | the size-only defect route degenerates at the cascade endpoints (`M^{1/3}`) | `ClayNS.naive_defect_bound_degenerates` | proved |
| no-go (kept) | no kinematic one-step dyadic persistence | `ClayNS.no_kinematic_one_step_persistence` (`OneStepDyadicNoGo.lean`) | proved |
| no-go (kept) | cutoff optimisation buys nothing; the survivor is an amplitude (Reynolds) restriction | `ClayNS.gauss_nearfar_optimization_no_gain`, `ClayNS.gauss_relative_contraction_amplitude_no_go` | proved |

**A freeze statement.**  Lane A's first unresolved theorem is the pair of
producers above; everything downstream of them is already proved in this
project.  No lane-B object, including the S0–S2a control cut and the new
critical-weight results, is used anywhere in the A files, and no B→A transport
is constructed.

---

## 2. Lane B — unforced periodic `T³`: active

Control cut (upstream naming), with this project's independent Lean status:

| step | upstream state | this project's Lean carrier | status here |
|---|---|---|---|
| S0 literal finite `X_N, D_N, N_N` | source-written (Agda) | `GalerkinFlow.critEnergy`, `critDissipationRate`, `critProductionRate` (`CriticalWeightedGalerkin.lean`) | constructed on the literal Galerkin flow |
| S1a pointwise critical-energy split | source-written (Agda) | `GalerkinFlow.critEnergy_hasDerivAt` | **proved** |
| S1b integrated-energy identity | conditional compiler in Agda (`concreteScalarFTCInstalled = false`) | `GalerkinFlow.critEnergy_balance` | **proved unconditionally** in this carrier (library FTC + integral linearity) |
| S2a projected-pairing weld | source-written (Agda) | `GalerkinFlow.critProduction_pairing_symm`, `critProductionRate_eq_output_pairing` | **proved** |
| **S2b** `N_N ≤ a·D_N + ∫R406` | **open** | `ClayNS.Waleffe.S2bAbsorption` (statement), `retained_viscosity_budget` (consumer) | **open**; consumer proved, producer unpaid |
| S3 uniform initial critical ceiling | open | — | open |
| S4 positive retained viscosity `0 < 2ν − a` | open | appears as the coefficient in `retained_viscosity_budget` | open |

### New lane-B results this round (all built here, no `sorry`, axioms `propext, Classical.choice, Quot.sound`)

* **Shell laws paid.**  `waveMaxCoord_le_critWeight`, `critWeight_le_two_mul`:
  the two fields of the Agda record `DyadicShellBounds` are theorems here.
  `critWeight_add_le` adds the triad transfer bound `w(p+q) ≤ 2(w p + w q)`.
* **S1a/S1b.**  As above; S1b is the Lean-carrier certification of the calculus
  authorities that the Agda S1b compiler assumes.  It is *not* a transport of
  the Agda theorem: the objects are this carrier's own.
* **S2b structure.**  `critEnergyOf_scale`, `critDissipationOf_scale` (quadratic)
  and `critProductionOf_scale` (**cubic**) prove the homogeneity of the literal
  folds, and `no_subcubic_remainder_absorption` concludes: for a state of
  positive critical production, no state-independent `a` plus an at-most
  quadratic remainder can dominate the production.  Hence the S2b payment must
  come from a genuinely superquadratic remainder — consistent with the R406
  pair remainder being quintic — and cannot be a critical-energy reservoir.
* **The no-go is not vacuous.**  `critProductionOf_witField = 12` for an
  explicit divergence-free, real, six-mode triad state
  (`CriticalProductionWitness.lean`); with the constant weight the same fold is
  zero by `force_energy_neutral_of`, so the dyadic weight genuinely breaks
  energy neutrality.
* **Wiener `ℓ¹` route excluded uniformly.**  `exists_sum_inv_critWeight_ge`:
  `∑ 1/w(k)` over nonzero modes of the box of radius `N` is `≥ N/2`.
* **Cancellation-preserving form of the production.**
  `weighted_production_eq_weightDifference`: for a symmetric mode set carrying a
  supported, transverse, real field,
  `2∑_k w(k)Re⟨f_k,u_k⟩ = −∑_{(k,p)} (w(k) − w(k−p))·Re S(k,p)`.  Only weight
  differences across a triad leg drive the production; the constant-weight
  specialisation `weighted_production_const_eq_zero` recovers energy neutrality.
  This is an identity — no majorisation, so the signed structure the corpus
  insists on is preserved.
* **Localisation to the shell boundary.**
  `critProductionOf_eq_shellJump_sum`: every pair whose output and high leg lie
  in the same dyadic shell contributes exactly zero, so all of `N_N` is carried
  by shell-crossing pairs.
* **But no high-low commutator gain.**  `no_highlow_commutator_gain`: for the
  *sharp* dyadic weight the jump `|w(p+q) − w(q)|` is not bounded by any fixed
  multiple of `w(p)` (take `|p|_∞ = 1`, `|q|_∞ = 2^j`).  So the shell-boundary
  localisation cannot be converted into a gain by a Lipschitz estimate in the
  low leg: an S2b producer must either smooth the multiplier — paying the R517
  comparison to the physical `H^{1/2}/H^{3/2}` multipliers — or exploit signed
  cancellation inside the shell-boundary set itself.

### S2b producer search — result

Searched the whole imported corpus (Agda + Lean) for a *producer* of the literal
inequality.  Every occurrence found is one of:

| owner | form | verdict |
|---|---|---|
| `NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact` | `signedProductionEstimate` is a **record field** of `IntegratedSignedCriticalSlice`; `round104PhysicalUniformSignedCriticalProductionClosed = false` | hypothesis, not producer |
| `NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact` | transports an R104 slice by `subst` on a remainder equality; `round507LiteralR406RemainderSameObjectWeldClosed = false` | compiler |
| `NSTriadKNLuoCriticalProductionGronwallClosureExact` | `productionTax` is a **record field**; concludes the absorption budget | compiler (its Lean analogue here is `retained_viscosity_budget`) |
| `NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact` | states the target; `round410SignedPhaseSensitiveCancellationStillOpen = true` | target statement |
| `NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact`, R372/R303/R353 chain | accept the estimate as input | compilers |

**No historical or pre-release branch in the supplied corpus proves the literal
S2b inequality for the constructed `N_N`.**  Nothing was credited from a
similarly named signed scalar, a conditional record field, or a compiler.

---

## 3. Lanes C and D — forced breakdown, released-proof verification

C and D are not discovery lanes here.  Their current job is dependency closure,
source observation, honest adapter construction, and forcing-independent donor
mining.

### 3.1 Dependency closure — verified at source level

Full output: `tranche-20260915-20dd/AGDA_DEPENDENCY_AUDIT.txt`
(`scripts/agda_dep_audit.py`).  Transitive `DASHI.*` import closures, all with
**zero unresolved imports**:

| root | closure size | postulate-bearing modules in closure |
|---|---|---|
| `FourLaneProofProgramExact` | 512 | 10 |
| `NSClayFourAlternativeReleasedProofBidiExact` | 511 | 10 |
| `NSOpenAI2026ReleasedProofDependencyAtlasExact` | 514 | 10 |
| `NSOpenAI2026ReleasedClayCDTorus369BidiExact` | 325 | 8 |
| `NSTriadKNForcedBlowupR406BidiRound522Exact` | 276 | 8 |
| `NSReleasedCDToR406AdversarialUpdateBidiExact` | 513 | 10 |
| `NSTriadKNClayForcedBreakdownFormulationRound523Exact` | 1 | 0 |

The recurring postulate boundaries are
`NSTriadKNForcedTailPrimitiveEstimates`, `…ForcedTailConcreteIncidenceType`,
`…AdversarialRow/ColumnConcreteBounds`, `…AdversarialPrimitiveEstimates`,
`…ResidualPrimitiveEstimates`, `…TransitionConcreteBounds`,
`…TransitionPrimitiveEstimates`, plus `DASHI.Arithmetic.DeltaGrowth`,
`DASHI.Arithmetic.PrimeIndexedPressure`, and — in the B control-cut closures —
`DASHI.Foundations.RealAnalysisAxioms`, which is explicitly an axiom boundary
for real analysis.  Import closure does not prove *use*; establishing use or
non-use needs an Agda kernel, which does not exist in this environment.

### 3.2 Current source observations (appended, nothing rewritten)

* Declared status constants in `NSClayFourAlternativeReleasedProofBidiExact`:
  A and B are `openInDASHI4` against the Fefferman Clay description; C and D are
  `externalReleasedLeanProof4` against the released paper and Lean.  All four
  carry the final flag `false` (no DASHI closure).  Recorded as declared.

* The external released Lean sources that the C/D atlas describes
  (`NavierStokes/R3/Theorem.lean`, `ActualCandidate`, `CandidateBreakdown`,
  `ViscosityScaling`, `IntegratedDissipation`, `PeriodicPaperTheorem`,
  `PeriodizePDE`, `PeriodicViscosity`, `CandidateConsequences`) are **not
  present** anywhere in this project or in the delivered tranche.  Consequently
  **no independent build or kernel receipt for the released C/D proof is
  claimed or possible here**; the C/D material available is the DASHI atlas and
  BIDI records *about* it.
* The C/D atlas rows already classify every external dependency as
  `structuralDonorOnly`, `representationAdapterOpen`, `differentEquationClass`
  or `noRecoveredMatch`; the audit found no row upgraded to
  `sameObjectWeldClosed` in the new tranche, and this round created no such
  upgrade either.
* The 2026-09-15 `20dd` tranche changed 7 files relative to the previous
  `aa5f` tranche (`FourLaneProofProgramExact`, `TheoremInterfaceValidation`,
  three `R571` Gate-A crosswalk/aggregate owners, `R571RadialCurvatureBoundary`,
  and the control record); donor copies are preserved verbatim under
  `Provenance/tranche-20260915-20dd/donor-version/`.

### 3.3 Same-object / BIDI adapters — what is real

No new C/D → B or C/D → A adapter was constructed, because no same-object
equality was available to construct one from.  The only adapters this round are
*inside* lane B (S2a pairing symmetry; the S1b consumer), and the existing
router mirror.  A C/D adapter would require the external theorem's object to be
identified with a DASHI or Lean object by an equality proof; a shared periodic
geometry or a shared name is explicitly not enough.

### 3.4 Forcing-independent donor mining

| donor | content | forcing-independent? | use here |
|---|---|---|---|
| `NSTriadKNMixedHelicityQuarticFluxHomogeneityRound289Exact` + `NSSignedCrossBeforeForcingNormHomogeneityBidiExact` | degree bookkeeping: companion cell `2`, nonlinear tangent `3`, forcing work `5`, norm-square `6`, its tangent `7` — as `Nat` arithmetic on declared degrees | yes: pure homogeneity discipline | **used**: this round *proves* the degree claims for the literal unforced folds (`critProductionOf_scale` cubic, energy/dissipation quadratic) and turns them into the S2b no-go.  The Agda owners remain bookkeeping; the Lean theorems are about the actual functionals |
| `NSTriadKNClayForcedBreakdownFormulationRound523Exact` | forced-breakdown formulation, self-contained (closure size 1, no postulates) | no: forced-specific | not used for B |
| `NSTriadKNForcedBlowupR406BidiRound522Exact`, `NSReleasedCDToR406AdversarialUpdateBidiExact` | forced R406 adversarial updates | no: hypotheses mention the forcing term | not used for B |
| forced-tail / adversarial primitive estimate modules | postulated estimate surfaces | no, and postulated | explicitly excluded from any B payment |

Rule applied: a donor lemma is admissible for B only if its hypotheses survive
deleting the external force.  Degree/homogeneity bookkeeping survives; every
estimate whose statement quantifies over a forcing profile does not.

---

## 4. Unpaid leaves, by lane

```text
A   A₁ dissipation-growth bound;  A-single mixed-moment contraction K < 1
B   S2b (primary), S3 uniform initial ceiling, S4 retained viscosity 2ν − a > 0
    plus, for the Agda carrier only: concrete scalar FTC / integration linearity
    (paid in the Lean carrier this round, not transported)
C   independent build/kernel receipt for the released proof (sources absent here)
D   same as C; plus any D → B donor would still need a same-object transport
```

No Clay closure, no global regularity on either unforced lane, and no Agda
kernel receipt is claimed anywhere in this round.
