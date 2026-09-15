# The unforced DASHI Navier–Stokes A programme — Lean receipts

Session deliverable: a new opt-in Lean library `NSUnforced`
(`Lean/NSUnforced/`, declared in the root `lakefile.toml`), containing eight
modules, no `sorry`, no project axiom, no `native_decide`, no
`@[implemented_by]`.  Every declaration listed below compiles in this tree and
audits to `[propext, Classical.choice, Quot.sound]`
(`Lean/NSUnforced/AxiomAudit.lean`, built).

Nothing in this library imports, cites or consumes the published forced
breakdown C/D lane, and nothing in it touches Yang–Mills material.  The OpenAI
source-head record `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` in
`NS_OPENAI_ARCHAEOLOGY.md` was read but not modified; no C/D result is used to
pay A1 or A2.

---

## 1. Classification of each receipt

| # | Declaration | Class | Kind |
|---|---|---|---|
| 1 | `fullSquareSum_eq_diag_add_offDiag` | infrastructure | exact identity |
| 2 | `fullSquareSum_transpose` | infrastructure | exact identity |
| 3 | `fullSquareSum_two_add_transpose` | infrastructure (A1 carrier) | exact identity |
| 4 | `fullSquareSum_gram_collapse` | **A1** | exact signed identity |
| 5 | `abs_fullSquareSum_gram_collapse_le` | **A1** | post-collapse majorisation |
| 6 | `fullSquareSum_rankOne_collapse` | infrastructure | exact identity |
| 7 | `abs_multiplierDifference_homochiral_le` | **A1** | gain estimate |
| 8 | `sum_multiplierDifference_homochiral_vanishes` | **A1** | exact cancellation |
| 9 | `heterochiral_multiplierDifference_not_output_controlled` | **A1 — decisive typed obstruction** | refutation |
| 9a | `norm_commutatorCarrier_homochiral_le` | **A1** | gain estimate |
| 9b | `sum_commutator_square_homochiral_le` | **A1** | forcing-side square with output gain |
| 9c | `norm_weighted_sum_sq_le` | infrastructure | weighted Cauchy–Schwarz |
| 9d | `sum_channel_sq_le_schur` | **A1** | Schur test on the Gram weights |
| 9e | `channel_energy_receipt` | **A1** | energy clause from the Schur test |
| 10 | `energy_le_exp_of_deriv_le` | infrastructure | Grönwall |
| 11 | `four_integral_forcing_le` | **A1** | budget engine |
| 12 | `pointwise_absorption_of_channel_squares` | **A1** | Young/Schur step |
| 13 | `budget568_of_uniform_absorption` | **A1 reduction** | pays the R568 record |
| 14 | `budget568_of_channel_control` | **A1 reduction** | pays the R568 record |
| 15 | `a1_of_channelObligation` | **A1 frontier** | frontier ⇒ A1 |
| 16 | `critical_cell_pointwise_payment` | **A2** | geometric pointwise payment |
| 17 | `a2_uniform_critical_ceiling` | **A2 reduction** | pays the R372/R414 critical record |
| 18 | `dualPayment_of_receipts` | consumer composition | R414 |
| 19 | `a1_does_not_pay_a2` | control-record enforcement | refutation |
| 20 | `a2_does_not_pay_a1` | control-record enforcement | refutation |

No entry above is an A1 or A2 *payment*.  Items 13–15 and 17 are reductions:
they discharge the endpoint **given** a named residual hypothesis.  The
residual hypotheses are stated exactly in §4.

---

## 2. Endpoint, hypotheses, consumer and lineage, per receipt

### A1 carrier — the literal R571 signed ±y multiplier-difference route

*Source lineage.*  `R106` (projected helical self-forcing vector),
`R311` (`signedRadius plus r = r`, `signedRadius minus r = -r`,
`innerMultiplierDifference sa sb ra rb = signedRadius sb rb - signedRadius sa ra`),
`R571` (`NSTriadKNInnerHelicalComponentCommutatorRound571Exact`, four sign
pairs from helical bilinearity), and the homochiral adaptor
`NSTriadKNR571HomochiralRadialIncrementSpecializationExact`.

*Endpoint proved.*  On a triad `k + p + q = 0` in any seminormed group,

```
|multiplierDifference s s ‖p‖ ‖q‖| ≤ ‖k‖        (abs_multiplierDifference_homochiral_le)
multiplierDifference s s ra rb + multiplierDifference s s rb ra = 0
                                               (sum_multiplierDifference_homochiral_vanishes)
```

The first is the one derivative of *output* gain the commutator-only route
buys; the second is the exact signed cancellation the control record requires
to be preserved before majorisation.

*Decisive typed obstruction.*  For every `M` there is a genuine triad with
`‖k‖ = 1` on which the heterochiral multiplier difference exceeds `M‖k‖`
(`heterochiral_multiplierDifference_not_output_controlled`, witness
`k = 1, p = n+1, q = −(n+2)`).  Consequence, stated plainly: **the literal
R571 carrier alone cannot pay `CommutatorOnlySpacetimeBudget568`.**  Any A1
route must treat the heterochiral rows by a separate mechanism — the R577
four-sign receipt, or a cancellation internal to the heterochiral block.  This
converts the "R577 is a fallback, not mandatory" instruction into a checkable
statement: a *purely homochiral* gain argument is provably insufficient, so the
sign split (or an equivalent) is forced.

### A1 collapse — signed before positive

*Source lineage.* `R543.fullSquareSum` (full ordered square),
`R566.forcingPairScalarized`
(`forcingPair α β = pairResolvent α β · ⟪doubleForcing α, doubleCell β⟫`, with
`pairResolvent` symmetric), `R567.fullPairScalarIsFourForcing`
(`Full(pairScalar) = 4 · Full(forcingPair)`), `R503`/`R572` spectator-row and
compiler infrastructure (which is what supplies a Gram factorisation of the
symmetric resolvent).

*Endpoint proved.*  If `ρ a b = ∑_{j∈J} r j a · r j b` then

```
fullSquareSum (fun a b => ρ a b * ⟪D a, C b⟫) s
  = ∑_{j∈J} ⟪ ∑_{a∈s} r j a • D a , ∑_{b∈s} r j b • C b ⟫
```

exactly — no absolute value, no norm, no estimate
(`fullSquareSum_gram_collapse`).  Only then is Cauchy–Schwarz applied
(`abs_fullSquareSum_gram_collapse_le`).  The literal factor `4` of the R568
endpoint is re-derived over `ℝ` by `fullSquareSum_two_add_transpose`.

*Consumer.*  `pointwise_absorption_of_channel_squares`, then
`budget568_of_channel_control`.

### A1 engine — cutoff-uniform spacetime budget

*Source lineage.*  R557/R565/R553 (reduction of the literal live R406
trajectory to this single spacetime debt), R567 (the factor four), R495
(integration transport authority), R500/R503 (integrated direct/resolvent
consumers), R572 (direct leaf-A compiler).

*Endpoint proved* (`four_integral_forcing_le`).  With `0 < ν`, `0 ≤ ε < 2ν`,
`0 ≤ K`, `E, D, G : ℝ → ℝ`, `E ≥ 0`, `D ≥ 0`, `D`, `G` continuous,

```
E'(t) = −2ν D(t) + 4 G(t)          (Galerkin energy balance)
4 G(t) ≤ ε D(t) + K E(t)           (pointwise absorption receipt)
E(0) ≤ E₀
```

imply, for every `T ≥ 0`,

```
4 ∫₀ᵀ G ≤ commutatorBudget ν ε K E₀ T
        = (2ν/(2ν−ε)) · ( εE₀/(2ν) + K E₀ T e^{KT} ).
```

The right-hand side mentions only `ν, ε, K, E₀, T`.  Cutoff-independence is
therefore structural, not asserted.

*Consumer.*  `budget568_of_uniform_absorption`, which returns the Lean form of
the Agda record

```
structure CommutatorOnlySpacetimeBudget568 (globalForcingFull : ℕ → ℝ → ℝ) where
  bound  : ℝ → ℝ
  budget : ∀ N T, 0 ≤ T → 4 * ∫ t in 0..T, globalForcingFull N t ≤ bound T
```

— the bound's type has no cutoff argument, exactly as
`cutoffIndependentCommutatorBound568 : Time → ℚ` in the Agda original.

### A2 — the phase-sensitive critical-production ceiling

*Source lineage.*  R406 (fixed-output live global flux), R102 (helical critical
exchange production `P = 2 r_k (r_q − r_p) A`), R105 Waleffe lane, R353/R372
(`uniformCriticalCeiling`), R104 (critical frontier consumer).  The Lean cell
payments are the preserved donor theorems
`ClayNS.Waleffe.phase_damping_payment`, `kato_integrated_payment`,
`cell_integrated_production_payment`, `finite_production_payment`
(`Provenance/ns-latest-20260912/payload/RequestProject/NavierStokes/WaleffeIntegratedPayment.lean`),
reused unchanged — the consumer factors through them, so they were not redone.

*Endpoint proved* (`a2_uniform_critical_ceiling`).  For a cutoff-indexed finite
family of adverse cells whose amplitudes solve `Ȧ = −γA + F` and whose
production obeys the phase-sensitive comparison `ν P ≤ 2γ A₊`,

```
criticalSize N T = ∑_i ∫₀ᵀ P_{N,i} ≤ (2 M₀ + 2 M₁(T)) / ν
```

whenever `∑_i (A_{N,i}(0))₊ ≤ M₀` and `∑_i ∫₀ᵀ (F_{N,i})₊ ≤ M₁(T)` uniformly in
the cutoff.

*Independence.*  `NSUnforced/A2CriticalCeiling.lean` imports only `Mathlib` and
the donor Waleffe module.  No A1 module is in its import closure, so A1 cannot
leak into A2 or vice versa.  `critical_cell_pointwise_payment` records that the
pointwise comparison is a *geometric* consequence of `k + p + q = 0`, not a
dynamical assumption.

### Consumer composition — R414

`dualPayment_of_receipts` builds the Lean form of
`DualSignedCancellationPayment` from an A1 receipt and an A2 receipt, reading
`signedRemainderIntegral G N T = 4 ∫₀ᵀ G N t`.  Both arguments are used.

The Agda Boolean `round414DoesNotAssumePackageAImpliesCriticalBarrier = true`
is replaced by two theorems: `a1_does_not_pay_a2` and `a2_does_not_pay_a1`
exhibit data for which one record exists and the other provably cannot.  So at
this interface neither payment can silently discharge the other.

No instance of `DualSignedCancellationPayment` is constructed in this library:
composition is available, but unpaid.

---

## 3. Dependency map (Lean)

```
Mathlib
  ├── NSUnforced.SignedFullSquare            (R543/R566/R567, signed Gram collapse)
  ├── NSUnforced.HelicalMultiplierDifference (R571 carrier, gain + obstruction)
  ├── NSUnforced.ChannelSchur                (Schur test; imports SignedFullSquare)
  ├── NSUnforced.CutoffUniformBudget         (Grönwall + absorption engine)
  └── RequestProject.NavierStokes.WaleffeIntegratedPayment   [donor, unchanged]

NSUnforced.A1Budget568      ← SignedFullSquare, CutoffUniformBudget
NSUnforced.Frontier         ← A1Budget568
NSUnforced.A2CriticalCeiling← Mathlib, WaleffeIntegratedPayment      (no A1 edge)
NSUnforced.DualConsumer414  ← A1Budget568, A2CriticalCeiling
NSUnforced                  ← all of the above
NSUnforced.AxiomAudit       ← NSUnforced
```

Build: `lake build NSUnforced` and `lake build NSUnforced.AxiomAudit`.

---

## 4. Exact remaining obligations

### A1 (`A1ChannelObligation`, `Lean/NSUnforced/Frontier.lean`)

```
∃ (χ : Type) (C : ℕ → ℝ → Finset χ) (A B : ℕ → ℝ → χ → ℝ) (cA cB θ : ℝ),
  0 < θ ∧ 0 ≤ cA ∧ 0 ≤ cB ∧ 2θ·cA < 2ν ∧
  (∀ N t, globalForcingFull N t ≤ ∑_{c∈C N t} A N t c · B N t c) ∧
  (∀ N t, ∑_{c∈C N t} (A N t c)² ≤ cA · Dissip N t) ∧
  (∀ N t, ∑_{c∈C N t} (B N t c)² ≤ cB · Energy N t)
```

`a1_of_channelObligation` proves this suffices (given the balance, sign and
initial-energy hypotheses).  Nothing in the library proves it.

### A2

The cutoff-uniform positive network-forcing expenditure `M₁(T)`, i.e. the donor
`ClayNS.Waleffe.PhysicalWeightedPositiveWaleffeNetworkForcingBudget`.  Not paid
here.

---

## 5. Ranked remaining seams

1. **Heterochiral rows of the commutator square.**  Now a proved obstruction,
   not a suspicion (`heterochiral_multiplierDifference_not_output_controlled`).
   The next concrete step is a Lean statement of the R577 four-sign inner-fibre
   Gram receipt for the two heterochiral sign pairs, and a proof that the
   heterochiral contribution to `∑_c (A c)²` is controlled by the dissipation
   with a constant independent of the shell separation.  Until that exists the
   `∑ A² ≤ cA · D` clause of `A1ChannelObligation` is out of reach.

2. **Gram factorisation of the symmetric pair resolvent.**  The collapse
   theorem is stated for `ρ a b = ∑_j r j a · r j b`.  The literal
   `R566.Swap.pairResolvent` is symmetric, and R503/R572 manipulate it as such,
   but a Lean-checked finite Gram factorisation with a *bounded* channel count
   has not been produced.  Without it, `fullSquareSum_gram_collapse` applies
   only to the separable/rank-one part of the resolvent.

3. **Cell control constant `cA` (R574).**  Partly reduced this session:
   `sum_commutator_square_homochiral_le` shows the homochiral part of
   `∑ ‖A c‖²` is dominated by `∑ ‖k‖²‖w‖²`, i.e. by output-wavenumber-weighted
   cross products — the correct dissipation-facing shape.  What is missing is
   the identification of `∑ ‖k‖²‖w‖²` with `cA · D` for a *small* `cA`.
   `pointwise_absorption_of_channel_squares` makes the requirement explicit:
   sub-criticality needs `θ < ν / cA`, so `cA` must be finite and
   cutoff-uniform.  R574's primitive component low-output bound is the natural
   donor; it has no Lean carrier yet.

4. **Energy-side receipt `∑ B² ≤ cB · E`.**  Reduced this session to a purely
   combinatorial question by `channel_energy_receipt`: with row/column bounds
   `R_row`, `R_col` on the Gram weight matrix, `c_B = R_row R_col` works, given
   the Parseval-type inequality `∑_b ‖cell b‖² ≤ Energy`.  What remains is to
   exhibit those two bounds for the literal `R566.Swap.pairResolvent` weights
   and to mirror the Parseval bookkeeping the Agda lane owns.

5. **A2's `M₁`.**  Independent of 1–4; the donor file states it as an explicit
   `Prop` and proves what it buys, so the seam is isolated.

6. **Transport B.**  Untouched this session; it remains independent, since no
   typed transport was proved.

---

## 6. Honest scope statement

Nothing here proves global regularity, a spacetime budget for the true
Navier–Stokes commutator square, or any Clay-level statement.  What is proved
is: the signed carrier algebra is exact over `ℝ`; the homochiral multiplier
gain is real and the heterochiral one provably is not; a pointwise absorption
receipt with cutoff-uniform constants does imply the R568 endpoint with an
explicit cutoff-free bound; the analogous statement holds for the A2 ceiling;
and the two payments are formally independent at the R414 interface.  No Agda
kernel receipt was obtained or claimed in this session.
