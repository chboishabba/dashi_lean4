# NS proof-search tranche 2026-09-15 — intake, reconciliation, and lane-B results

Status: active worker record.  Non-promoting.  Nothing here claims a Clay
closure, and nothing here promotes a statement from provenance, a Boolean
ledger, a conditional compiler surface or a similarly named theorem.

---

## 1.  Verification before import

`ns-proof-search-tranche-20260915-master-aa5f-toe-759.tar.gz`

| check | result |
|---|---|
| archive sha256 | `d2bfe3119258f90eac6b4c9feaadce47d28cfbab488e1ae2a4de275047b91d28` |
| extraction | complete, no truncation |
| payload files | **10,457** regular files |
| `SOURCE_MANIFEST.txt` lines | 10,457 (matches) |
| `SHA256SUMS` | `sha256sum -c` → **10,457 OK, 0 mismatched, 0 missing** |

`HANDOFF.md` declares `dashi_agda` master `aa5f5e041cbbbc8f880ff503ff0428c20c660c41`
(PR range `57b6f07c7..aa5f5e041`, #929–#935), `dashi_lean4` main
`63fa6af1d45680e9d618e9e2c59d49ed5873ce56`, and TOE task
`759f2a06-f7cf-415a-bc5e-cc15ccb72acc`.  Those identifiers are recorded as
declared; this worker verified the *payload*, not the upstream repositories.

## 2.  Indexing and import

Full hash-level index: `TRANCHE_INDEX.csv` (donor, path, sha256, size, status,
matching project path).  Per-file disposition: `IMPORT_LOG.csv`.

| donor | identical | divergent | new |
|---|---|---|---|
| `dashi_agda` | 8,162 | 286 | 1,250 |
| `dashi_lean4` | 204 | 8 | 547 |

Import policy, applied uniformly and recorded per file:

* **new Agda** → imported at its donor path (1,198 `.agda` plus scripts,
  workflows and docs).  Nothing pre-existing was overwritten.
* **new Lean, TOE `NSUnforced`** → `Lean/NSUnforced/` (live; see §3).
* **new Lean, other `ImportedLeans/`** → `Provenance/tranche-20260915/dashi_lean4/`
  (this includes this project's own earlier output returned as provenance).
* **new Lean, otherwise** → `Lean/` (`AgdaMirror`, `Integration`, `Spine`,
  `Promoted`, `Welds`, `Cuisine`, `Synthesis` surfaces).
* **divergent (294 files)** → donor copy preserved verbatim under
  `Provenance/tranche-20260915/donor-version/`; the project version is kept.

Nothing was discarded, including cross-lane and non-NS material (Yang–Mills,
Riemann, biology, chemistry, culture).

**Safety scan of the 1,198 imported Agda modules:** 0 `postulate`, 0
`TERMINATING`/`NON_TERMINATING` pragmas, 0 `trustMe`.  No Agda kernel exists in
this environment and **no Agda kernel receipt is claimed** — the Agda side of
this report is a source, provenance and dependency review only.

## 3.  Independent Lean receipts (run here, not taken on report)

The TOE `NSUnforced` library was put on the build surface (`lakefile.toml`,
library `NSUnforced`, `srcDir = "Lean"`) and built in this environment:

```
lake build NSUnforced NSUnforced.AxiomAudit      → 8,037 jobs, no errors, no warnings
```

All 28 audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`.  So the TOE report's receipts
reproduce here.  Its `A2CriticalCeiling` module consumes this project's own
`RequestProject.NavierStokes.WaleffeIntegratedPayment`, which now compiles as a
cross-library dependency; the import edge is real, not nominal.

Whole project: `lake build` → **8,207 jobs, no errors, no warnings**.
New-material audit module: `RequestProject.NavierStokes.TrancheAxiomAudit20260915`.
No `sorry`, no `axiom`, no `@[implemented_by]` anywhere in `RequestProject/` or
`Lean/NSUnforced/`.

## 4.  Foreign-label reconciliation: the two different `A1`/`A2`

This is the reconciliation the handoff requires, and it is a real collision, not
a naming quibble.  **Nothing was relabelled; both label sets are preserved.**

| label | corpus | what it actually is | type |
|---|---|---|---|
| `A1` | **B carrier** (`NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact.transportGradient`) | radial *transport-gradient* envelope: `\|L\| ≤ \|y\| A1` | a nonnegative rational/real **constant** |
| `A2` | **B carrier** (`…EnvelopeSplitExact.transportCurvature`) | radial *Taylor-curvature* envelope: `\|R±\| ≤ \|y\|² A2` | a nonnegative **constant** |
| `G2` | B carrier (`…derivativeCurvature`) | state-side: `\|g₊-g₋\| ≤ \|y\| G2` | a **constant** |
| `G1` | B carrier (`…derivativeEnvelope`) | state-side: `\|g±\| ≤ G1` | a **constant** |
| `A1` | **TOE source-local** (`NS_UNFORCED_A_PROGRAMME.md`, `NSUnforced.Frontier`) | the whole commutator-only spacetime-budget route ending at `CommutatorOnlySpacetimeBudget568` | a **`Prop`** (`A1ChannelObligation → …`) |
| `A2` | **TOE source-local** (`NSUnforced.A2CriticalCeiling`) | the phase-sensitive uniform critical-production ceiling | a **`Prop`** |

The two `A1`s and the two `A2`s are of different kinds (a constant versus a
proposition) and sit at different places in the route.  **No endpoint claimed on
one may be read as the other.**  Concretely: paying the B-carrier `A1`/`A2`
leaves (§5) does *not* pay TOE `A1`, and TOE's `a1_does_not_pay_a2` /
`a2_does_not_pay_a1` are statements about the TOE pair only.

Lane discipline is unchanged and was not crossed anywhere in this session:
`A` = unforced `R³` (untouched), `B` = unforced `T³` (all new work below),
`C`/`D` = forced breakdown (not used, not cited as evidence).  TOE calls its
library an "A programme"; on the canonical four-lane terminology its R571/R568
provenance is **B-carrier** material, and it is used here only as B material.

## 5.  New lane-B results (all proved, all built here)

### 5.1 The two radial Gate-A leaves are paid

`RequestProject/NavierStokes/R571RadialCurvature.lean`

`NSTriadKNR571RadialCurvatureBoundaryExact` records that with the preferred
Taylor model the `+` remainder is exactly zero, so the whole `A2` leaf collapses
to one centred second-difference bound for `m_σ(k) = σ‖k‖`, and states
explicitly that no uniform `|y|² A2` estimate is claimed there.  That estimate
is now proved:

```
0 ≤ ‖k+y‖ - 2‖k‖ + ‖k-y‖ ≤ ‖y‖²/‖k‖          (norm_second_difference_nonneg/_le)
```

Consequences on the B carrier:

* `abs_radialIncrement_le` — **`A1 = 1`**, cutoff-uniform;
* `abs_centeredRadialDefect_le` — **`A2 = 1/‖k‖`**;
* `abs_centeredRadialDefect_le_of_one_le_norm` — on the periodic lattice every
  nonzero centre mode has `‖k‖ ≥ 1`, so **`A2 = 1`, with no dependence on the
  Galerkin cutoff**.

Sharpness: `centeredRadialDefect_bound_is_order_sharp` exhibits a
displacement orthogonal to the centre mode where the defect is `2√2 - 2 ≥ 4/5`
against a bound of `1`, so the quadratic envelope is the true order.

### 5.2 The paired second moment, with the radial half discharged

`RequestProject/NavierStokes/R571PairedSecondMoment.lean`

The Agda paired-commutator identity and second-moment budget are rational-
arithmetic carriers; they are re-proved over `ℝ` here so a real analytic
estimate can consume them (`paired_commutator_identity`,
`finite_weighted_paired_commutator_identity`, `paired_second_moment_pointwise`).
Then:

```
r571_pairedSecondMoment_of_stateEnvelope
r571_finite_pairedSecondMoment_of_stateEnvelope
```

pay the whole cell / whole family second-moment bound with coefficient `G2 + G1`
— `A1` and `A2` are *proved*, not hypothesised.  `StateDerivativeEnvelope` is the
named residual: `|g±| ≤ G1` and `|g₊-g₋| ≤ ‖y‖ G2`.

**Open payment:** `G1`, `G2`.  These are analytic bounds on the transported
high-frequency field, not geometry, and nothing here supplies them.

### 5.3 The heterochiral obstruction is answered

`RequestProject/NavierStokes/HeterochiralOutputGain.lean`

TOE's first ranked seam is
`heterochiral_multiplierDifference_not_output_controlled`: the heterochiral
multiplier `‖p‖+‖q‖` is unbounded relative to `‖k‖`.  That is about the scalar
alone.  Including the helical vertex:

1. `heterochiral_radialSum_mul_defect_le` —
   `(‖p‖+‖q‖)·‖p̂+q̂‖ ≤ 4‖k‖` on any triad with `p,q ≠ 0`;
2. `cross_helical_antiparallel_eq_zero` — the heterochiral vertex vanishes
   *exactly* at antiparallelism, proved frame-free from the curl eigen-relation
   `i(n × h) = s h` (no helical frame is ever chosen);
3. `nrm_cross_helical_le` — `‖h_p × h_q‖ ≤ (3/2)‖n+m‖`;
4. `heterochiral_vertex_output_controlled` —
   **`(‖p‖+‖q‖)·‖h_p × h_q‖ ≤ 6‖k‖`**;
5. `sum_heterochiral_square_le` — summed over a family,
   `∑ ((‖p‖+‖q‖)‖h_p × h_q‖)² ≤ 36 ∑ ‖k‖²`, the counterpart of
   `NSUnforced.sum_commutator_square_homochiral_le`, which explicitly excludes
   the heterochiral rows.

Consequence, stated exactly: the heterochiral row buys the **same one power of
output gain** as the homochiral row, so the R577 sign split is *not* forced at
this point of the A1 route.  Non-vacuity: `exists_unit_helical_vector`.

**Open payment (unchanged):** identifying `∑ ‖k‖²‖w‖²` with `c_A · Dissip` for a
small cutoff-uniform `c_A` (the TOE seam 3, the Agda R574 donor), and the
energy-side `∑ B² ≤ c_B · Energy` clause (TOE seam 4) for the literal
`R566.Swap.pairResolvent` weights.  Neither is touched here.

### 5.4 Lean mirror of the canonical proof-debt router

`RequestProject/NavierStokes/ProofDebtRouterMirror.lean` reproduces
`DASHI.Core.ProofDebtRouterExact` constructor for constructor and clause for
clause, re-checks in Lean every routing fact the Agda owner asserts by `refl`,
and is explicitly **not** a second router: no routing decision is added or
altered.  One thing is upgraded: the Agda owner's firewall comment

> There is intentionally no function `SourceAlignedDeferredTheorem T -> T`

becomes the theorem `no_receipt_to_theorem`, proved by manufacturing a fully
aligned receipt for `False`.  Provenance, alignment and authority provably
cannot pay a mathematical obligation.

## 6.  Exact source → carrier → consumer lineage

| Agda owner (source) | Lean carrier (here) | consumer | status |
|---|---|---|---|
| `NSTriadKNR571RadialCurvatureBoundaryExact` (`A2` leaf, no estimate claimed) | `R571.abs_centeredRadialDefect_le`, `…_of_one_le_norm` | `R571.r571_pairedSecondMoment_of_stateEnvelope` | **paid**, `A2 = 1` cutoff-uniform |
| `…RadialCurvatureBoundaryExact` (`A1` leaf) | `R571.abs_radialIncrement_le` | same | **paid**, `A1 = 1` |
| `NSTriadKNLuoCenteredPairedCommutatorIdentityExact` (ℚ) | `R571.paired_commutator_identity` (ℝ) | second-moment budget | mirrored exactly |
| `NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact` (ℚ) | `R571.paired_second_moment_pointwise` (ℝ) | `…_finite_…` | mirrored exactly |
| `…EnvelopeSplitExact` state leaves `G1`,`G2` | `R571.StateDerivativeEnvelope` | same | **open payment** |
| `R311`/`R571` signed radius, via TOE `HelicitySign` | `R571.radialSymbol` | all of §5.1–5.2 | reused verbatim |
| TOE `heterochiral_multiplierDifference_not_output_controlled` | `Heterochiral.heterochiral_vertex_output_controlled` | `Heterochiral.sum_heterochiral_square_le` → `A1ChannelObligation` clause `∑A² ≤ cA·D` | obstruction **answered**; clause still open |
| R145 `ℂ³` carrier (`ClayNS.Waleffe.cross`, `ClayNS.SlotKernel.bdot`) | reused unchanged | §5.3 | reused |
| `DASHI.Core.ProofDebtRouterExact` | `ProofDebtRouter.*` | crosswalk only | mirrored; firewall upgraded to a theorem |
| TOE `NSUnforced` (9 modules) | `Lean/NSUnforced/` on the build surface | built + audited here | independent receipt obtained |

## 7.  Open payments, stated plainly

1. **`G1`, `G2`** — the state-side Gate-A leaves (B carrier).  Analytic bounds on
   the transported high-frequency field.  Not paid.
2. **`c_A`** — identification of the output-weighted cross-product square with
   `c_A · Dissip`, `c_A` small and cutoff-uniform (Agda R574 donor).  Not paid.
3. **`c_B`** — the energy clause `∑ B² ≤ c_B · Energy` for the literal symmetric
   pair resolvent; TOE reduced it to row/column bounds
   (`channel_energy_receipt`) but those bounds are not exhibited.  Not paid.
4. **Gram factorisation of the symmetric pair resolvent with a bounded channel
   count** (TOE seam 2).  Not paid.
5. **A2's `M₁`** (TOE label): the cutoff-uniform positive network-forcing
   expenditure.  Not paid.
6. **Lane A, and any B→A transport.**  Untouched.  No transport theorem exists.
7. **R568, `A1ChannelObligation`, periodic regularity.**  Open.

## 8.  What is *not* claimed

No Clay closure.  No global regularity, on either lane.  No Agda kernel receipt.
No promotion from a Boolean ledger, an authority record, a finite-carrier
experiment or a similarly named theorem.  The historical R181/R207/Gram route
remains a documented alternative/no-go and was not used as a positive-
majorisation replacement; the signed cancellation of the R571 route is preserved
exactly (`paired_commutator_identity` is an identity, and
`cross_helical_antiparallel_eq_zero` is an exact vanishing) before any
majorisation is applied.
