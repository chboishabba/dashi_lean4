# Yang–Mills Clay lane — handoff

## 0. Headline

**No Clay closure is claimed, and no Lean receipt for the Clay endpoint exists in this
tree.** What is delivered is five new machine-checked Lean modules that close the
generic operator-theoretic legs of the physical chain around a new shared carrier,
plus a precise obstruction report naming the first blocking obligation.

Full write-up: [`docs/ym/clay_final_tranche_round.md`](docs/ym/clay_final_tranche_round.md).
Round entry prepended to [`status.md`](status.md).

## 1. Incoming tranche: verification

| item | value |
|---|---|
| archive | `ym-clay-final-proof-tranche-20260916.tar.gz` |
| SHA-256 | `dcd7a4b24ab445e1c6c25787383201bdb377ba35e8d335534faa4ae6166a5bb7` |
| embedded `SHA256SUMS` | **3557 / 3557 files OK** |
| embedded `SOURCE_MANIFEST.txt` | 3557 entries, consistent with `SHA256SUMS` |

Provenance recorded in the tranche's own `HANDOFF.md` and reproduced here:

* Agda master: `chboishabba/dashi_agda` `origin/master` @ `20ddc053cc7d98be40cb60c9dafcdccf43bca695`
* Lean main: `chboishabba/dashi_lean4` `origin/main` @ `e6e62d6be20ffadbd92a6e5026bf063b742ed07b`
* Overlays (donors, not master):
  `agent/ym-rh-unification-pareto-v2` @ `0f913fd1a34d2e707428d47edc12b9f831e76d13`,
  `agent/ym-rh-pareto-form-flow-v1` @ `390cd1c8fecbea2b1856258c03b22ef0a426c3cb`,
  `agent/ym-literal-cmp116-trajectory-r345` @ `55448979b7fc614f1ab34d7c3f09c78501d340c0`,
  `agent/ym-rh-pareto-global-board` @ `d8813edd5f04cd0779e92ee8c09b276802bfda01`

The tranche's `RequestProject/YangMills/` selection (156 files) is byte-identical to
this repository's Yang–Mills Lean lane, so that payload was already imported; the new
material in the tranche is `lean-main/` (481 Lean files across `Spine`, `Integration`,
`AgdaMirror`, `Promoted`, `Synthesis`, `Cuisine`), `agda-master/`, `agda-pr-overlays/`
and `docs/`.

**Donor triage.** `lean-main/YangMillsContinuumGap.lean` is a record/Boolean compiler:
`Type`-valued opaque fields and a `clayYangMillsPromoted : Bool` that is, per its own
docstring, intentionally `false`. Under the stated proof boundary it cannot pay a
physical theorem and was not used. `lean-main/YangMillsClosure.lean` contains four
genuine real-analysis theorems (Kotecký–Preiss geometric bound, absorption, monotone
RG induction, discrete Grönwall), but none mentions a Hilbert space, operator or
spectrum, so none can be welded to a spectral endpoint without the operator layer this
round supplies.

## 2. What is new in this repository

All in `RequestProject/YangMills/`:

| file | content |
|---|---|
| `VacuumSectorSpectralGap.lean` | the shared carrier `VacuumGapDatum`; reducing vacuum sector; `H ≥ 0`; no eigenvalue below the gap; **unique solvability and resolvent bound on the vacuum complement for every real `lam < Δ`**; the `projHam` witness family |
| `CommutingProjectionGap.lean` | `Σᵢ (1 − Pᵢ) ≥ 1 − ∏ᵢ Pᵢ` for commuting orthogonal projections; the local Hamiltonian, its self-adjointness, and gap `1` above the joint-invariant vacuum; a `VacuumGapDatum` from it |
| `CoreToDomainGap.lean` | the vacuum gap survives operator closure; `closureDatum` from essential self-adjointness; the resulting spectral statement |
| `ContinuumGapTransport.lean` | gap transport along vacuum-sector graph limits, with fixed or drifting constants; `continuumDatum`; **no spectral pollution in the continuum limit**; a non-constant drifting witness |
| `SameObjectGapTransfer.lean` | transfer of the whole carrier along an operator equality; the same-evolution-on-a-common-core weld; the assembled chain statement |

New documentation: `docs/ym/clay_final_tranche_round.md`.

### The mismatch that motivated the round

The pre-existing machinery (`UnboundedFormGapResolvent`, `FormGapSpectralExclusion`)
required `Δ‖ψ‖² ≤ re⟪ψ, Hψ⟫` on the **whole** domain. With a vacuum `Ω` satisfying
`HΩ = 0`, that forces `Δ ≤ 0`, so it was inapplicable to any physical Hamiltonian.
`VacuumGapDatum` imposes the bound only on `D(H) ∩ Ω^⊥` and still delivers the full
resolvent statement.

## 3. Verification performed here

```
lake build RequestProject
# Build completed successfully (8188 jobs) — 0 errors, 0 warnings

rg -n 'sorry|admit|^axiom|implemented_by|unsafe' RequestProject/YangMills
# no hits
```

`#print axioms` is attached to every headline theorem of the five new modules and
reports exactly `[propext, Classical.choice, Quot.sound]`.

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (see `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`).

## 4. Proof boundary held

* No new `axiom`, `postulate`, `@[implemented_by]`, `sorry` or `unsafe`.
* No Boolean/record placeholder, source receipt, provenance field, external theorem or
  similarly named scalar was used to discharge a physical obligation.
* The only bridge used between two Hamiltonians is a genuine equality of unbounded
  operators *including domains*, produced by
  `UnboundedHamiltonianDomain.pmap_generator_unique_of_hasCore`.
* Finite-lattice results are filed as the first link only; they are not offered as
  payment for any continuum claim.
* Every unpaid physical input is displayed as a Lean hypothesis, and every hypothesis
  package is inhabited by an explicit witness so that no statement is vacuous.

## 5. Obstruction: the first blocking obligation

> **M7a — there is no four-dimensional continuum Yang–Mills Hilbert space,
> Hamiltonian or domain anywhere in this corpus.**

Nothing in the Agda master, the four overlays, `lean-main`, or the Yang–Mills Lean
lane constructs a Hilbert space carrying a continuum `SU(N)` gauge theory on `ℝ⁴`, the
action variation as an operator on it with a domain and dense invariant core, or a
cutoff family of such operators. Consequently:

* **M7c** (essential self-adjointness) cannot even be stated;
* **M9** (uniform-in-spacing gap) is blocked because the Bałaban/KP estimates in the
  corpus are statements about real sequences and kernels, not about quadratic forms of
  an operator, and the transfer-matrix identification that would convert them has no
  carrier here;
* **M8** (`U^YM = U^OS`) needs both evolutions, hence M7a;
* **C** (continuum limit, OS/Wightman, non-triviality, Clay equivalence) needs all of
  the above.

The separate source-transcription obstruction (literal CMP 109 Eq. (5.1)/(5.42) jet;
CMP 116 differentiated activity/entropy constants) is *not* the first blocker: even
fully transcribed, those are inequalities between real numbers and M7a still stands
between them and any spectral conclusion.

## 6. Suggested next step

A finite-volume, finite-spacing lattice `SU(N)` gauge Hilbert space
`L²(SU(N)^{links})` with its gauge-invariant subspace, and the Kogut–Susskind
Hamiltonian, whose strong-coupling electric term is a sum of commuting link
averagings. At that point `CommutingProjectionGap.localGapDatum` applies verbatim and
yields a genuine lattice `VacuumGapDatum`, discharging weld 1 of §3 of the round
write-up for a real gauge theory. Uniformity in the spacing (M9) would remain the wall.

## 7. Manifest and checksums

`SOURCE_MANIFEST.txt` lists, and `SHA256SUMS` checksums, the Yang–Mills Lean lane
(`RequestProject/`), the Yang–Mills documentation (`docs/ym/`), this handoff, the build
configuration and the toolchain pin. Verify with:

```
sha256sum -c SHA256SUMS
```
