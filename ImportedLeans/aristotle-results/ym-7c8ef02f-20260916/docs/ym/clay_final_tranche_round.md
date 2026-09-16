# Yang–Mills Clay final tranche: the vacuum-sector round

**Status up front. No Clay closure is claimed, and no Lean receipt for the Clay
endpoint exists in this tree.** What this round delivers is five new machine-checked
Lean modules that close the *generic* operator-theoretic legs of the physical chain
around a genuinely new shared carrier, and a precise statement (§6) of the first
obligation that actually blocks the endpoint.

Everything below compiles under `lake build RequestProject` (8188 jobs, zero errors,
zero warnings). There is no `sorry`, `axiom`, `@[implemented_by]` or `unsafe` in any
new file, and every headline theorem is followed by `#print axioms`, all reporting
only `propext`, `Classical.choice`, `Quot.sound`.

## 0. Provenance of the imported tranche

Archive `ym-clay-final-proof-tranche-20260916.tar.gz`,
SHA-256 `dcd7a4b24ab445e1c6c25787383201bdb377ba35e8d335534faa4ae6166a5bb7`.
Its embedded `SHA256SUMS` was verified: **3557/3557 files OK**. The payload contains

* `RequestProject/YangMills/` (156 files) — byte-identical to the working tree's
  Yang–Mills lane, i.e. the tranche's Lean Yang–Mills selection was already imported;
* `lean-main/` — the canonical Lean snapshot
  (`chboishabba/dashi_lean4` `origin/main` @ `e6e62d6be20ffadbd92a6e5026bf063b742ed07b`),
  481 Lean files across `Spine`, `Integration`, `AgdaMirror`, `Promoted`, `Synthesis`,
  `Cuisine`, plus `YangMillsClosure.lean` and `YangMillsContinuumGap.lean`;
* `agda-master/` — `chboishabba/dashi_agda` `origin/master` @ `20ddc053cc7d98be40cb60c9dafcdccf43bca695`;
* `agda-pr-overlays/` — the four unmerged donor branches
  (`agent/ym-rh-unification-pareto-v2` @ `0f913fd1`,
   `agent/ym-rh-pareto-form-flow-v1` @ `390cd1c8`,
   `agent/ym-literal-cmp116-trajectory-r345` @ `55448979`,
   `agent/ym-rh-pareto-global-board` @ `d8813edd`).

### What the donor endpoint files actually contain

`lean-main/YangMillsContinuumGap.lean` is a **record/placeholder compiler**: its
`ContinuumLimitMassGap`, `OSWightmanReconstruction` and
`Nontrivial4DSU3YangMillsMeasure` carry `Type`-valued opaque fields, and its
`clayYangMillsPromoted : Bool` is, by its own docstring, *intentionally `false`*.
It is honest about this. Under the stated proof boundary it cannot pay any physical
theorem, and it is **not** used as a donor for anything below.

`lean-main/YangMillsClosure.lean` (`ym1_local_kp_sum_below_one`,
`ym2_strict_absorption`, `ym3_uniform_volume_kp`, `ym4_balaban_rg_gronwall`) contains
real analysis — a geometric Kotecký–Preiss bound, a grouping estimate, a monotone
induction and a discrete Grönwall inequality. These are genuine theorems about real
sequences; none of them mentions a Hilbert space, a Hamiltonian or a spectrum, so
none of them can be welded to the spectral endpoint without the operator layer that
this round builds.

## 1. The mismatch this round fixes

The Lean lane already had `UnboundedFormGapResolvent`: for a self-adjoint unbounded
`H` with `Δ‖ψ‖² ≤ re⟪ψ, Hψ⟫` **on the whole domain**, every real `lam < Δ` is in the
resolvent set. Likewise `FormGapSpectralExclusion` in the bounded case.

That hypothesis is **never satisfiable by a physical Hamiltonian with `Δ > 0`**. A
physical Hamiltonian has a vacuum `Ω` with `HΩ = 0`; putting `ψ = Ω` in the
whole-domain bound forces `Δ ≤ 0`. So the previously available spectral machinery,
although correct, could not be applied to any Yang–Mills Hamiltonian. The mass gap is
a statement about `Ω^⊥`, and that version was missing.

## 2. The shared carrier

`RequestProject/YangMills/VacuumSectorSpectralGap.lean` introduces

```
structure VacuumGapDatum (E) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  op   : E →ₗ.[ℂ] E      -- the Hamiltonian, densely defined and unbounded
  vac  : E               -- the vacuum
  gap  : ℝ
  vac_mem, vac_unit, vac_ground   -- Ω ∈ D(H), ‖Ω‖ = 1, HΩ = 0
  selfAdjoint                     -- H† = H
  gap_pos                         -- Δ > 0
  form_gap : HasVacuumFormGap op vac gap   -- Δ‖ψ‖² ≤ re⟪ψ,Hψ⟫ for ψ ∈ D(H), ψ ⊥ Ω
```

Proved about it:

| theorem | content |
|---|---|
| `vacuumComplement_invariant` | `⟪Ω, Hψ⟫ = 0` for every `ψ ∈ D(H)`: the vacuum sector is reducing |
| `domain_decomposition`, `op_eq_op_vacuumPart` | `D(H) = ℂΩ ⊕ (D(H) ∩ Ω^⊥)` and `H` ignores the vacuum component |
| `hasFormLowerBound_zero` | `H ≥ 0` on all of `D(H)` |
| `eigenvalue_eq_zero_of_lt_gap` | an eigenvalue `< Δ` is forced to be `0`: **no excited state below the gap** |
| `isClosed_sectorRange` | closedness of the range of `H − lam` restricted to the vacuum sector |
| `exists_unique_solution_vacuumSector` | **for real `lam < Δ` and `y ⊥ Ω`, a unique `ψ ∈ D(H) ∩ Ω^⊥` with `Hψ − lam ψ = y`** |
| `resolvent_bound_vacuumSector` | `‖ψ‖ ≤ (Δ − lam)⁻¹‖y‖` |

The proof of solvability does not restrict the operator to a subspace Hilbert space.
It shows instead that a vector orthogonal to both `Ω` and the sector range is
orthogonal to `(H − lam)ψ` for *every* `ψ ∈ D(H)` — using the splitting of `D(H)`
above — and then invokes the existing `mem_domain_of_orthogonal_range`, which turns
it into an eigenvector below the gap, hence `0`.

`projHam`, `projectionWitness` and `projectionWitness_gap` inhabit the carrier in
every Hilbert space with a unit vector, at any prescribed positive gap.

## 3. The four legs, as active consumers

| module | leg | main theorem |
|---|---|---|
| `CommutingProjectionGap.lean` | finite lattice construction | `hasVacuumFormGap_localHamiltonian`, `localGapDatum` |
| `CoreToDomainGap.lean` | core → domain → self-adjointness | `hasVacuumFormGap_closure`, `closureDatum`, `core_to_domain_no_spectrum_below_gap` |
| `ContinuumGapTransport.lean` | cutoff → continuum, no spectral pollution | `hasVacuumFormGap_of_graphLimit(_tendsto)`, `continuum_no_spectrum_below_gap` |
| `SameObjectGapTransfer.lean` | OS / Yang–Mills same-object weld | `vacuumGapDatum_of_same_evolution`, `chain_no_spectrum_below_gap` |

Each consumes existing project results rather than duplicating them:

* `CoreToDomainGap` consumes `UnboundedHamiltonianDomain.exists_seq_of_mem_closure_domain`
  and `IsSymmetric.isClosable`, and routes the estimate through
  `ContinuumGapTransport.formGap_le_of_graphLimit`.
* `ContinuumGapTransport` feeds `VacuumSectorSpectralGap`'s resolvent theorem.
* `SameObjectGapTransfer` consumes `UnboundedHamiltonianDomain.pmap_generator_unique_of_hasCore`
  — the only admissible bridge — and `ContinuumGapTransport.continuumDatum`.
* `CommutingProjectionGap` produces a `VacuumGapDatum` that any of the above can consume.

### The welds, with their exact hypotheses

1. **Finite → carrier.** `localGapDatum` needs: pairwise commuting orthogonal
   projections; `Pᵢ Ω = Ω`; and `∏ᵢ Pᵢ` annihilates `Ω^⊥` (joint invariants = `ℂΩ`).
   Gap `1`.
2. **Core → domain.** `closureDatum` needs: `H` densely defined and symmetric;
   `Ω ∈ D(H)`, `‖Ω‖ = 1`, `HΩ = 0`; gap `Δ` on `D(H) ∩ Ω^⊥`; **and `H.closure`
   self-adjoint** (essential self-adjointness — see §6, item M7c).
3. **Cutoff → continuum.** `continuumDatum` needs: uniform (or convergent) gaps;
   `IsVacuumGraphLimit H vacn Hinf vac`; `Hinf` self-adjoint with normalised zero mode.
4. **Same object.** `chain_no_spectrum_below_gap` needs: `U^YM = U^OS` as functions,
   and a submodule that is a **core for both** Hamiltonians, each differentiating its
   evolution there.

None of 1–4 is discharged for four-dimensional `SU(N)` Yang–Mills. Every one is
displayed as a Lean hypothesis, and each is inhabited by an explicit witness
(`localGapDatum_witness`, `closureDatum_witness`, `drift_continuum_no_spectrum_below_gap`,
`same_evolution_self`) so that none of the statements is vacuous.

## 4. What was deliberately *not* used

* `YangMillsContinuumGap.clayYangMillsPromoted` and its `Type`-valued record fields —
  a Boolean/record compiler, excluded by the proof boundary.
* Authority receipts, source-transcription constants and provenance metadata from the
  Agda overlays — none of them carries a same-object map into a Hilbert-space
  statement, so none can pay a spectral theorem.
* Finite-lattice evidence as payment for a continuum claim: `CommutingProjectionGap`
  is filed as the first link, explicitly *not* as a continuum result.

## 5. Verification

```
lake build RequestProject          # 8188 jobs, 0 errors, 0 warnings
rg -n 'sorry|admit|^axiom|implemented_by|unsafe' RequestProject/YangMills   # no hits
```

`#print axioms` on every headline theorem of the five new modules reports exactly
`[propext, Classical.choice, Quot.sound]`.

## 6. Obstruction report: the first blocking obligation

With §3 in place, the remaining distance to the Clay endpoint is *entirely* the
construction of the physical objects. Ordered by dependency, the first genuinely
blocking item is:

> **M7a — there is no four-dimensional continuum Yang–Mills Hilbert space,
> Hamiltonian or domain anywhere in this corpus.**

Concretely, nothing in the Agda master, the four overlays, `lean-main`, or the
Yang–Mills Lean lane constructs

* a Hilbert space carrying a continuum `SU(N)` gauge field theory on `ℝ⁴`
  (the closest objects are the finite gauge-invariant `L²` carrier of
  `GaugeInvariantL2Carrier`/`GaugeInvariantCarrierWitness`, which is a finite group
  witness, and the abstract projection carriers of this round);
* the Yang–Mills action variation as an operator on it, with a domain and a dense
  invariant core;
* a cutoff family of such operators indexed by lattice spacing.

Everything downstream is therefore unreachable, in this order:

* **M7c (essential self-adjointness).** Cannot be stated without M7a. `closureDatum`
  is waiting for exactly this hypothesis, and has nothing to be applied to.
* **M9 (uniform lattice gap).** The Bałaban/Kotecký–Preiss estimates present in the
  corpus (`YangMillsClosure`, `SmallFieldRGContraction`, `MarkedPolymerDecay`,
  `WeightedInfluenceRows`, the Row A/B/C files) are statements about **real number
  sequences and kernels**, not about quadratic forms of an operator on a Hilbert
  space. To feed `ContinuumGapTransport` they would have to be re-expressed as
  `HasVacuumFormGap (H a) (Ω a) Δ` for the lattice Hamiltonians `H a` of M7a, with
  `Δ` independent of the spacing `a`. That translation is not a bookkeeping step: it
  requires the transfer-matrix/reflection-positivity identification of the polymer
  decay rate with a spectral gap of the transfer operator, and that identification
  has no carrier here.
* **M8 (`U^YM = U^OS`).** Needs both evolutions, hence M7a plus an OS reconstruction
  on the same space.
* **C (continuum limit, OS/Wightman, non-triviality, Clay equivalence).** Needs all
  of the above.

There is also a separate, already-recorded source-transcription obstruction
(the literal CMP 109 Eq. (5.1)/(5.42) jet and the CMP 116 differentiated
activity/entropy constants are not recoverable from the scans in this tree). That one
is *not* the first blocker: even with those constants transcribed exactly, the
resulting statements are inequalities between real numbers, and M7a would still
stand between them and any spectral conclusion.

### What a next round could actually attempt

The smallest honest advance that would move the frontier is a **finite-volume,
finite-spacing lattice `SU(N)` gauge Hilbert space** with

1. `E = L²(SU(N)^{links})` with Haar measure, the gauge-invariant subspace as carrier;
2. the Kogut–Susskind Hamiltonian `H_a = (g²/2a) Σ_links E² + (1/2g²a) Σ_plaquettes (1 − Re tr U_p)`;
3. at strong coupling, the electric term recognised as the sum of commuting link
   averagings — at which point `CommutingProjectionGap.localGapDatum` applies
   verbatim and yields a genuine lattice `VacuumGapDatum`.

That would discharge weld 1 of §3 for a real gauge theory. It would still be a
finite-lattice result, and — per the standing boundary — could not pay the continuum
theorem; the uniformity in `a` (M9) would remain the wall.
