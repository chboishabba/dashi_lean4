# NS tranche `master-20dd / lean-7f60` — intake, audit and lane-B results

Status: active worker record.  Non-promoting.  No Clay closure, no regularity
theorem, and no Agda kernel receipt is claimed anywhere below.

---

## 1. Verification before import

`ns-proof-search-tranche-20260915-master-20dd-lean-7f60.tar.gz`

| check | result |
|---|---|
| archive sha256 | `64b36407434a947789901579091b4019d4eb2ff7cbaf01769d6973fb21374a21` |
| extraction | complete, no truncation |
| payload files | **10,400** regular files |
| `SOURCE_MANIFEST.txt` lines | 10,400 (matches) |
| `SHA256SUMS` | `sha256sum -c` → **10,400 OK, 0 mismatched, 0 missing** |

`HANDOFF.md` declares `dashi_agda` master `20ddc053cc7d98be40cb60c9dafcdccf43bca695`,
`dashi_lean4` main `7f60fa116f59a8f3f860fe53c13782ffc0d67ed6`, and two retained
source-archive digests.  Those identifiers are recorded **as declared**; this
worker verified the payload, not the upstream repositories.

## 2. Index and import — nothing discarded

Hash-level index: `TRANCHE_INDEX.csv`.  Per-file disposition: `IMPORT_LOG.csv`.
Importer: `scripts/import_tranche_20dd.py`.

| donor | identical | divergent | new |
|---|---|---|---|
| `dashi_agda` | 9,321 | 291 | 20 |
| `dashi_lean4` | 759 | 7 | 2 |

Policy (unchanged from the previous intake):

* `dashi_agda/<p>` → project `<p>`; new files imported at their donor path.
* `dashi_lean4/ImportedLeans/<p>` → compared against the existing provenance
  mirror *and* against the live project copy of any embedded
  `output-final_aristotle/` payload, so the live `Lean/NSUnforced` and
  `RequestProject/NavierStokes/*` copies are correctly recognised as identical
  rather than re-imported.
* divergent donor copies preserved verbatim under
  `Provenance/tranche-20260915-20dd/donor-version/`; the project version kept.

**All 291 divergent Agda files are byte-identical to the previously preserved
`aa5f` donor versions** — i.e. they are the pre-existing project/donor
divergence, not new upstream edits.  Exactly **7 files changed upstream**
between the two tranches:

```text
DASHI/Papers/NavierStokes/FourLaneProofProgramExact.agda
DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
DASHI/Physics/Closure/NSTriadKNR571GateAEnvelopeCrosswalkExact.agda
DASHI/Physics/Closure/NSTriadKNR571GateAEnvelopeCrosswalkRegression.agda
DASHI/Physics/Closure/NSTriadKNR571GateAEnvelopePublicationAggregate.agda
DASHI/Physics/Closure/NSTriadKNR571RadialCurvatureBoundaryExact.agda
Docs/roadmaps/NSProofControl20260915.md
```

The 20 new Agda modules are the S0/S1a/S1b/S2a control-cut owners, their
regressions, the positivity-free mode carrier, the four-lane coordinator
regression and six `R571` Gate-A owners.  The 2 new Lean files are the donor
`lakefile.toml` and `docs/provenance/NS_ARISTOTLE_B_RECEIPT_20260915.md`.
Cross-lane and non-NS material was kept, not dropped.

## 3. Safety scan, honestly reported

* The 20 newly imported Agda modules contain **0 `postulate`, 0
  `TERMINATING`/`NON_TERMINATING`, 0 `trustMe`**.
* The corpus as a whole is **not** postulate-free: 99 files contain a
  `postulate` block, 52 of them under `DASHI/Physics/Closure`, and 7 files carry
  `TERMINATING`/`trustMe` pragmas.
* Transitive import audit (`scripts/agda_dep_audit.py`, output in
  `AGDA_DEPENDENCY_AUDIT.txt`): the S0/S1a/S1b/S2a owners each have a
  `DASHI.*` closure of 121–347 modules with **zero unresolved imports** and
  **8–9 postulate-bearing modules in the closure**, including
  `DASHI.Foundations.RealAnalysisAxioms` (an explicit real-analysis axiom
  boundary) and the forced-tail / adversarial primitive-estimate surfaces.
  Import closure is not use; deciding use needs an Agda kernel, which does not
  exist in this environment.  `DASHI.Core.ProofDebtRouterExact` has a closure of
  2 modules and **no** postulates.

## 4. Lean receipts, run here

`lake build` over the project including the five new modules: no errors, no
`sorry`, no `axiom`, no `@[implemented_by]`.  `#print axioms` on every new
headline theorem reports exactly `propext, Classical.choice, Quot.sound`.

New modules (all under `RequestProject/NavierStokes/`):

| module | content |
|---|---|
| `CriticalDyadicWeight.lean` | the literal dyadic weight `w(k)=2^{⌈log₂|k|_∞⌉}`; both `DyadicShellBounds` fields proved; `w(p+q) ≤ 2(w p + w q)`; the `ℓ¹` divergence no-go |
| `CriticalWeightedGalerkin.lean` | S0 folds on `GalerkinFlow`; S2a pairing symmetry; S1a pointwise split; S1b integrated identity (unconditional) |
| `CriticalProductionAbsorption.lean` | the S2b target `S2bAbsorption`; its consumer `retained_viscosity_budget`; homogeneity of the folds; `no_subcubic_remainder_absorption` |
| `CriticalProductionWitness.lean` | explicit admissible triad state with literal critical production `12` (and unweighted production `0`), discharging the no-go's hypothesis |
| `CriticalWeightDifferenceTransfer.lean` | the weight-difference (commutator) identity for the weighted production, constant-weight neutrality, and the shell-boundary localisation |

## 5. S2b — the primary task, and what was found

The immediate instruction was to prove, or to recover and certify a historical
proof of, the literal inequality `N_N(T) ≤ a D_N(T) + ∫R406` for the constructed
`N_N`.

* **It was not proved.**  S2b remains open.
* **No historical producer exists in the supplied corpus.**  Every occurrence of
  the estimate is a record field, a compiler consuming it, or a target
  statement; the table in `../FOUR_LANE_DASHBOARD.md` §2 lists each owner and
  its exact form, together with the upstream status constants that say the same
  (`round104PhysicalUniformSignedCriticalProductionClosed = false`,
  `round507LiteralR406RemainderSameObjectWeldClosed = false`,
  `round410SignedPhaseSensitiveCancellationStillOpen = true`).
* **What was established instead** (all machine-checked here): the literal folds
  and the two identities they satisfy (S1a, S1b); the exact homogeneity of the
  three folds; the consequent no-go excluding any state-independent `a` with an
  at-most-quadratic remainder; an explicit state certifying that the weighted
  production really is nonzero while its unweighted counterpart vanishes; the
  cutoff-uniform failure of the Wiener `ℓ¹` majorisation route; the
  cancellation-preserving weight-difference form of the production and its
  localisation to shell-crossing pairs; and the failure of a high-low commutator
  gain for the sharp dyadic multiplier.

Together these say precisely where S2b can live: in the superquadratic part of
the remainder, not in a critical-energy reservoir, not behind an `ℓ¹`
majorisation of the inverse weight, and — given the shell-boundary localisation
together with the failure of a low-leg Lipschitz gain — either behind a smoothed
multiplier (paying the R517 comparison) or inside the signed structure of the
shell-boundary set itself.

## 6. Lane discipline

Lane A was not touched and is not implied by any of the above; its frozen cut is
in `../FOUR_LANE_DASHBOARD.md` §1.  Lanes C and D were audited for dependency
closure and mined only for forcing-independent material (the degree/homogeneity
discipline); no C/D → A or C/D → B transport was constructed, and the external
released C/D Lean sources are absent from this project, so no build or kernel
receipt for them is claimed.
