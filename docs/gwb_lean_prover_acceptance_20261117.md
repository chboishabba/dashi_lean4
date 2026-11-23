# GWB Rust/Lean consumer proof — tracked receipts, no TAR output

Working PR: [dashi_lean4 #112](https://github.com/chboishabba/dashi_lean4/pull/112).
SLR Rust owns runtime observations; Agda and Lean own formal proof contracts.
SensibLaw Python is historical, **never** used as the language producer.

## Proof acceptance results reported by operator

The operator ran the prior proof suite at commit `cbd840d6b` and reported:

| Check | Observed |
|---|---:|
| Exact original sentences | 643 |
| Rust candidate deltas | 4,190 |
| Real SLR alternative fibres | 814 |
| Real SLR typed residuals | 15,595 |
| Rust direct/reference parity | PASS |
| Lean fibre/source receipt | PASS |
| GWB scope nonfactorability | PASS |
| Adversarial negative controls | 10 rejected |
| Semantic observer audit | PASS (57 embedded, 73 unmatched role positions) |

These counts come from the operator's PR #112
[local execution receipt](https://github.com/chboishabba/dashi_lean4/pull/112#issuecomment-6937379893).
The actual *raw* per-sentence Rust/Lean logs were local and uncommitted
at that head; they cannot be recovered from the PR comment. Do not
mistake these operator-reported counts for file-backed Git proof receipts.

## Persistent evidence layout

There is **no TAR creation, update, packing, or TAR required to run again**.
Use the canonical in-repo output:

`artifacts/gwb-semantic-proof/`

The runner writes:

- `slr-rust-semantic-expansion.json`: **complete original per-sentence
  candidate alternatives/residuals** as emitted by SLR Rust.
- `semantic_observer_audit.json`: read-only source-backed witness
  pairs for flattening, actor-role eligibility, and year associations.
- `proof_run_manifest.json`: original UTF-8 source SHA, revision,
  exact SLR and JMD commit heads, Lean version, passed gate counts, and
  explicitly unpaid gates.
- Rust and Lean kernel/source/negative-control log files, preserving
  the actual test outputs for review.

The historical article, 3.4 MB flat event projection, 4.5 MB
original parser record, and ~16 MB P0b mention carrier remain **local**
in `.dashi/gwb-source/`, excluded from Git. The source SHA is pinned to
`a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233`
at `enwiki-revid:1385850169`. These are observations, not model truth
or semantic admissions.

## One-time migration: import the ALREADY EXECUTED local result

**No Rust/Lean rerun needed** when the passing proof receipt already exists
inside the previously refreshed local TAR. From JMD repository root, on
PR #112's branch:

```bash
python3 tools/import_gwb_existing_receipts.py \
  gwb_article_proof.tar --delete-on-success
git push
```

The import tool validates the original UTF-8 source and every captured
Rust/Lean success marker, all five actual consumer receipts, counts,
nonpromotion gates, and all ten negative-control logs using the
**same** publisher as a fresh run. It imports the original source
fixture into ignored `.dashi/gwb-source/`, commits only the genuine
results to `artifacts/gwb-semantic-proof/`, and then deletes the old
TAR **only after** verifying that the results directory is clean
(committed). It creates no new TAR.

If you do want a new proof run rather than import existing receipts,
pass the legacy input TAR to the runner once:

```bash
SLR_ROOT=/path/to/slr \
  bash scripts/run_gwb_lean_proof_suite.sh gwb_article_proof.tar
```

This imports original source evidence to `.dashi/gwb-source/`,
runs the checks, and commits the outputs; the TAR itself is unchanged.
For safety, this alternate route does not delete the legacy input.
Use the import command with `--delete-on-success` to retire the TAR
after confirming the existing captured results.

## Subsequent runs — no TAR

```bash
SLR_ROOT=/path/to/slr \
  bash scripts/run_gwb_lean_proof_suite.sh
```

The runner reuses the ignored original source evidence in
`.dashi/gwb-source/` and your cached Lean 4.28.0 `.olean` files.
It calls existing SLR Rust semantic-expansion and production consumer
adequacy crates, then targeted Lean. All **ten** evidence mutations must
be rejected. The receipt publisher verifies exact source SHA/revision,
candidate/fibre/residual counts, five source-specific consumer outcomes,
all required success markers, no `sorryAx`/`admitAx`, and all ten
negative-control logs. If any check fails, **the previous tracked
results remain untouched**.

On success, `tools/publish_gwb_proof_receipts.py` atomically replaces
only `artifacts/gwb-semantic-proof/`, then creates a Git commit affecting
only that directory (not unrelated staged files). A byte-identical rerun
does not commit again. Pass `--no-commit` to the script to leave results
in the working tree for manual staging; or run `git push` afterward
to publish the local commit to this existing PR.

The canonical result publisher has a **15 MiB single Rust-receipt
limit** and **20 MiB total generated-evidence limit**. Larger receipts
must be reviewed; do not hide or truncate semantic alternatives to
make a Git size limit pass.

## What the proofs actually show

The Rust crate `sl-semantic-expansion` produces genuine candidate
alternatives, typed residuals and direct/reference parity, although
its own contract describes the crate as outside the certified direct
production path. That is exactly why the Lean/Agda proof chain is
important, but a Lean receipt checking source coordinates and boundary
conditions does not automatically supply reviewed S28 evidence.

The production consumer-adequacy evaluator returns operationally
adequate source-only consumers and unresolved identity, event date and
world occurrence queries. The actual sentence-18 GWB claim candidate
is used to avoid vacuously treating an empty semantic-reference set
as proof of actor identity.

Still **OPEN**: original DB-native M12/S28 reviewed semantic transport
ledger, actual event-identity and chronology admission, and a
query-specific kernel-backed FactorsThrough witness on that ledger.
The existing Rust parity receipt is not a proof of historical truth.

## Attribution and operations

Reuse existing Agda, SLR and JMD owners and keep source attribution.
Do not rerun spaCy or the SensibLaw/Python mention producer.
No alternative language parser or fabricated semantic coordinate.
No `/tmp` source copies or new PRs. Original input fixtures are
local, receipts live under one Git-tracked results directory.
