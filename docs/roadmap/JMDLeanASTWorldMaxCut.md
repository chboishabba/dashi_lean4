# JMD Lean AST World — P0 phases, deliverables and exact remaining lemmas

**2026-11-09.** This is the primary first-task ledger. The original objective is **one world of the harvested Lean declarations**, then gap matching, then checked proof reuse. Bidirectional translation is P4, not P0. No LLM or AO agent orchestration is required.

## Source of truth, exact scope

- **Frozen repository rosters:** 21,481 global `language:Lean` GitHub repository IDs (34 partitions, 231 pages, 298 raw count/page receipts); 8,764 public JMD stars, 1,996 primary-language Lean stars. These are metadata, **not 21,481 compiled Lean environments or ASTs**.
- **One database:** use existing `dashi_agda/.dashi/repository.sqlite3`; original `repo_symbols`, `repo_symbol_signatures`, `repo_refs`, `repo_requirements` stay the canonical Agda source index. Lean-specific `jmd_lean_world_*` tables share that file. No competing world store.
- **Native Lean AST:** retain lean4export v3 NDJSON `meta`, `in` names, `il` universe nodes, `ie` expression DAG, declaration type/value roots and references. Structural fingerprints are discovery candidates, not Lean kernel equalities.
- **Provenance:** numeric GitHub ID, source owner/name, original commit, module, Lean compiler revision, NDJSON digest, dependency edges, licence/credit when supplied. Never merge proof identities because fingerprints match.

## Actual implementation owners

| Owner | Function | Evidence limit |
|---|---|---|
| `scripts/build_jmd_lean_ast_world.py` | Global+starred roster admission, native v3 AST parsing and persistence | Source written; full 21,481 run not executed in this session |
| `scripts/query_jmd_lean_ast_world.py` | The **only repository queue**; native type-fingerprint and reference-relatedness discovery | Candidate-only; now groups cross-repo fingerprints by same Lean compiler revision |
| `scripts/jmd_lean_world_intake_queue.py` | Source inventory of a clean pinned local checkout with tracked `.lean` files, Git blob SHA and file digest | Not an AST and does not own scheduling |
| `scripts/jmd_lean_ast_batch_capture.py` | Source header candidate → actual Lean `#check` → native `lean4export` artifact | Incomplete for macros/generated declarations; execution needs local Lean |
| `scripts/jmd_lean_ast_world_batch.py` | One bounded local-checkout manifest → source inventory → optional Lean export → same AST importer | Per-repo failure receipts; no clone, no agent, no proof promotion |
| Existing ITIR `itir.formal.inspect/route` | LLM-free **consumer** for actual unpaid DASHI gaps | Not a source AST ingestion engine |

## Exact max-cut

| Gate | Exact deliverable | Standing |
|---|---|---|
| **P0.00 / W01** | Deduplicate all 21,481 global and 1,996 starred Lean IDs by immutable GitHub numeric ID, retaining starred-only repos | Ingestion code present; full roster admission **OPEN for runtime receipt** |
| **P0.01 / W02** | Bind each available local source checkout to exact origin, clean full Git SHA and tracked blob SHA | Source written; full local-source census OPEN |
| **P0.02 / W03** | Account for all pinned `.lean` files per repository, including explicit excluded/unsupported cases | Source written; full coverage OPEN |
| **P0.03 / W04** | Parse every supported native lean4export name/universe/expression constructor without loss | Parser + synthetic tests written; real v3 corpus acceptance OPEN |
| **P0.04 / W05** | Every declaration type/value root resolves to a valid native DAG and its constant refs | Root traversal/source written; real corpus validation OPEN |
| **P0.05 / W06** | Structural fingerprints stable under DAG allocation/binder-name variation without granting semantic equality | Candidate code and negative controls written; true kernel equivalence not claimed |
| **P0.06 / W07** | Cross-repository matches keyed to pinned Lean revision, preserving all distinct proof sources | Query tightened; real candidate report OPEN |
| **P0.07 / W08** | **Complete actual environment declaration coverage**, including generated/macro declarations, rather than only recognized source headers | OPEN: source scanner is expressly incomplete |
| **P0.08 / W09** | Measured repository/module/declaration AST coverage and explicit inaccessible/failed reasons | OPEN: no completed full-world AST coverage receipt |
| **P0.09 / W10** | Rerun at identical revision is idempotent and does not duplicate AST nodes | Existing regression written; full replay OPEN |
| **P0.10 / W11** | Source revision changes update only affected world/debt edges | Existing Agda invalidation owners; actual Lean-world integration OPEN |
| **P0.11 / W12** | First real unpaid DASHI lemma finds the strongest applicable Lean donor in this world | OPEN until native AST candidates exist and actual target types compared |
| **P1 / W13** | Kernel-check a real Lean implication/equivalence and preserve axiom/dependency closure | OPEN; generic composition theorem alone is insufficient |
| **P2** | Incremental source→world refresh and selective obligation reopening | Partial |
| **P3** | Optional selected Lean→Agda target transport when an Agda consumer needs it | Separate conditional lane |
| **P4** | Bidirectional translator stability | Separate `agda2lean` roadmap, not the first task |

These W01–W13 are **acceptance IDs**, not invented names of existing Agda theorem declarations. Search original owners and kernel-check any proof extensions; parser invariants tested in Python are not Agda mathematical theorems.

## Actual runnable local sequence (no CI dependency)

From `dashi_lean4` with a previously indexed `dashi_agda` checkout:

```sh
python scripts/build_jmd_lean_ast_world.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --repositories docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --stars docs/roadmap/jmd_stars/jmd_starred_primary_lean.csv

python scripts/query_jmd_lean_ast_world.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --queue /tmp/jmd-lean-ast-work.jsonl --limit 200
```

Only **existing local checkouts** are accepted by the bounded intake. Input JSONL must contain `github_id`, `repository`, `commit` (40 hex) and `checkout` (local path).

```sh
python scripts/jmd_lean_ast_world_batch.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --checkouts /path/to/pinned_checkouts.jsonl \
  --output /tmp/jmd-lean-world --max-repos 50

# Opt-in: native Lean execution of untrusted third-party packages.
# Run credential-free in a constrained Nix environment with cached dependencies.
python scripts/jmd_lean_ast_world_batch.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --checkouts /path/to/pinned_checkouts.jsonl \
  --output /tmp/jmd-lean-world --capture \
  --max-repos 50 --max-modules 12 --max-declarations 50

python scripts/query_jmd_lean_ast_world.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --same-type-candidates /tmp/jmd-type-candidates.json --limit 100
```

Run test files by `python -m unittest discover -s scripts -p 'test_*jmd*ast*world*.py' -v`, plus `test_jmd_lean_world_intake_queue.py` and `test_jmd_lean_ast_batch_capture.py`. They are source-written; the assistant did **not** run these tests or a Lean kernel in this environment.

## First real acceptance target

Given a pinned source theorem P and an unpaid original DASHI goal Q, automatically retrieve P's actual native AST/type/axiom context; distinguish exact matching, structural candidate, and missing implication; if applicable create an independently checked Lean proof of `P → Q`, preserve attribution, and only then update original proof debt. Without an actual full-corpus AST coverage record, **absence means `index-incomplete`, not `no mathematical candidate exists`.**

**Safety and governance:** no unpublished DASHI sources sent upstream, no ESD edits, no automatic GitHub clone/publish, no Docker or CI requirement. The AO fleet/LLM system is not invoked; ITIR gap finding is a downstream read-only consumer.

## Source acquisition gate — completes the missing metadata-to-checkout connector in source

`scripts/jmd_lean_public_source_acquisition.py` consumes the **existing** `query_jmd_lean_ast_world.py --queue` JSONL, deduplicates numeric repository IDs, and emits `(github_id, repository, commit, checkout)` for already-pinned checkouts or an opt-in bounded public `git clone`. The default is **dry-run**. Neither action builds Lean or launches AO/LLM workers. Git identity, dirty tracked source, duplicate IDs, timeouts and failed clones have explicit residuals. Seven offline unit tests were added.

```sh
# Default: inspect existing local checkouts; no network.
python scripts/jmd_lean_public_source_acquisition.py \
  --queue /tmp/jmd-lean-ast-work.jsonl \
  --checkout-root /path/to/lean-checkouts \
  --output /tmp/jmd-source-acquisition --limit 20

# Optional network acquisition: deliberately bounded and rate limited.
python scripts/jmd_lean_public_source_acquisition.py \
  --queue /tmp/jmd-lean-ast-work.jsonl \
  --checkout-root /path/to/lean-checkouts \
  --output /tmp/jmd-source-acquisition --limit 20 --acquire --delay 1.5

# The resulting /tmp/jmd-source-acquisition/pinned_checkouts.jsonl
# is the exact input to scripts/jmd_lean_ast_world_batch.py.
```

**W02 expanded exact residual:** entire global corpus source acquisition is a substantial network, storage and licensing operation; its 21,481 entries are not claimed cloned or elaborated. A completed source manifest must record successes, explicit failures and the pinned original commit. Running third-party `lake` commands remains a *separate* opt-in action inside an isolated Nix environment.

**Runtime verification:** the acquisition and AST-world scripts were committed with tests; those tests and the full source scan have not been run from the assistant's environment. No full AST coverage is yet established.

## Real v3 export format cross-check (not a mathematical proof)

`docs/roadmap/JMDLeanASTV3RealCorpusAudit.json` records an independent read-only inspection of the actual upstream artifact `formalverification/lean2agda/corpus/list-reverse-reverse/lean/term.ndjson` (GitHub blob `0361fcf36279860765d02211660b908ebe771c2b`). This is Lean 4.33.1, lean4export format 3.1.0, 1,073 NDJSON records, 195 nonroot name nodes, 14 universe nodes, 835 expression DAG nodes, and 41 declarations including the inductive group. Across every available declaration type, 21 value roots and seven recursor RHS roots, the independent walk found **zero absent expression or constant-name references**. The scan visited 1,536 expression instances across roots (not unique expression nodes).

This is a **real third-party schema/closure observation**, not an execution of `build_jmd_lean_ast_world.py` or a Lean kernel check, and not evidence of any cross-prover theorem. It provides a meaningful external v3 regression target, unlike synthetic fixtures alone. The full 21,481-roster admission and AST census are still open.


## P0 implementation correction — 11 November 2026: ephemeral native AST handoff

The separate `dashi_agda` worker PR
[#1491](https://github.com/chboishabba/dashi_agda/pull/1491)
now has source-written, selected-declaration native
`lean4export` execution inside its ephemeral source workspace,
before source cleanup. The worker also contains an optional verified
local compiled-import cache keyed by pinned source hashes and Lean
version. This is not a full Lake project builder, an untrusted
execution sandbox, or the final kernel-proof certificate.

The **single** PR #105 world importer remains
`scripts/build_jmd_lean_ast_world.py`. Its new
`scripts/jmd_lean_ephemeral_ast_handoff.py` is only a strict adapter:
it takes the worker's source-bound JSON receipt, validates
the original repository/commit, source-closure equality and
content-addressed native NDJSON bytes, then emits the same manifest
format already consumed by `--exports`. It does not create another
index, rewrite native Lean expressions, or claim proof authority.

```sh
# PR #1491 worker (trusted source, matching Lean + exporter):
bash scripts/run_lean_world_nix.sh owner/repo FULL_40_SHA Target.lean \
  --compile-local-imports --compiled-cache-dir /path/to/cache \
  --native-declaration Chosen.theorem \
  --native-out /path/to/export-artifacts \
  --export-bin /path/to/compatible/lean4export \
  > /tmp/worker-v3-receipt.json

# From PR #105 checkout:
python scripts/jmd_lean_ephemeral_ast_handoff.py \
  --receipt /tmp/worker-v3-receipt.json \
  --github-id ORIGINAL_NUMERIC_REPOSITORY_ID \
  --manifest-out /tmp/native-v3-export-manifest.jsonl

python scripts/build_jmd_lean_ast_world.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --repositories docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --exports /tmp/native-v3-export-manifest.jsonl
```

**Acceptance delta:** W02/W03 local closure assembly and W04 selected
native producer are now source-written. W04/W05 still require an actual
`lean4export` v3 DAG replay through the importer; W07 complete
environment declaration enumeration remains open. W08/W09 full
corpus coverage, W10 idempotent live replay, W11 dependency-delta
integration, W12 first original unpaid DASHI proof reuse and W13
kernel payment are still **OPEN**. PostgreSQL integration belongs to
the existing PR #1484 and is not silently replaced by SQLite-only
source admission.

The first real acceptance receipt is an original pinned module,
an original native v3 artifact, **full DAG parser acceptance**,
persistent world counts, and a candidate query linked to the
original declaration type. No LLM orchestration or translator
round-trip is on this P0 path. No real Nix/Lean/PostgreSQL run is
asserted by source-writing these changes.
