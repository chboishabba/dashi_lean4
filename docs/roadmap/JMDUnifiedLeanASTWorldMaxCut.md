# JMD Unified Lean AST World — canonical P0 roadmap and exact max-cut

Status: **2026-11-09, code committed, full-corpus execution outstanding**.
This is the governing P0 document for the accumulated Lean repositories,
superseding translator-centric and image-specific roadmaps **for P0 only**.

## Actual first job

Unify the independent GitHub-wide Lean repository harvest and JMD-starred
Lean repository harvest into ONE versioned, queryable mathematical source
world. Only after source-declaration and AST ingestion do we invoke existing
AO/ITIR gap-finding. No LLM is required for any of these steps.

Data sources committed on dashi_lean4 PR #105:

- **21,481** unique GitHub-wide language:Lean repository IDs at the
  2026-11-09 search snapshot (34 creation-date partitions).
- **8,764** public JMD stars, of which **1,996** have primary language Lean,
  at the independently recorded star-list snapshot.
- **Do not add 21,481 + 1,996**: the total *union* is determined by numeric
  GitHub ID with overlaps computed during world admission.
- These are **repositories** and **search metadata**, not Lean ASTs,
  elaborated types or certified proofs.

Native world DB: the existing dashi_agda preflight database,
\`.dashi/repository.sqlite3\`. Do not create a separate semantic index,
PostgreSQL authority, agent framework, or fleet. Existing
\`dashi-repo\`, \`repo_symbols\`, \`repo_symbol_signatures\`, \`repo_refs\`,
\`repo_requirements\`, ITIR \`itir.formal.inspect\` and \`itir.formal.route\`
remain the discoverability and gap-join owners.

## World schema and staged evidence

| Stage | Exact substrate / identity | Evidence and authority |
|---|---|---|
| **S0 repository metadata** | \`jmd_lean_world_repositories\` keyed by numeric GitHub ID; global/starred union; source snapshot | Metadata only. Not AST |
| **S1 pinned source inventory** | \`jmd_lean_world_source_files\` keyed by ID, git commit, path with Git blob SHA and file SHA256 | Source presence, not parsed theorem |
| **S2 native Lean AST** | \`jmd_lean_world_exports\`, \`names\`, \`levels\`, \`ast\`, \`declarations\`, \`refs\` | Native lean4export v3 indexed typed DAG, source-bound candidate |
| **S3 discovery projection** | Clearly marked virtual Lean-export file, \`repo_symbols\`, \`repo_symbol_signatures\`, \`repo_refs\` | Candidate-only native discovery; no invented Agda source lines |
| **S4 verified reuse** | Actual elaborated Lean statement + donor term checked by target Lean kernel | Not produced merely by S0–S3 |
| **S5 Agda consumer payment** | Independently kernel-accepted Agda target/transport, where needed | Separate optional boundary |

The virtual Lean export paths carry the prefix
\`jmd-lean-export://\`. They are NOT files under the Agda source root,
nor evidence of a physical source line.

## Implemented source files (Lean PR #105)

- \`scripts/build_jmd_lean_ast_world.py\`: additive global/stars union,
  export-v3 input parser (including name trie, numeric-name components,
  universe levels, expressions, inductives, constructors, recursors),
  declaration/type roots, native constant references, candidate-only
  graph fingerprints, source/export hashes and per-stage counts.
- \`scripts/index_jmd_lean_checkout_sources.py\`: read-only source
  inventory from already-pinned local Git checkouts, or a numeric-ID
  mirror directory; verifies origin, HEAD and tracked file identity.
- \`scripts/query_jmd_lean_ast_world.py\`: starred-first missing-work
  queue, cross-export type-fingerprint candidate groups and native
  dependency neighbourhoods; retains candidate-only status.
- \`scripts/mirror_jmd_lean_sources.py\`: opt-in bounded public Git
  clone of named repositories, safe pin read, retryable batch offsets;
  does NOT execute third-party packages.
- \`scripts/project_jmd_lean_ast_to_dashi_repo.py\`: candidate-only
  projection to **existing** dashi-repo symbol/signature/reference
  tables, without overwriting Agda mathematical owners.
- \`scripts/test_build_jmd_lean_ast_world.py\`,
  \`test_index_jmd_lean_checkout_sources.py\`,
  \`test_query_jmd_lean_ast_world.py\`,
  \`test_project_jmd_lean_ast_to_dashi_repo.py\`: offline positive
  fixtures, identity/authority negatives, and local Git tests.
- Existing \`scripts/audit_jmd_formal_corpus.py\` remains the
  independent source-manifest accounting check.

These programs have been committed through GitHub. The actual 21k-row
world-building run and the newly added unit tests have **not** been
executed inside this assistant environment, which has no local Lean
toolchain, canonical repository DB or mounted GitHub CSV inputs.

## Complete P0 execution path (no orchestration required)

From an existing clean dashi_agda checkout:

\`\`\`sh
dashi-repo index --root .
\`\`\`

From dashi_lean4 PR #105 checkout (same host, using the existing DB):

\`\`\`sh
DB=/path/to/dashi_agda/.dashi/repository.sqlite3
GLOBAL=docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv
STARS=docs/roadmap/jmd_stars/jmd_starred_primary_lean.csv

python scripts/audit_jmd_formal_corpus.py

python scripts/build_jmd_lean_ast_world.py \
  --database "$DB" --repositories "$GLOBAL" --stars "$STARS"

python scripts/query_jmd_lean_ast_world.py \
  --database "$DB" --queue /tmp/jmd-lean-world-queue.jsonl --limit 0
\`\`\`

Acquire only if actual sources are not already locally mirrored:

\`\`\`sh
python scripts/mirror_jmd_lean_sources.py \
  --queue /tmp/jmd-lean-world-queue.jsonl \
  --mirror-root /data/jmd-lean-mirrors \
  --out-checkouts /tmp/jmd-pinned-checkouts.jsonl \
  --out-failures /tmp/jmd-acquisition-residuals.jsonl \
  --max-repos 20 --offset 0 --allow-network

python scripts/index_jmd_lean_checkout_sources.py \
  --database "$DB" --checkouts /tmp/jmd-pinned-checkouts.jsonl
\`\`\`

Repeat 20-repository chunks with offset 20, 40, 60, and so on; source
processing is source-driven, bounded and incremental. If repositories
are *already* checked out under numeric GitHub IDs, skip network:

\`\`\`sh
python scripts/index_jmd_lean_checkout_sources.py \
  --database "$DB" --mirrors-root /data/jmd-lean-mirrors
\`\`\`

For a **real** selected declaration in a pinned Lean checkout, run the
already installed, compatible native \`lean4export\` (where available)
in a resource-limited, credential-free Nix environment:

\`\`\`sh
# Example shape; replace with a real module/constant and installed exporter:
lake exe lean4export My.Module -- My.Namespace.theorem > /tmp/lean-theorem.ndjson
\`\`\`

Then supply an exact JSONL source manifest (GitHub ID, matching owner,
full commit, module, export path):

\`\`\`json
{"github_id":123,"full_name":"owner/repo","commit":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","module":"My.Module","path":"/tmp/lean-theorem.ndjson"}
\`\`\`

\`\`\`sh
python scripts/build_jmd_lean_ast_world.py \
  --database "$DB" --exports /tmp/native-lean-exports.jsonl

python scripts/project_jmd_lean_ast_to_dashi_repo.py --database "$DB"

python scripts/query_jmd_lean_ast_world.py \
  --database "$DB" --same-type-candidates /tmp/lean-type-candidates.json \
  --related My.Namespace.theorem --limit 50
\`\`\`

The example IDs/SHAs/theorem are illustrative, not claims of a checked
source record. Actual module and type evidence comes from the selected
export. Running untrusted source build scripts requires a sandbox: Nix,
not Docker, with no credentials or unpublished DASHI material.

## Actual native-format inspection completed

A live-source read of upstream \`formalverification/lean2agda\`'s
\`corpus/nat-gcd-self/lean/term.ndjson\` (a genuine lean4export v3
fixture) gave **13,047 NDJSON records**, **1,921 explicit name entries**,
**26 universe entries**, **10,818 expression entries** and **334
declarations**, including inductive families and recursor rules.
An independent structural pass found all **334 declaration type roots**
resolved through the indexed graph. This is useful parser-format
evidence, **not** a complete run of the new Python importer and not
a proof that all 21,481 source repositories have been compiled.

## Correct global priority and exact remaining lemmas

| Gate | Narrowest unpaid result | Standing |
|---|---|---|
| **P0/W00** | Run the full real global+starred union, verify all numeric IDs and provenance, report actual overlap/union size | Source implementation written; execution OPEN |
| **P0/W01** | Acquire the selected bounded pinned checkouts, validate source inventories and negative controls | Source implementation written; full-corpus acquisition OPEN |
| **P0/W02** | Run actual native Lean exports in source-compatible toolchains; account for non-Lake projects and unsupported revisions | OPEN at corpus scale; selected exporter ingestion exists |
| **P0/W03** | Establish complete typed AST for selected declarations: native type roots, universe levels, inductive/recursor roots and dependency closure | Parser written; real importer acceptance and general coverage OPEN |
| **P0/W04** | Source-pin theorem evidence: verify export belongs to the exact Git checkout, installed toolchain, and checker environment | OPEN; source and exporter revisions currently recorded separately |
| **P0/W05** | Publish candidate-only Lean declarations to existing \`dashi-repo\` search, without Agda proof promotion or fake physical source lines | Projection written; live discovery replay OPEN |
| **P0/W06** | Incremental delta/restart: per-repo source changes invalidate only their AST and downstream candidates; distinct pinned revisions coexist | Partial provenance and idempotence; full selective replay OPEN |
| **P1/G01** | Feed actual indexed Lean statement AST neighbours into ITIR/AO's existing unpaid obligation inventory | OPEN, now possible once W00–W05 run |
| **P1/G02** | For a source-pinned donor \(P\), obtain a kernel-accepted Lean implication \(P\to Q\) to the exact original target \(Q\) | OPEN for real donor |
| **P1/G03** | Preserve all donor proof identities, transitive axiom dependencies and attribution; do not conflate structural hashes with definitionally equal types | Existing formal owners; real corpus instance OPEN |
| **P2** | Incremental world update and minimal independent proof reopening | Real replay OPEN |
| **P3** | Selected Lean-to-Agda transport only when the Agda mathematical consumer requires it | Separate optional lane |
| **P4** | Bidirectional translator fixed-point research | Separate lower-priority lane |

The theorem names for W03–W06 are acceptance contracts, not asserted
existing Agda/Lean lemmas. The *first decisive* mathematical proof is a
real source-aware donor/target implication and then an original target
checker payment. No amount of metadata ingestion, QID/OEIS overlap,
structural AST hashing, or exporter success is itself such a proof.

## Maximum cut / Pareto acceptance sequence

1. Pay W00: one canonical database containing **all** distinct accumulated
   Lean repository IDs, with separate global/starred provenance.
2. Pay W01–W03 for an initial bounded batch: source files and actual native
   kernel AST entries, not just a repo-name/title index.
3. Pay W05: native \`dashi-repo discover\` finds the Lean AST symbol with its
   source revision, and candidate status remains nonproof.
4. Pay G01/G02: the ITIR script joins a *real* outstanding mathematical
   target to one pinned Lean donor; an actual Lean checker accepts the
   required proof.
5. Pay W04/W06: demonstrate stale exporter rejection and minimal
   dependency invalidation. Scale in bounded batches, prioritising
   JMD-starred repositories and known high-alpha theorem families.

Keep the exact historical failures and missing packages as explicit
residuals. Do not claim missing source coverage is mathematical
nonexistence.
