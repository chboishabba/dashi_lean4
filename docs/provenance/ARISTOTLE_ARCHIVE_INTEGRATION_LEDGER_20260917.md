# Aristotle archive integration ledger — 2026-09-17

## Purpose

This ledger governs progressive integration of Aristotle/TOE handoff archives
into `dashi_lean4`.  Archive bytes remain immutable provenance material; an
extraction is a reviewable staging operation, not an automatic merge.

## Canonical archive store

The canonical store is outside this worktree:

`/home/c/Documents/code/aristotle-cli-rs/attachments/dashi_lean4-aristotle-archives/`

Current intake locations:

| Location | Role | Count | Status |
| --- | --- | ---: | --- |
| `untriaged-downloads/` | UUID-preserving Download intake | 44 | moved intact; unclassified |
| `dashi_lean4/artifacts/aristotle-archives/` | prior local archive cache | 33 | retained pending checksum reconciliation |

## Identity rules

1. **Archive filename / UUID** is the immutable storage identity. Never
   rewrite archive bytes or replace a file solely because a title matches.
2. **Tranche title** is the stable human-facing identity. Record it exactly as
   declared by the archive handoff/summary/manifest; do not derive it from a
   UUID or a filesystem copy suffix.
3. **SHA-256** is the duplicate identity. Only equal SHA-256 values may be
   collapsed to one canonical archive.
4. A repeated title with different SHA-256 values denotes distinct revisions
   or deliveries and must retain both archive records.

## Required intake record

Create one row per archive in the canonical-store manifest before extraction:

| Field | Meaning |
| --- | --- |
| `archive_uuid_or_filename` | Original filename, retained verbatim |
| `tranche_title` | Declared stable title; blank only until recovered |
| `sha256` | Full archive checksum |
| `bytes` | Exact byte size |
| `original_location` | Download or prior cache location |
| `canonical_location` | Final attachment-store path |
| `top_level_roots` | Tar/zip root directories |
| `handoff_manifest` | Embedded or adjacent manifest/receipt path |
| `duplicate_of` | Canonical checksum record, if exact duplicate |
| `integration_state` | `untriaged`, `staged`, `reviewed`, `promoted`, or `rejected` |

## Intake register

| Archive filename | Tranche title | SHA-256 | Source | Staging path | State | Review result |
| --- | --- | --- | --- | --- | --- | --- |
| `toe-latest-output-20260912.tar.gz` | TOE / DASHI source handoff | `d2647f3ac2f9ba26efdb028ba4c28356cd7cf480f056d7376d2505d2dc10efc8` | `attachments/toe-to-dashi-lean4-20260912/` | `ImportedLeans/_staging/toe-to-dashi-lean4-20260912/` | staged | Its 26-file `Lean/Spine` tree is byte-identical to active `Spine/`, including `Spine/JMD`; do not promote a duplicate Spine copy. Review `RequestProject`, Agda, and provenance payloads separately. |
| `toe-agda-lean-consolidation-20260913.tar.gz` | TOE consolidation brief — 2026-09-13 | `bf25f24ac5b129e1383290495ead4ef592e2302370d5701742d7245b560a41d6` | `attachments/toe-consolidation-tranche-20260913/` | `ImportedLeans/_staging/toe-consolidation-tranche-20260913/` | staged | Primary `RequestProject` has 0 staged-only files and 4 divergent entrypoints; `Spine` has 24 identical and 2 divergent files. Treat as a dated baseline/diff source; preserve donor versions and review divergences before any promotion. |

## Extraction and promotion gate

1. Verify the source archive checksum against its intake record.
2. Extract only to
   `ImportedLeans/_staging/<archive_uuid_or_filename>/` in this worktree.
3. Inventory `Spine`, `Content`, `Ontology`, `RequestProject`, manifests,
   provenance, and dependency declarations.
4. Compare candidate modules with active `Spine/`, `Spine/JMD/`,
   `RequestProject/`, and `ImportedLeans/`; do not overwrite active modules.
5. Promote a reviewed, minimal module set in its own commit with source title,
   UUID, SHA-256, and import/build evidence in the commit message and ledger.
6. Leave the original archive in the canonical store after promotion.

## Branch boundary

All extraction and promotion work happens on `archive-integration/20260917`.
The main `dashi_lean4` worktree and the dirty `aristotle-cli-rs` worktree are
not to be stashed, reset, or modified by this process.
