# Unified 0xDA51 Address Space Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement one backwards-compatible `0xDA51 [16|4|44]` ABI across `dashi_lean4`, `dashi_agda`, `zkperf`, and `zkSEC`, adding atlas type 8 without conflating identity with theorem/security authority.

**Architecture:** `dashi_lean4` is the formal ABI owner and proves the bit/arithmetic contract plus type-8 atlas decoding. `dashi_agda` mirrors the wire contract and fixtures. `zkperf` exposes the same parser/encoder for trace-envelope identity, and `zkSEC` accepts DA51 only as evidence identity/provenance while preserving its existing proposal/grounding/admissibility authority boundary.

**Tech Stack:** Lean 4.28 + Mathlib, Agda stdlib primitives, Rust/Serde tests, Python/pytest.

**Spec:** `docs/superpowers/specs/2026-10-17-da51-unified-address-space-design.md`

## Global Constraints

- Prefix `0xDA51`, header split `[16][4][44]`, and type codes 0–7 are ABI-frozen.
- Type 8 is additive and uses `[level:4][biome:4][status:4][serial:12][reserved:20]`.
- Legacy type-0–7 payloads remain opaque in this tranche.
- Status nibble 1 is not itself a proof outside a typed proof-carrying boundary.
- DA51 identity grants no `zkSEC` severity, vulnerability, authorization, exploitability, or admissibility.
- Existing trace/shard IDs are not renumbered.
- Shared golden fixtures must agree on 64-bit integer and 16-hex-digit rendering.

## Review Focus

- Unknown type nibble 9–15 must parse as a DA51 envelope only when explicitly allowed as unknown, never as a known semantic type.
- Type-8 reserved bits must be zero for canonical atlas decoding.
- Invalid atlas level/biome/status codes must fail canonical atlas decoding.
- Existing legacy DA51 trace IDs must remain valid legacy identities and must not be reinterpreted as atlas entries.
- A valid type-8 address with status `provedTrue` must not cause `zkSEC` to promote a security claim without the existing grounding/linkage/invariant path.

---

### Task 1: Canonical Lean DA51 ABI and atlas type 8

**Files:**
- Create: `DA51/Core.lean`
- Create: `DA51/Atlas.lean`
- Create: `DA51/Fixtures.lean`
- Create: `DA51.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces: `DA51.prefixVal`, `DA51.AddrType`, `DA51.mkAddr`, `DA51.prefixOf`, `DA51.typeOf`, `DA51.dataOf`, `DA51.IsValid`, `DA51.Atlas.Coord`, `DA51.Atlas.Coord.address`, `DA51.Atlas.Coord.decode`.
- Produces theorems proving field read-back, 64-bit bound, `UInt64` shift/mask agreement, atlas round-trip/injectivity, reserved-bit rejection, rank ordering, and the 23 golden catalogue addresses.

- [ ] Add fixture/evaluation theorem statements first so missing definitions fail.
- [ ] Implement the minimal canonical header/type registry with frozen codes 0–8.
- [ ] Prove arithmetic decoders and historical `UInt64` extraction agree.
- [ ] Implement type-8 coordinate encoding/decoding with zero-reserved canonicality.
- [ ] Add all 23 atlas literal fixtures and uniqueness proof.
- [ ] Register `DA51` as an opt-in Lean library in `lakefile.toml`.
- [ ] Verify with `lake build DA51` and axiom inspection for principal theorems.
- [ ] Commit the Lean tranche.

### Task 2: Agda DA51 mirror and fixtures

**Files:**
- Create: `DASHI/DA51/Core.agda`
- Create: `DASHI/DA51/Atlas.agda`
- Create: `DASHI/DA51/Fixtures.agda`
- Modify: `DASHI/HME/Trace.agda` only to reference the typed address boundary where compatible.

**Interfaces:**
- Consumes: the frozen numeric contract from Task 1.
- Produces: Agda `DA51Address`, type-code registry 0–8, atlas field record, encoder/decoder, and fixture equalities.

- [ ] Add representative expected-address fixtures before implementation.
- [ ] Implement numeric split/join helpers and prefix/type/data validation.
- [ ] Implement type-8 field encoding/decoding with canonical zero reserved bits.
- [ ] Encode all 23 atlas addresses as fixture equalities.
- [ ] Keep HME trace semantics separate from address identity.
- [ ] Verify with the repository's pinned Agda check command; no holes/postulates in new modules.
- [ ] Commit the Agda tranche.

### Task 3: `zkperf` Rust DA51 envelope

**Files:**
- Create: `src/da51.rs`
- Modify: `src/lib.rs` or crate root module declaration used by this repository.
- Modify: `src/bin/record.rs` only where DA51 metadata is emitted.
- Modify: `zkperf-da51.service` documentation text if needed.
- Test: Rust unit tests colocated in `src/da51.rs` or the repository's existing test layout.

**Interfaces:**
- Produces: `Da51Address(u64)`, known `Da51Type`, prefix/type/data extraction, lower/upper hex parsing/formatting, `AtlasCoord` encode/decode, and validation.
- Existing witness/proof objects remain unchanged except optional envelope metadata.

- [ ] Write golden tests for prefix/type/data, all 23 atlas addresses, malformed prefix, unknown type, invalid fields, nonzero reserved bits, and serial 4095.
- [ ] Implement minimal parser/formatter and known-type registry.
- [ ] Implement atlas type-8 encode/decode.
- [ ] Thread optional DA51 metadata through the trace/shard recording edge without changing proof authority.
- [ ] Run `cargo test` and preserve legacy non-type-8 DA51 identity acceptance.
- [ ] Commit the Rust tranche.

### Task 4: `zkSEC` evidence identity carrier and authority firewall

**Files:**
- Modify: `src/zksec/adapters/contracts.py`
- Modify: `src/zksec/build_mu_exec_from_ingest.py` where producer evidence is normalized.
- Create/modify: focused tests under the repository's existing `tests/` layout.
- Modify: `docs/producer_contracts/mu_exec_ingest_v1.md`.

**Interfaces:**
- Produces: a validated DA51 evidence-reference value carrying address/type/producer/provenance.
- Does not alter the existing rule that only grounded linkage + invariant evaluation may promote evidence into an execution-law failure.

- [ ] Write parser/validation tests and the negative authority-escalation test for a syntactically valid type-8 `provedTrue` address.
- [ ] Implement DA51 evidence-reference parsing/validation.
- [ ] Thread the reference through ingest provenance without changing semantic identity or admissibility rules.
- [ ] Update producer-contract docs to state the DA51 identity/authority separation.
- [ ] Run focused pytest plus existing `mu_exec` fixture tests.
- [ ] Commit the Python tranche.

### Task 5: Cross-repo compatibility audit and PRs

**Files:**
- Create: `docs/DA51_COMPATIBILITY.md` in `dashi_lean4` with final commit SHAs and fixture checksum/manifest.

**Interfaces:**
- Consumes: Tasks 1–4.
- Produces: one reviewable PR per repository and a compatibility ledger.

- [ ] Compare the 23 atlas fixture literals across all four implementations.
- [ ] Record exact branch/commit SHA for each repository.
- [ ] Record which verification commands ran and any unavailable build surface explicitly.
- [ ] Open PRs in dependency order: Lean, Agda, zkperf, zkSEC.
- [ ] Perform final diff review for accidental authority promotion or type-code renumbering.
