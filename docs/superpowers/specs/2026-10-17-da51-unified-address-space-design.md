# Unified 0xDA51 Address Space — Design

Date: 2026-10-17
Status: design handoff
Scope: `dashi_lean4`, `dashi_agda`, `zkperf`, `zkSEC`

## Intent

Make `0xDA51` one backwards-compatible address ABI across the project rather than four loosely related conventions. Preserve the historical Lean header and type codes 0–7, add atlas coordinates as type 8, keep the existing Agda/zkperf trace-shard lane, and make provenance/security consumers refer to DA51 identities without silently inheriting proof or authority.

Success means:

- one canonical `[prefix:16][type:4][data:44]` contract with prefix `0xDA51`;
- type codes 0–7 retain their historical meanings and numeric codes;
- type 8 is the atlas-entry payload `[level:4][biome:4][status:4][serial:12][reserved:20]`;
- Lean proves arithmetic and `UInt64` extraction agree;
- atlas type-8 encode/decode is round-trip and injective;
- Agda has a matching wire-format/type registry boundary, without claiming semantics for legacy payloads that are not formalized there;
- `zkperf` emits/validates DA51 envelope metadata for trace shards while leaving its existing witness/proof formats intact;
- `zkSEC` accepts DA51 as canonical evidence identity/provenance only, never as a vulnerability, severity, authorization, or proof-of-truth claim;
- fixtures lock cross-language byte/hex compatibility.

## Existing surfaces to preserve

### Historical Lean ABI

The earlier `DA51PrefixClassification` owner defines:

```text
[prefix:16][type:4][data:44]
prefix = 0xDA51
```

and type codes:

```text
0 monsterWalk
1 astNode
2 monsterProtocol
3 nestedCID
4 harmonicPath
5 shardID
6 eigenspaceAddr
7 hauptmodul
```

It also defines the literal `UInt64` extraction contract:

```text
prefix = raw >>> 48
type   = (raw >>> 44) &&& 0xF
data   = raw &&& 0x00000FFFFFFFFFFF
```

These numeric assignments are ABI-frozen.

### `dashi_agda`

The repository already owns DA51 proof/performance traces, source and trace registries, semantic annotation, HME processing, and an SL ↔ DA51 ↔ Agda interchange boundary.

### `zkperf`

`zkperf-da51.service` already describes the live lane as `perf trace → DA51 CBOR shard service`. `zkperf` also owns witness chains, commitments, proof artifacts, CBOR privacy shards, lattice-shard concepts, and performance receipts.

### `zkSEC`

The V1 ingest contract explicitly makes `zkperf` the proposal producer and separates stable canonical identity from append-only provenance. Trace proposals cannot emit vulnerability/severity/authority conclusions. This boundary remains normative.

## Architecture

### 1. Canonical DA51 core in `dashi_lean4`

Add a small standalone module family, independent of atlas semantics:

```text
DA51/Core.lean
DA51/LegacyTypes.lean
DA51/Atlas.lean
DA51/Fixtures.lean
```

`DA51/Core.lean` owns only the wire ABI:

- `prefixVal = 0xDA51`;
- `AddrType` with codes 0–8;
- `mkAddr`, `prefixOf`, `typeOf`, `dataOf`, `IsValid`;
- 64-bit bound and field read-back theorems;
- equality with historical `UInt64` shift/mask extraction;
- type-code injectivity and decoder for recognized type codes.

`DA51/LegacyTypes.lean` documents type 0–7 meanings and preserves the historical names/codes. It does **not** import the old speculative payload layouts or mathematical labels as ABI facts.

`DA51/Atlas.lean` owns type-8 only. It mirrors the proven `Cryptids.Atlas.Address` payload and should be factored so `Cryptids` consumes the canonical core rather than redefining the header.

### 2. Type-8 atlas payload

Wire form:

```text
0x DA51 8 L B S NNN 00000
```

with data layout:

```text
[level:4][biome:4][status:4][serial:12][reserved:20]
```

Rules:

- level codes: `delta0=0`, `pi1=1`, `sigma1=2`, `pi2=3`, `sigma2=4`, `lean=5`;
- biome codes remain 0–8 as currently defined;
- status codes remain `open=0`, `provedTrue=1`, `provedFalse=2`, `trueInLiterature=3`, `falseInLiterature=4`;
- serial is `<4096`;
- reserved bits must be zero for canonical atlas addresses.

Formal obligations:

- encode/decode round trip;
- address injectivity;
- canonical decode rejects bad prefix/type/field codes/nonzero reserved bits;
- numeric ordering by level rank;
- self-hosted initial-segment theorem;
- exact catalogue fixtures for all 23 supplied coordinates;
- no-duplicate catalogue addresses;
- status soundness remains a property of `Placed P`, not of raw bytes.

### 3. `Cryptids` migration

`Cryptids/Atlas/Address.lean` becomes a semantic adapter over the canonical DA51 core. Existing theorem names should be retained where practical via aliases/wrappers to avoid downstream breakage.

`Cryptids/Atlas/Coordinates.lean` remains the catalogue owner. The 23 addresses and all proof-carrying `Placed` terms stay there.

No historical type-0–7 payload semantics are imported into `Cryptids` merely because the header is shared.

### 4. Agda mirror/boundary

Add a focused Agda module family under the existing DA51/HME area:

```text
DASHI/DA51/Core.agda
DASHI/DA51/Atlas.agda
DASHI/DA51/Fixtures.agda
```

Agda owns:

- the 16/4/44 decomposition;
- prefix and type-code registry 0–8;
- type-8 field record and encoder/decoder;
- finite fixture equalities for representative legacy headers and all atlas addresses;
- a typed distinction between `DA51Address` and the semantic payload/provenance attached to it.

The Agda layer does not claim that a zkperf trace, a Lean theorem, or a literature citation is true solely because it has a DA51 address.

### 5. `zkperf` integration

Add a small Rust DA51 envelope module used by the record/shard path rather than redesigning existing witness objects.

Required API:

```text
Da51Address(u64)
Da51Type::{0..8}
prefix/type/data extraction
parse/format hex
validate prefix and known type
AtlasCoord encode/decode for type 8
```

For trace/perf shards, DA51 is an **identity/envelope coordinate**. Existing CBOR witness/proof payloads remain authoritative for their own claims.

Emit optional metadata fields where the existing schema permits:

```text
da51_address
da51_type
da51_version = 1
```

Do not reinterpret old trace IDs as atlas coordinates. Existing historical `da51...` trace values remain legacy DA51 identities unless their type nibble is explicitly 8 and the type-8 canonical decoder accepts them.

Add golden tests using the same fixtures as Lean/Agda.

### 6. `zkSEC` integration

Extend producer/adaptor contracts with a DA51 evidence identity carrier:

```text
Da51EvidenceRef {
  address: u64/string,
  type_code,
  producer,
  provenance
}
```

Policy:

- valid DA51 prefix/type is necessary only for DA51 identity acceptance;
- type 8 may supply atlas catalogue coordinates;
- no DA51 type grants vulnerability, severity, authorization, exploitability, or proof authority;
- a `zkperf` DA51 reference stays proposal-only until the existing grounding/linkage/invariant flow promotes the *underlying evidence*;
- `Placed.sound`/Lean status and `zkSEC` admissibility are separate authority systems.

Tests must include the negative case: a syntactically valid DA51/type-8 address with `status=provedTrue` cannot by itself create an admissible security violation.

### 7. Cross-repo fixture contract

Create one human-readable fixture table copied verbatim across test suites (or generated from one checked-in JSON if dependency policy permits):

- prefix/type/data extraction examples;
- one address for each type code 0–8;
- all 23 atlas addresses;
- malformed prefix;
- unknown type 9–15;
- invalid atlas level/biome/status;
- nonzero type-8 reserved bits;
- maximum serial 4095.

All implementations must agree on the 64-bit integer and 16-hex-digit rendering.

## Trust and authority invariants

These are non-negotiable:

```text
DA51 identity != theorem proof
DA51 identity != literature truth
DA51 identity != zk proof validity
DA51 identity != security violation
DA51 identity != authorization
trace provenance != semantic identity
status nibble 1 != proof term outside the typed Placed boundary
```

Only the Lean `Placed P` constructor may turn status `provedTrue` into `P`, because it carries `Status.Sound P`. Wire decoders expose a status code only.

## Backwards compatibility

- Prefix `0xDA51` is frozen.
- Header split 16/4/44 is frozen.
- Codes 0–7 are frozen.
- Existing trace/shard identifiers are not renumbered.
- Type 8 is additive.
- Legacy payloads remain opaque unless a specific legacy decoder is deliberately ported later.
- Existing `Cryptids.Atlas` theorem names should remain source-compatible where feasible.

## Testing and acceptance

### Lean

- kernel-check all DA51 core and atlas modules;
- no `sorry`;
- print/check axioms for the principal theorems;
- preserve the supplied target that principal atlas format theorems require no stronger axioms than the current project boundary;
- evaluate all 23 catalogue literals.

### Agda

- pinned Agda root for DA51 core/atlas fixtures;
- no holes/postulates/unsafe escapes in the new tranche;
- exact fixture agreement with Lean.

### Rust / `zkperf`

- `cargo test` for DA51 parser/encoder/decoder and golden fixtures;
- compatibility test that existing non-type-8 DA51 IDs remain accepted as legacy identities;
- service/docs updated to state the canonical ABI.

### Python / `zkSEC`

- unit tests for parsing/validation and proposal-only authority boundaries;
- negative authority-escalation tests;
- existing `mu_exec` fixture tests continue to pass.

## Delivery shape

Use separate reviewable PRs, in dependency order:

1. `dashi_lean4`: canonical DA51 core + atlas adapter/fixtures;
2. `dashi_agda`: matching formal boundary + fixtures;
3. `zkperf`: Rust envelope + golden tests + service/schema documentation;
4. `zkSEC`: evidence-reference adapter + authority firewall tests;
5. final cross-repo audit documenting exact commit SHAs and fixture checksum.

No repository should depend at build time on another repository solely to read this 64-bit ABI. The ABI is intentionally tiny and duplicated with golden fixtures so each security/proof boundary remains independently buildable.

## Non-goals

- porting speculative historical type-0–7 payload layouts;
- treating Monster/Bott/eigenspace labels as wire semantics without dedicated proofs;
- changing existing zkperf cryptography, lattice design, or witness-chain format;
- making zkSEC infer security conclusions from atlas status;
- assigning DA51 addresses to every artifact in the ecosystem in this tranche.
