# DA51 cross-repository compatibility audit

Date: 2026-10-17

This ledger records the completed max-cut consolidation across `dashi_lean4`, `dashi_agda`, `zkperf`, and `zkSEC`.

## Frozen ABI

```text
[prefix:16][type:4][data:44]
prefix = 0xDA51
```

Historical type codes `0`–`7` keep their numeric assignments. Type `8` is additive and means `atlasEntry`.

Type-8 data is:

```text
[level:4][biome:4][status:4][serial:12][reserved:20]
```

Canonical atlas decoding requires recognized level/biome/status codes and zero reserved bits.

## Final implementation heads

| repository | branch | head | PR |
|---|---|---|---|
| `chboishabba/dashi_lean4` | `design/da51-unified-address-space` | `190ca2fdaa8b8d18d58b4cbcef914e4483968d26` | #81 |
| `chboishabba/dashi_agda` | `feat/da51-unified-address-space` | `3749ca1bf178e1a93d5b31ee060f17472ec78d44` | #1219 |
| `chboishabba/zkperf` | `feat/da51-unified-address-space` | `5b8f3f75af5714ea6b66f8fb7c580ab263ce4440` | #2 |
| `chboishabba/zkSEC` | `feat/da51-unified-address-space` | `55176f78fefb1bd5a7645f739c80ffb283541bea` | #1 |

## Shared fixture contract

Every repository contains the same `fixtures/da51_v1.json` content.

- Git blob SHA: `f6135a9637af405f3327bcf9a6a828fdb197d79a`
- SHA-256: `3a2f191afd465b52ba1db7774c0cf3d02d1ee4f099ea62cd33802ab52293cd75`
- atlas addresses: 23
- serials: exactly `0` through `22`
- decoded vectors: type, level, biome, status, serial and reserved fields for every catalogue address
- negative fixtures: wrong prefix, unassigned type, invalid atlas level/biome/status, nonzero reserved bits
- maximum serial fixture: `4095`
- authority fixture: address identity, provenance and external authority are explicitly distinct

## Repository responsibilities

### `dashi_lean4`

Normative formal ABI owner:

- canonical prefix/header/type registry;
- arithmetic constructor and field decoders;
- historical `UInt64` shift/mask equivalence theorems;
- type-8 atlas encoder/decoder;
- encode/decode round trip and address injectivity;
- rank ordering and self-hosted initial-segment theorem;
- proof-carrying `Status.Sound` / typed placement boundary;
- authority-neutral `DA51.EvidenceRef` provenance edges;
- exact catalogue fixtures and canonical ABI documentation.

`Cryptids.Atlas.Address` is a downstream consumer when present: it should import/re-export `DA51.Core` rather than defining another prefix/header/type registry. The current `dashi_lean4` tree does not contain the supplied `Cryptids/Atlas/*` paths, so the migration rule is documented rather than applied to a nonexistent file.

### `dashi_agda`

Executable mirror/interchange owner:

- matching prefix/header/type registry and type-8 decoder;
- exact atlas computations;
- `DASHI.DA51.Provenance.EvidenceRef` with producer/artifact/kind;
- HME `AddressedTrace` now carries the provenance edge separately from `TraceWitness` semantics.

### `zkperf`

Runtime producer:

- `Da51Address(u64)` and known type registry;
- fixed-width parser/formatter and inspector CLI;
- atlas codec and semantic-vector tests;
- legacy `da51...` identity compatibility;
- `Da51EvidenceRef { address, producer, artifact, kind }` producer envelope;
- explicit distinction between DA51 CBOR framing and the 64-bit address ABI.

### `zkSEC`

Security-boundary consumer:

- validates DA51 identity and type-8 syntax;
- threads DA51 into proposal provenance only;
- binds producer identity at ingest;
- exposes an explicit producer/artifact evidence envelope;
- keeps grounding, linkage and invariant evaluation as the security-promotion path;
- regression-tests that atlas status cannot create a security conclusion by itself.

## Authority invariants

```text
DA51 identity != theorem proof
DA51 identity != literature truth
DA51 identity != ZK proof validity
DA51 identity != security violation
DA51 identity != authorization
provenance != semantic identity
provenance != authority
status nibble 1 != proof term outside a typed proof-carrying boundary
```

## Integration rulings

1. The historical type-0–7 payload layouts are not imported as new ABI semantics; only their frozen names/codes are preserved.
2. Existing zkperf DA51 CBOR framing is not conflated with the 64-bit DA51 address.
3. Atlas status bytes cannot cross the zkSEC authority boundary as security conclusions.
4. Each repository remains independently buildable; the compact ABI is mirrored and locked by the shared semantic fixture rather than by introducing build-time cross-repository dependencies.
5. Types `9`–`15` remain unassigned.
