# DA51 cross-repository compatibility audit

Date: 2026-10-17

This ledger records the max-cut `0xDA51` consolidation across `dashi_lean4`, `dashi_agda`, `zkperf`, and `zkSEC`.

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

## Implementation heads audited

These are the implementation heads immediately before this audit ledger was added:

| repository | branch | implementation head | PR |
|---|---|---|---|
| `chboishabba/dashi_lean4` | `design/da51-unified-address-space` | `a12353d72621ec12a1a443a3e75c29877c56f25c` | #81 |
| `chboishabba/dashi_agda` | `feat/da51-unified-address-space` | `2539fab52d6e8abb11b216653518f0a78bd7f811` | #1219 |
| `chboishabba/zkperf` | `feat/da51-unified-address-space` | `2edd4e94d62bceb0df9a30ab32e3ed417b893c61` | #2 |
| `chboishabba/zkSEC` | `feat/da51-unified-address-space` | `6b250fca7a990bf5e14fb3cd072be9c6595fe324` | #1 |

The Lean PR head advances by one commit when this ledger is added; the table intentionally records the code/CI implementation head that was audited.

## Shared fixture contract

Every repository contains the exact same `fixtures/da51_v1.json` bytes.

- Git blob SHA: `570867dce88bf151a08e172eb978de49a77d7976`
- SHA-256: `cc67f109e5be3cfea89d7a8e0ba2b1b6279b5f012d751efbdb7e3a971e957106`
- atlas addresses: 23
- serials: exactly `0` through `22`
- negative fixtures: wrong prefix, unassigned type, invalid atlas level/biome/status, nonzero reserved bits
- maximum serial fixture: `4095`

An independent arithmetic check decoded all 23 manifest coordinates, verified serial order and uniqueness, rejected every malformed atlas fixture, and round-tripped the maximum serial fixture.

## Repository responsibilities

### `dashi_lean4`

Formal ABI owner for this tranche:

- canonical prefix/header/type registry;
- arithmetic address constructor and field decoders;
- the historical `UInt64` shift/mask equivalence theorems;
- type-8 atlas coordinate encoder/decoder;
- proof of encode/decode round trip and address injectivity;
- rank ordering and self-hosted initial-segment theorem;
- proof-carrying `Status.Sound` / `Placed P` boundary;
- exact 23-address catalogue fixtures.

The current `dashi_lean4` default branch does not contain the supplied `Cryptids/Atlas/Address.lean` or `Cryptids/Atlas/Coordinates.lean` paths, so there was no in-place Cryptids module to refactor. The canonical DA51 core instead mirrors that supplied ABI and catalogue exactly, ready for the Cryptids files to import when they are present in this repository lineage.

### `dashi_agda`

Formal mirror/interchange owner:

- matching prefix/header/type registry;
- matching type-8 atlas fields and canonical decoder;
- exact 23 address computations;
- `AddressedTrace` at the existing HME trace boundary.

The Agda address record is deliberately separate from trace witness semantics.

### `zkperf`

Runtime envelope owner:

- `Da51Address(u64)` and known type registry;
- fixed-width hex parser/formatter and inspector CLI;
- type-8 atlas encoder/decoder and golden tests;
- legacy `da51...` identity compatibility;
- explicit distinction between existing DA51 CBOR framing and the 64-bit address ABI.

No existing trace/shard identifier is renumbered or automatically reinterpreted as an atlas coordinate.

### `zkSEC`

Security-boundary consumer:

- validates DA51 evidence identity and type-8 syntax;
- binds a DA51 producer to the trace producer;
- threads the address into proposal provenance only;
- keeps the existing IR grounding, linkage-score and invariant-evaluation promotion path unchanged;
- regression-tests that atlas status `provedTrue` cannot create an admissible security violation by itself.

## Authority invariants preserved

```text
DA51 identity != theorem proof
DA51 identity != literature truth
DA51 identity != ZK proof validity
DA51 identity != security violation
DA51 identity != authorization
trace provenance != semantic identity
status nibble 1 != proof term outside a typed proof-carrying boundary
```

## Verification status

The PR branches include repository-native verification workflows and fixture checksum assertions. At audit time GitHub had not scheduled Actions runs for these PR heads, and the execution container available to this implementation session has Python/pytest but does not have Lean/Lake, Agda, Cargo or Rustc installed. Therefore this ledger does **not** claim Lean/Agda/Rust build success without evidence.

What is directly verified in-session:

- all four checked-in fixture files have identical Git blob SHA `570867d...`;
- independent 64-bit arithmetic verification accepted all 23 atlas fixtures with serials `0..22` and unique addresses;
- malformed type-8 fixture cases and nonzero reserved bits were independently rejected;
- fixture SHA-256 is `cc67f109...e957106`.

The PR CI definitions are the remaining compiler/toolchain verification gates before merge.

## Integration rulings

1. The historical type-0–7 payload layouts are not imported as new ABI semantics; only the frozen type names/codes are preserved.
2. Existing zkperf `DA51` CBOR framing is not conflated with the 64-bit DA51 address. An address is attached/parsed explicitly.
3. No atlas status byte can cross the zkSEC authority boundary as a security conclusion.
4. Each repository remains independently buildable; the tiny ABI is duplicated and locked by an identical golden manifest rather than creating build-time cross-repository dependencies.
