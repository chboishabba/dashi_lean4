# DA51 Address ABI v1

`dashi_lean4/DA51/Core.lean` is the normative formal owner of the DA51 64-bit address ABI.

```text
[prefix:16][type:4][data:44]
prefix = 0xDA51
```

Type assignments are frozen:

| code | meaning |
|---:|---|
| 0 | monsterWalk |
| 1 | astNode |
| 2 | monsterProtocol |
| 3 | nestedCID |
| 4 | harmonicPath |
| 5 | shardID |
| 6 | eigenspaceAddr |
| 7 | hauptmodul |
| 8 | atlasEntry |
| 9-15 | unassigned/reserved |

Type 8 uses:

```text
[level:4][biome:4][status:4][serial:12][reserved:20]
```

Canonical type-8 addresses require a recognized level, biome and status and zero reserved bits.

## Three distinct layers

1. **Address identity** — the immutable 64-bit DA51 value.
2. **Type semantics** — interpretation of the 44 data bits according to the 4-bit type.
3. **Provenance** — producer-owned evidence edges (`DA51.EvidenceRef`) naming proofs, traces, benchmarks, sources or receipts.

These layers must not be collapsed. In particular, a DA51 address or provenance edge is not by itself theorem truth, literature authority, ZK validity, security severity, exploitability, or authorization.

For typed Lean catalogue owners, `DA51.Atlas.Status.Sound` is the stronger proof-carrying boundary: status `provedTrue` requires `P` and status `provedFalse` requires `¬ P`. Raw wire decoding never manufactures this obligation.

## Cross-language fixture

`fixtures/da51_v1.json` is the shared executable interchange contract. It contains the type registry, all 23 atlas coordinates, decoded semantic vectors, maximum-serial coverage, malformed negative examples and the authority-separation invariants. The same bytes are carried by `dashi_agda`, `zkperf` and `zkSEC` feature branches.

## Cryptids migration rule

`Cryptids.Atlas.Address` must not own another copy of the prefix/header/type registry. When that module is present in the consuming repository, it should import/re-export `DA51.Core` and retain only atlas/project-specific placement concepts (`Level`, `Biome`, `Status.Sound`, `Coord`, `Placed`, catalogue integration). Historical `DA51PrefixClassification` remains lineage documentation, not a second ABI authority.

## Compatibility

Historical codes 0-7 and existing DA51 trace/shard identities are not renumbered. Type 8 is additive. Existing payload layouts for types 0-7 remain opaque to this tranche unless their historical owner defines them separately.
