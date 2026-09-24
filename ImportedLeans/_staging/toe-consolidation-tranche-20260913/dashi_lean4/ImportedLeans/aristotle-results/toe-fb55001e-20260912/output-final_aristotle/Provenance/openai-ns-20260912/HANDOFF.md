# OpenAI Navier–Stokes Lean archaeology tranche — 2026-09-12

## Upstream provenance

- Repository: `https://github.com/openai/NavierStokesAndEuler`
- Pinned commit: `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
- Commit date: 2026-09-10T13:40:53Z
- Official announcement: `https://openai.com/index/navier-stokes-solution/`
- Official paper: `https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf`
- Current dashi_agda master independently checked before delivery:
  `4c8ebfb733f5768ce7ed61388cc5272ececd5d0d`.

## Scope boundary

This upstream Lean proof establishes forced finite-time blowup with smooth,
compactly supported force and bounded kinetic energy (the Clay C/D
alternatives).  It is not interchangeable with the existing DASHI
arbitrary-data/global-regularity route.  Do not merge claims by name or topic.

## Required archaeology and BIDI work

Index every delivered Lean file, import edge, declaration and theorem lineage.
Build a theorem-by-theorem comparison between the upstream proof and DASHI's
Lean and Agda corpus:

1. state each endpoint, domain, forcing regime, solution notion and consumer;
2. identify definitional matches, transportable interfaces, and mismatches;
3. construct narrow bidirectional adapters only when the current consumer
   actually factors through the proved carrier;
4. preserve all older source and provenance rather than overwriting it;
5. produce a timeline from archived DASHI work through the public proof and
   name the exact derivation/dependency chain for every reuse claim.

Agda remains the broad searchable source/provenance map.  Lean is the
consolidated theorem-bearing surface: prefer importing or adapting a real Lean
proof over duplicating it as a Boolean ledger or re-proving equivalent generic
infrastructure.  Do not assert that the historical DASHI NS programme already
contains the OpenAI proof unless the endpoint and full consumer chain match.

No build is requested by this delivery.  This archive excludes `.git`, `.lake`,
olean files and generated build outputs.
