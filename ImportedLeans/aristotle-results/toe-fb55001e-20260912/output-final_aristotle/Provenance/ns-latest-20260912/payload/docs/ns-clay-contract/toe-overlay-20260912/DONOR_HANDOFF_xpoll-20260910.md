# Full cross-pollination source handoff — 2026-09-10

## Exact source state

This is the complete tracked `DASHI/**/*.agda` source corpus from
`chboishabba/dashi_agda` master commit
`1d3cb03c1dec2d1b1293ada9684b168fd963da8f`.

`SOURCE_MANIFEST.txt` lists every shipped payload: 15,952 Agda files plus four
explicit NS-worker source/report files.  `SHA256SUMS` covers the same payload.
There are no raw archives, `.agdai`, `.olean`, `.lake`, caches, build products,
Git metadata, or virtual environments.

## Why index everything

Do **not** use missing current import closure as a reason to discard a module.
The corpus is an indexed research/provenance archive as well as a collection of
build surfaces.  A module can carry a useful definition, vocabulary, source
atlas, boundary, counterexample, dependency edge, or bridge to a lane that is
not currently buildable in this checkout.  Index all paths and their imports,
even when you defer operational import into an aggregate.  Preserve the module,
its commit and hash; make its status explicit as complete, conditional,
dependency-incomplete, divergent, or deferred.

In particular, cross-pollinate broadly across the unconventional material:
NS/YM/RH, Aristotle/Wikidata, legal/source provenance, ecology and water,
photosynthesis/RTX/optics, exotic gravity, Moonshine/J-invariant, Gödel/Turing,
game theory, cognition, and all other lanes.  Do not be narrow or prudish about
subject matter.  The discipline is provenance and honest claim boundaries, not
topic-based exclusion.

## Recommended intake phases

1. Verify checksums and create a path/hash/import index for every source.
2. Compare every same-path divergence against the local version.  Keep both
   provenance records; reconcile only when the intended declarations/imports
   are preserved.
3. Import dependency-complete groups into appropriate aggregates.
4. Retain dependency-incomplete or conditional modules in the indexed archive
   and record the exact missing edges rather than silently refusing or deleting
   them.
5. Build/Agda-check only where a toolchain and a requested scope exist.  A
   ledger Boolean, compiler receipt or route interface is not by itself a
   physical/theorem closure claim.

## NS worker supplement

Unlike the earlier cutset, this archive deliberately contains
`ns_worker_result/` and lists it in both manifest and checksums.  Read
`ns_worker_result/docs/ns-clay-contract/ns-agda-tranche-intake-20260909.md`.
It records the NS worker's actual R395--R530 reconciliation (159 new, 36 donor
reconciliations, two RingSolver-repair versions retained) and its honest
no-Agda-toolchain limitation.  The included Lean Gram-bound source/documents
also preserve the result that the physical cancellation frontier remains open;
Package A, literal periodic Clay regularity, YM, and RH are not closed here.
