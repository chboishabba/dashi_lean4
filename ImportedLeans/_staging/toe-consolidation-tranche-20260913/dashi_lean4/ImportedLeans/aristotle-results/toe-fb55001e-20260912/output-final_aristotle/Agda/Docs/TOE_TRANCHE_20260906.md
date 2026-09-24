# TOE Agda update tranche — 2026-09-06

Base handoff commit: f2eb0e61e025bfbb1da207b91b67c8aeed0b2c8a
Target commit: 49f5193ebedb06649d7217eacf67cfa71dd786b2
Scope: exact source delta from the 2026-09-01 slim handoff to the current merged dashi_agda master.

Contents:
- Current versions of all added, copied, modified, and renamed paths (at repository-relative paths).
- TOE_TRANCHE_20260906.patch: exact binary-safe Git diff from the base commit to the target commit, including deletions.

To update a checkout/extract that matches the base handoff:
    git apply --binary TOE_TRANCHE_20260906.patch

This tranche deliberately excludes raw archives, generated build products, toolchains, caches, and the already-delivered canonical Lean corpus.
