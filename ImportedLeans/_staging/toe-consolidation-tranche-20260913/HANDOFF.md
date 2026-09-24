# TOE source-only consolidation tranche

Date: 2026-09-13 (Australia/Brisbane)

This is a source-only intake bundle for consolidation work.  Unpack beside a working tree, read `TOE_CONSOLIDATION_BRIEF.md`, `SOURCE_MANIFEST.txt`, and `SHA256SUMS` before importing.  Do not overwrite a project blindly.

Contents:

* `dashi_agda/`: canonical Agda sources, source metadata, and retained documentation from `96511f784` on `master`.
* `dashi_lean4/`: canonical Lean sources, source metadata, active carriers, and retained imported worker source from `ff0b3a02` on `main`.
* `TOE_CONSOLIDATION_BRIEF.md`: the required cross-pollinating consolidation programme.
* Adjacent `SOURCE_MANIFEST.txt`: complete path listing for the delivered source files.
* Adjacent `SHA256SUMS`: checksum verification for the delivery metadata; adjacent `ARCHIVE_SHA256SUM.txt` verifies the compressed bundle itself.

At packaging, both repositories were clean, matched their writable `origin` branches, and GitHub reported zero open PRs for each.  No Lean or Agda build was run in this handoff operation.

Excluded on purpose: Git histories, raw tars/zips, generated build output, `.lake`, `.olean`, `.agdai`, MAlonzo, toolchains, caches, vendor build trees, and other reproducible/non-source payloads.  The omission is recorded in the brief so these are not mistaken for missing theorem sources.
