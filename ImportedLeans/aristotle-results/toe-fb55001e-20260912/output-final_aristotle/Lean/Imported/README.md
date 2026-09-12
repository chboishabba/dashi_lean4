# `Lean/Imported` — ingested, **not yet promoted**

This directory holds Lean sources mined out of the handoff archive supplied to
this round (`toe-dashi-canonical-corpus-handoff-20260830`).  The archive itself
has been deleted: it was a transport medium, not part of the corpus.

## What is here

Every file is a Lean source that was **not already present, byte-for-byte, in
`Lean/`**.  The content-addressed store inside the archive held 2 472 distinct
Lean blobs across 55 nested handoffs; after

* dropping blobs whose content is already in the tracked tree,
* dropping Yang–Mills and Navier–Stokes paths (outside this cutset), and
* keeping, for each logical module path, only the copy from the most recent
  archive,

2 427 files remained.  A second, content-level dedupe then removed 998 files
whose bytes were reachable by more than one path; eight further files were
removed because their paths had escaped the Yang–Mills filter; and 58 that clear
the promotion bar below were moved out into `Lean/Promoted`.  **1 341 files
remain here.**  `INGESTION_INDEX.csv` lists them with the date of the handoff
they came from.  No tarball hash, blob shard or member path is retained:
transport provenance is deliberately discarded.

## Authority of this directory

**None of it is built, and none of it is a checked theorem of this project.**

`lakefile.toml` does not glob `Imported.*`, so nothing here is elaborated by
`lake build`.  These files were produced against other projects, other Mathlib
revisions and other toolchains; a file being present here says only that some
earlier session wrote it.

The promotion ladder this project uses is

```
present in Imported/  ⟶  compiles in this toolchain  ⟶  wired into a library
                      ⟶  axiom-audited  ⟶  cited by a canonical module
```

and each arrow is a separate step.  `Lean/Integration/CorpusPromotion.lean`
states that ladder formally and proves that the earlier rungs do not imply the
later ones — the machine-checked form of "the theorem is in one of the tars"
not being the same as "the corpus owns the theorem".

## Where each file stands

`PROMOTION_STATUS.csv` records, for every path, the rung it actually reaches,
as decided by `scripts/promotion_status.py`:

* `wired` (58) — elaborates cleanly, no `sorry`/`axiom`/`native_decide`, and has
  been moved to `Lean/Promoted` and built by the `Promoted` library;
* `elaborates` (4) — clean here, but held out of the library because they prove
  by `native_decide` or declare an axiom of their own;
* `elaborates-with-sorry` (15) — elaboration is not a proof;
* `fails` (244) — errors in this toolchain; the first error line is recorded;
* `not-attempted` (1 078) — imports a library root that does not exist here.

Nothing above `wired` is decided mechanically: no entry in that file claims that
a module's statement corresponds to the source it was formalised from.

Material that survives review should be *moved* into the canonical libraries
(`Integration`, `Synthesis`, `Spine`, `Cuisine`) with a docstring recording the
mathematical source of the claim, and deleted from here.  This directory is
expected to shrink.
