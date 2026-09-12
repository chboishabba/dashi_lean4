# Source-tranche audit: the announced R423 Agda bundle is not present

> **Superseded (2026-09-09).** The tranche was re-sent and *is* now present as
> `ns-agda-tranche-20260909.tar.gz` at the project root. It has been unpacked,
> checksum-verified, reviewed and selectively imported; see
> [`ns-agda-tranche-intake-20260909.md`](ns-agda-tranche-intake-20260909.md).
> The findings below remain an accurate record of the earlier pass, when no
> archive, `HANDOFF.md` or `SOURCE_MANIFEST.txt` was present in the tree.

This note records, factually, what was searched for and what was found when the
new source-only Agda NS tranche (announced as reconciled `dashi_agda` master
`74c7bee33`, with `HANDOFF.md` and `SOURCE_MANIFEST.txt`) was to be unpacked
beside the project and reviewed.

## What was searched

* The whole working tree, for `HANDOFF.md` and `SOURCE_MANIFEST.txt` at any
  depth up to three levels, and for any additional archive (`*.tar.gz`,
  `*.zip`) beside the project directory.
* The one archive that is present,
  `toe-dashi-canonical-corpus-handoff-20260901-slim.tar.gz` (84,301 entries),
  listed in full and grepped for `HANDOFF`/`SOURCE_MANIFEST` at top level and
  for Navier–Stokes round numbers.
* The whole tree and the archive listing for the commit string `74c7bee` and
  for any module named with rounds in the 400s.

## What was found

* No `HANDOFF.md` and no `SOURCE_MANIFEST.txt` anywhere, at any level.
* No second archive: the only archive present is the September 1 slim corpus
  handoff, which a previous session already merged.
* No occurrence of `74c7bee` anywhere in the tree or the archive listing.
* No module with a round number in the 400s.  The highest NS-lane Agda round
  material actually on disk is in the 390s
  (`DASHI/Physics/Closure/…Round394…`); `DASHI/Papers/NavierStokes/` tops out at
  Round 228.  The archive contains nothing beyond what is already on disk.

## Consequence for this session

Nothing was imported, because there was nothing new to import, and therefore no
comparison of the current Agda `R423`/cutoff-uniform signed-companion scheduling
surface against the Lean frontier could be made against real sources.  No Agda
kernel was run and **no Agda kernel receipt is claimed** — neither from imports
nor from anything else in this session.

The Lean work of this session (see
[rate-block-gram-bound.md](rate-block-gram-bound.md)) proceeded on the
independently-checked Lean frontier: the truncation-uniform outer-cell
Gram-operator bound at a retained output, equivalently the two scalar
polarization bounds of `TransverseFrameSplit`.  Package A and the literal
periodic Clay regularity target remain explicitly **not** closed.
