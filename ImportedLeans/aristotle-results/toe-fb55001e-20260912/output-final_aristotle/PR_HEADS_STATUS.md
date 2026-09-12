# PR_HEADS status — what was actually delivered to this round

The handoff describes an archive containing "the current tracked `dashi_agda`
repository plus `PR_HEADS` metadata and binary patches for fetched PR heads
#602, #604, #605, #606, #607, #610, #612, #613, #614, #615, #616, and #617".

**The PR-specific surfaces are not present in the material available to this
round.**  This is a delivery gap, not a judgement about the pull requests, and
it is recorded here rather than papered over.

## What was searched

| location | result |
|---|---|
| the tracked working tree (`Agda/`, `Lean/`, `scripts/`, all top-level docs) | no `PR_HEADS` file or directory, no `*.patch`, no `*.diff` |
| `git log`, `git branch -a`, `git remote` | a single `Initial commit`; no PR-head refs, no fetched remote branches |
| the three top-level archives (`*-aristotle*.tar.gz`, 12 389 / 12 926 / 12 320 entries) | no entry whose path matches `PR_HEADS`, `.patch` or any of the PR numbers |
| the three archives nested one level inside them | likewise none |

The three top-level archives are *prior-round outputs* of this same workstream
(they contain `output-final_aristotle/…` trees, including the Yang–Mills and
Navier–Stokes lanes that this round is instructed not to touch, and further
nested copies of earlier rounds).  They are not PR heads and carry no PR
metadata.

## Consequences for this round, and how they are enforced

1. Every surface classified in this round is **tracked-tree source**.  No row
   cites a PR ref.  This is machine-checked:
   `Integration.SewingRegistry.no_branch_only_rows` proves that every row of the
   registry has `prov.prRef = none`.
2. The taxonomy nonetheless carries the field
   (`Integration.SewingTaxonomy.Provenance.prRef : Option String`) and the
   predicate `SewnRow.branchOnly`, so a later round that does receive the
   patches can file branch-only rows without changing the schema.
3. **No statement is made about which PR surfaces are already represented in the
   tracked tree.**  Answering that requires the patches; guessing it from module
   names would be exactly the "infer equivalence from shared vocabulary" failure
   the handoff forbids.  The honest status of all twelve PR heads is therefore
   *undetermined here*:

   | PR head | status in this round |
   |---|---|
   | #602, #604, #605, #606, #607, #610, #612, #613, #614, #615, #616, #617 | not delivered; representation in the tracked tree **undetermined** |

## What would close this

The `PR_HEADS` metadata plus the binary patches, or the fetched refs themselves.
With those in hand the check is mechanical: apply each patch to a scratch
worktree, diff the resulting module set against `corpus_index.json` (which
records every tracked module path, its imports and its declaration counts), and
file each PR surface as *already represented* (paths and content both present),
*divergent* (path present, content differs) or *branch-only* (path absent).
`scripts/corpus_inventory.py` regenerates that index in a few seconds, so the
comparison is a small addition rather than new infrastructure.
