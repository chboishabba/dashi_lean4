# Millennium external acceptance status

Pinned upstream: `lean-dojo/LeanMillenniumPrizeProblems@603053dc267cf3efe422f438eb78098c0ececd6f`.

This layer is fail-closed: `GREEN` means a theorem term has kernel-checked
against the exact pinned upstream proposition. Source-written adapters, theorem
names, registry strings, historical solution status, or Boolean receipts do not
count.

The exact same-kernel audit surface now imports and `#check`s all seven pinned
problem statements. That is a conformance result only: it does not turn an open
mathematical producer, an incomplete upstream specification, or a historically
solved-but-unformalized problem into an exact proof receipt.

| Problem | Current max-cut | State |
|---|---|---|
| P vs NP | Agda literal SAT lower-bound compiler exists; universal polynomial SAT failure remains uninhabited in current source; exact machine-model transport also remains | RED-MATH |
| RH | Exact LeanDojo ↔ Mathlib `RiemannHypothesis` weld source-written; current DASHI global/high-zero producer remains open | RED-MATH |
| Navier–Stokes | Literal independent Clay C/D theorem terms already exist; only `ClaySpec C/D ↔ LeanDojo Fefferman C/D` same-statement/representation weld remains; no new fluid estimate belongs here | RED-TYPE |
| Hodge | Pinned LeanDojo statement explicitly incomplete; stronger DASHI algebraic-cycle programme remains authoritative | UPSTREAM-INCOMPLETE |
| BSD | Exact upstream target compiles from `Rank.Existence + finite rank`; DASHI same-curve rank carriers are wired to a typed weld, while universal rank equality remains open | RED-MATH |
| Yang–Mills | Pinned LeanDojo statement explicitly incomplete; stronger DASHI OS/QFT/mass-gap programme remains authoritative | UPSTREAM-INCOMPLETE |
| Poincare | Pinned statement is historically solved, but upstream explicitly does not include Perelman's Lean proof; retained only as an exact statement/regression surface | UPSTREAM-SOLVED-UNFORMALIZED |

## What the max-cut rules out

The current exact-target work removes statement-name drift and the earlier
cross-toolchain excuse: the pinned LeanDojo statements and the strongest root
DASHI donors can co-elaborate in one Lean environment. The surviving REDs are
therefore intentionally narrow:

- RH: produce Mathlib's actual `_root_.RiemannHypothesis`;
- BSD: inhabit the existing same-object rank/continuation weld and the universal
  rank equality it consumes;
- P vs NP: produce the universal polynomial SAT failure/lower-bound theorem and
  certify the machine-model transport;
- NS C/D: prove the proposition-level representation weld between the already
  proved independent Clay specification and LeanDojo's Fefferman carrier.

No adapter is allowed to add a fresh Millennium hypothesis merely to make one
of these endpoints typecheck.

## Kernel receipts

The GitHub workflow builds the immutable upstream package in its native Lean
4.31 graph, probes the exact faithful target source beside DASHI under DASHI's
kernel, probes the nested literal NS C/D project beside the exact LeanDojo
statements, and runs the DASHI terminal/axiom audit.

The current connector-visible exact head still has no pull-request workflow run.
Therefore the new tranche is **SOURCE-WRITTEN / KERNEL-PENDING** and no lane is
promoted to `GREEN` on static inspection alone.
