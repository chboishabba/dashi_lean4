# Millennium external acceptance status

Pinned upstream: `lean-dojo/LeanMillenniumPrizeProblems@603053dc267cf3efe422f438eb78098c0ececd6f`.

This layer is fail-closed: `GREEN` means a theorem term has kernel-checked
against the exact pinned upstream proposition. Source-written adapters, theorem
names, registry strings, or Boolean receipts do not count.

| Problem | Current max-cut | State |
|---|---|---|
| P vs NP | Agda literal SAT lower-bound compiler exists; universal polynomial SAT failure remains uninhabited in current source; exact machine-model transport also remains | RED-MATH |
| RH | Exact LeanDojo ↔ Mathlib `RiemannHypothesis` weld source-written; current DASHI global/high-zero producer remains open | RED-MATH |
| Navier–Stokes | Literal independent Clay C/D theorem terms already exist; only `ClaySpec C/D ↔ LeanDojo Fefferman C/D` statement weld remains | RED-TYPE |
| Hodge | Pinned LeanDojo statement explicitly incomplete; stronger DASHI algebraic-cycle programme remains authoritative | UPSTREAM-INCOMPLETE |
| BSD | Exact upstream target compiles from `Rank.Existence + finite rank`; DASHI same-curve rank carriers are wired to a typed weld, while universal rank equality remains open | RED-MATH |
| Yang–Mills | Pinned LeanDojo statement explicitly incomplete; stronger DASHI OS/QFT/mass-gap programme remains authoritative | UPSTREAM-INCOMPLETE |
| Poincare | Solved upstream regression only | RED-TYPE |

## Kernel receipts

The GitHub workflow builds the immutable upstream package in its native Lean
4.31 graph, probes the exact faithful target source beside DASHI under DASHI's
kernel, probes the nested literal NS C/D project beside the exact LeanDojo
statements, and runs the DASHI terminal/axiom audit.

The authoring container currently cannot resolve GitHub and GitHub has not yet
surfaced an exact-head workflow run for this branch. Therefore no lane is
promoted to `GREEN` and no local Lean kernel claim is made.
