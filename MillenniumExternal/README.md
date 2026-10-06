# MillenniumExternal

This directory is the DASHI-side acceptance/audit layer for the independently
pinned LeanDojo Millennium statements.

It is intentionally not another statement formalization. `TerminalCensus.lean`
imports existing DASHI theorem-bearing terminal surfaces; `ExternalTargetFrontier.lean`
keeps the exact cross-version adapter state fail-closed; `All.lean` is the
aggregate typecheck and axiom-audit root.

The external source pin and two-environment build are documented in
`docs/millennium-external-targets.md`.
