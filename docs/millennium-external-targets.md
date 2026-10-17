# External Millennium acceptance boundary

DASHI now pins the independent LeanDojo statement repository at:

`lean-dojo/LeanMillenniumPrizeProblems@603053dc267cf3efe422f438eb78098c0ececd6f`

The integration is intentionally two-environment because the pinned upstream
uses Lean/mathlib 4.31 while DASHI uses its current 4.35-rc3 toolchain and a
different mathlib revision.

## Acceptance rule

An internal Clay-facing theorem name is not sufficient for closure. For a
faithful upstream target, final external acceptance requires an exact theorem
term against the pinned proposition plus an axiom audit.

Current classifications live in:

- `MillenniumExternal/TerminalCensus.lean`
- `MillenniumExternal/ExternalTargetFrontier.lean`

The classifications are fail-closed. A terminal constructor can exist while
the external adapter remains `redType`; this means the mathematical producer
is present but the exact external carrier has not yet been kernel-welded.

## Upstream incomplete statements

At this pin, LeanDojo itself classifies Hodge and Yang--Mills as
`statement_incomplete`. A proof of those interfaces is therefore not accepted
as a Clay solution. DASHI's stronger Hodge/YM programmes remain useful as
inputs to a future faithful external statement repair.

## Verification

`.github/workflows/millennium-external-targets.yml`:

1. checks out the exact upstream commit;
2. verifies the registry/declaration/status surface;
3. builds upstream under upstream's own toolchain/package graph;
4. builds DASHI's terminal census under DASHI's own graph;
5. prints axioms for the imported DASHI terminal constructors;
6. rejects `sorry`, explicit `axiom`, or `unsafe` escapes in the new adapter layer.
