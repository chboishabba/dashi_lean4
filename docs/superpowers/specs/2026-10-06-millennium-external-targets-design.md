# External Millennium Target Integration Design

## Goal

Make independently maintained Clay/Millennium Lean statements an explicit acceptance surface for DASHI's existing Millennium proof programmes, without weakening either the upstream statements or DASHI's theorem graph.

## Source authority

Upstream source: `lean-dojo/LeanMillenniumPrizeProblems`.
Pinned commit: `603053dc267cf3efe422f438eb78098c0ececd6f`.
Upstream license: Apache-2.0.
Upstream Lean toolchain at the pin: `leanprover/lean4:v4.31.0`.
DASHI currently uses `leanprover/lean4:v4.35.0-rc3` and its own mathlib revision.

The upstream repository is immutable input. We do not edit upstream declarations to make a DASHI proof fit.

## Architecture

1. `scripts/vendor_millennium_targets.sh` materialises the exact upstream commit into `vendor/LeanMillenniumPrizeProblems` and rejects the wrong commit.
2. `vendor/LeanMillenniumPrizeProblems.VENDOR` records the immutable source identity and expected toolchain.
3. `scripts/audit_millennium_external_targets.py` reads the materialised upstream registry and verifies the expected canonical declaration/status surface.
4. `MillenniumExternal/TerminalCensus.lean` is the DASHI-side typed census of existing terminal constructors. It imports existing DASHI terminal modules only; it introduces no mathematical hypotheses and no replacement Clay statement.
5. `MillenniumExternal/All.lean` is the aggregate DASHI-side typecheck/axiom-audit root.
6. `.github/workflows/millennium-external-targets.yml` performs two independent checks:
   - exact upstream checkout and upstream-native build under upstream's own toolchain/package graph;
   - DASHI terminal-census build under DASHI's own toolchain/package graph.

Because the projects pin incompatible versions of the same package names, direct Lake dependency is deliberately not used. Cross-version interoperability is treated as a compatibility problem, not permission to alter a theorem statement.

## Problems and acceptance targets

The census covers the active DASHI lanes:

- Riemann hypothesis
- Navier--Stokes existence/smoothness
- Yang--Mills existence and mass gap
- Birch--Swinnerton-Dyer
- Hodge conjecture
- P versus NP

Poincare remains in the upstream vendor/audit because it is part of the canonical seven, but no new DASHI proof programme is introduced for an already solved mathematical problem.

For upstream entries marked `statement_incomplete`, notably Hodge and Yang--Mills at this pin, the external statement is an audit input rather than a valid prize acceptance target. DASHI must not promote a proof of an upstream-incomplete proposition to a Clay solution.

## Terminal-constructor rule

The adapter layer must reuse existing terminal constructors. It must not:

- add a new assumption to make an adapter close;
- hide a missing theorem in a structure field;
- replace an upstream proposition by a weaker local proposition;
- equate status booleans with theorem inhabitants;
- conflate source-written with kernel-verified.

If a direct adapter needs more than definitional rewriting / already-proved equivalence, that mismatch is reported as a real seam.

## Verification classes

- `GREEN`: exact external target constructed from an existing DASHI terminal theorem.
- `RED-TYPE`: representation/toolchain/type mismatch.
- `RED-MATH`: exact external proposition exposes a genuinely missing theorem.
- `UPSTREAM-INCOMPLETE`: upstream registry itself marks the target as not a valid prize target.

## Attribution

Upstream definitions and registry metadata remain attributed to LeanDojo and their contributors. DASHI owns only the vendor pin, compatibility/audit machinery, and adapters from DASHI theorem constructors.