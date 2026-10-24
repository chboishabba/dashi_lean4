# MillenniumExternal

This directory is the fail-closed acceptance boundary between DASHI's existing
Millennium proof programmes and the independently pinned LeanDojo statements at
commit `603053dc267cf3efe422f438eb78098c0ececd6f`.

It is intentionally not another statement formalization.

## Max-cut rule

For every problem, search and compose in this order:

1. exact external proposition;
2. existing DASHI literal / physical carrier;
3. existing same-object weld or definitional equality;
4. existing terminal constructor;
5. only then introduce a new typed seam.

A new seam must expose exactly the missing transport. It must not restate the
Clay target, replace proof data by a Boolean status receipt, or hide an
unproved mathematical premise inside a wrapper.

## Current exact cuts

- **Riemann hypothesis:** the exact pinned Clay proposition is bidirectionally
  equivalent to Mathlib's root `RiemannHypothesis`. `ExactTargetSurface.lean`
  contains this exact source-level weld. The current DASHI RH programme still
  reports the global theorem producer open.
- **Navier--Stokes:** `ExternalClayNS/LiteralABCD.lean` already contains literal
  C and D theorem terms via the released comparator proof and an independent
  semantic/physical bridge. `ExternalClayNS/LeanDojoTargetBridge.lean`
  isolates the remaining acceptance seam to the two statement equivalences
  `ClaySpec.ClayOptionC/D <-> LeanDojo FeffermanC/D`.
- **Birch--Swinnerton--Dyer:** LeanDojo itself proves the exact Taylor target
  equivalent to `Rank.Existence` plus finite Mordell--Weil rank.
  `ExactTargetSurface.lean` consumes the existing DASHI BSD core through
  `BSDLeanDojoSameObjectWeld` and delegates Taylor packaging to upstream. The
  current DASHI source still reports universal rank equality open.
- **P versus NP:** Agda already has the literal `SATNotInP -> PNotEqualsNP`
  Clay-core compiler and direct universal-SAT-failure producer shape. The
  universal lower-bound inhabitant remains the mathematical wall; exact
  machine-model transport to LeanDojo is a separate certification seam.
- **Hodge / Yang--Mills:** the pinned LeanDojo registry marks these statements
  incomplete, so they cannot be prize-acceptance targets. DASHI retains its
  stronger faithful internal programmes.
- **Poincare:** retained as a solved-target regression only.

## Verification states

`greenExact` means a theorem term has kernel-checked against the exact pinned
external proposition. `redType` is a carrier / statement-weld seam. `redMath`
means the statement cut is paid or sharply isolated but the current DASHI
sources still identify a genuine mathematical theorem as open.
`upstreamIncomplete` means the external statement itself is unsuitable as a
prize target.

`TerminalCensus.lean` records the strongest existing owners;
`ExternalTargetFrontier.lean` records these fail-closed states; `All.lean` is
the root-package typecheck/axiom-audit root; and `ExactTargetSurface.lean` is
the same-kernel probe for exact pinned statements plus DASHI donors.

Source-written code is never promoted to `greenExact` without the corresponding
kernel receipt.
