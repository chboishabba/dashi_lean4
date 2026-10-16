# Millennium Submission Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the external-target audit in PR #45 into the shortest exact acceptance path, beginning with an unconditional LeanDojo Navier–Stokes C theorem if the existing released comparator proof can be transported without new fluid estimates.

**Architecture:** Keep PR #45's pinned upstream source and same-kernel audit as the acceptance root. For NS, bypass the opaque `ClayOptionC ↔ FeffermanC` wrapper and transport the already-proved comparator C witness directly into LeanDojo's literal `NavierStokesOnR3.Breakdown`; factor any failed transport into theorem-bearing clause lemmas rather than a fresh Millennium assumption. Update the global frontier only from kernel-checkable theorem surfaces.

**Tech Stack:** Lean 4, Mathlib, pinned OpenAI `NavierStokesAndEuler`, pinned LeanDojo `LeanMillenniumPrizeProblems`, Python 3 source regressions, GitHub Actions.

**Spec:** Approved in-chat roadmap on 2026-10-07; PR #45 is the authoritative acceptance design.

## Global Constraints

- Preserve LeanDojo pin `603053dc267cf3efe422f438eb78098c0ececd6f`.
- Preserve OpenAI NS proof pin `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- Do not weaken or restate LeanDojo targets.
- Do not add a new mathematical hypothesis to obtain an external theorem.
- One literal Fefferman alternative is sufficient; target C first and treat D as redundant audit coverage.
- `GREEN` requires an unconditional theorem term against the exact pinned proposition plus axiom audit.

## Review Focus

- Pair-spacetime versus time-first `Fin 4` coordinate order must not be silently identified.
- Initial divergence definitions must be proved equal, not inferred from notation.
- Derivative-decay transport must account for comparator operator-norm derivatives versus LeanDojo coordinate derivatives.
- A LeanDojo global smooth finite-energy solution must genuinely induce the comparator solution needed for contradiction.
- Frontier status must remain fail-closed if any adapter theorem is conditional.

---

### Task 1: RED source regression for unconditional NS C acceptance

**Files:**
- Create: `scripts/test_millennium_submission_surface.py`
- Modify: `.github/workflows/millennium-external-targets.yml`

**Interfaces:**
- Produces: a regression requiring an unconditional `leanDojoFeffermanC` theorem and forbidding promotion from the conditional `LeanDojoCDStatementWeld` route.

- [ ] Add source regression that fails on the current conditional bridge.
- [ ] Add it to the external-target workflow.
- [ ] Observe RED in exact-head CI.

### Task 2: Direct comparator-to-LeanDojo C max-cut

**Files:**
- Create: `ExternalClayNS/LeanDojoCComparatorBridge.lean`
- Modify: `ExternalClayNS/lakefile.toml`
- Modify: `.github/workflows/millennium-external-targets.yml`

**Interfaces:**
- Consumes: `SemanticGapAdapter.openAIComparatorOptionC` / comparator C theorem and exact LeanDojo `NavierStokesOnR3.Breakdown`.
- Produces: either unconditional `leanDojoFeffermanC` or the smallest theorem-bearing transport frontier with no opaque statement-level equivalence assumption.

- [ ] Prove coordinate carrier pack/unpack lemmas required by the transport.
- [ ] Prove comparator initial-data clauses imply LeanDojo condition (4) and divergence-free initial data.
- [ ] Prove comparator force clauses imply LeanDojo condition (5) on the packed spacetime field.
- [ ] Prove any LeanDojo global smooth finite-energy solution induces the comparator solution used by the released contradiction.
- [ ] Compose the released comparator C theorem into exact `MillenniumNavierStokes.FeffermanC`.
- [ ] Print axioms for the final theorem.

### Task 3: Acceptance frontier promotion or narrowed wall

**Files:**
- Modify: `MillenniumExternal/ExternalTargetFrontier.lean`
- Modify: `MillenniumExternal/STATUS.md`
- Modify: `MillenniumExternal/All.lean` if an unconditional theorem is available in the root package.

**Interfaces:**
- Consumes: Task 2 kernel result.
- Produces: `greenExact` only on unconditional exact theorem; otherwise a precise clause-level `redType`/`redMath` note.

- [ ] Promote NS only if the exact target theorem kernel-checks.
- [ ] Otherwise record the exact surviving transport theorem(s), with no new wrapper assumption.
- [ ] Keep RH/BSD/P-vs-NP/Hodge/YM classifications unchanged unless this tranche proves more.

### Task 4: Verification and stacked PR

**Files:** no additional production files.

- [ ] Run source regressions and exact-target workflow.
- [ ] Inspect all `#print axioms` outputs for unexpected axioms.
- [ ] Open a stacked PR against `agent/millennium-external-target-adapters-20261006` with exact verification boundary.
