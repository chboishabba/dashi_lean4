# Millennium External Target Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the pinned LeanDojo Millennium repository an independent acceptance/audit surface for the existing DASHI Millennium terminal constructors.

**Architecture:** Materialise and verify the exact upstream source in isolation, keep its package graph/toolchain separate from DASHI, and add a DASHI-side typed terminal census plus aggregate axiom audit. Direct cross-project adapters are added only where the exact upstream target can be compiled under a compatible environment; incomplete upstream statements remain explicitly non-prize targets.

**Tech Stack:** Lean 4, Lake, GitHub Actions, shell, Python 3.

**Spec:** `docs/superpowers/specs/2026-10-06-millennium-external-targets-design.md`

## Global Constraints

- Pin upstream exactly at `603053dc267cf3efe422f438eb78098c0ececd6f`.
- Preserve upstream Apache-2.0 attribution.
- Do not alter upstream theorem statements to fit DASHI.
- Do not change DASHI's toolchain/mathlib pin as part of this integration.
- Hodge and Yang--Mills upstream `statement_incomplete` entries are audits, not valid prize targets.
- No adapter may manufacture mathematical hypotheses.

## Review Focus

- Wrong upstream commit must fail before any target audit runs.
- A registry target renamed or reclassified upstream must fail the audit visibly.
- Missing DASHI terminal module must fail the DASHI aggregate typecheck.
- A `sorry`/axiom accidentally entering an adapter must be visible in the final axiom printout.
- Upstream-incomplete Hodge/YM must never be reported as GREEN prize closure.

---

### Task 1: Pinned vendor materialisation and provenance

**Files:**
- Create: `vendor/LeanMillenniumPrizeProblems.VENDOR`
- Create: `scripts/vendor_millennium_targets.sh`

**Interfaces:**
- Produces: exact source tree at `vendor/LeanMillenniumPrizeProblems` with verified HEAD.

- [ ] Write the pin/provenance manifest.
- [ ] Write fail-closed materialisation script.
- [ ] Verify wrong/moved HEAD is rejected.
- [ ] Commit.

### Task 2: Upstream registry acceptance audit

**Files:**
- Create: `scripts/audit_millennium_external_targets.py`

**Interfaces:**
- Consumes: materialised `Problems/Registry.lean`.
- Produces: deterministic audit failure if declaration names/status classifications drift.

- [ ] Encode the seven registry entries and active target expectations.
- [ ] Require Hodge/YM `statement_incomplete` at the pinned revision.
- [ ] Run syntax/audit checks.
- [ ] Commit.

### Task 3: DASHI terminal-constructor census

**Files:**
- Create: `MillenniumExternal/TerminalCensus.lean`
- Create: `MillenniumExternal/All.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Consumes: existing RH/NS/YM/BSD/Hodge/P-vs-NP terminal modules.
- Produces: opt-in `MillenniumExternal` Lean library and aggregate root.

- [ ] Import the strongest current terminal modules without redefining problem statements.
- [ ] Add typed aliases/checks for existing terminal proposition/constructor surfaces where stable names exist.
- [ ] Add aggregate imports and `#print axioms` for terminal constructors.
- [ ] Register opt-in library in Lake.
- [ ] Commit.

### Task 4: Independent two-environment CI

**Files:**
- Create: `.github/workflows/millennium-external-targets.yml`

**Interfaces:**
- Consumes: Tasks 1--3.
- Produces: upstream-native build/audit and DASHI-native terminal aggregate build.

- [ ] Checkout exact upstream pin into vendor path.
- [ ] Build upstream under its own checked-in toolchain/package graph.
- [ ] Run registry audit.
- [ ] Build `MillenniumExternal.All` under DASHI toolchain.
- [ ] Upload logs on failure/success.
- [ ] Commit.

### Task 5: Exact-target adapter frontier receipt

**Files:**
- Create: `MillenniumExternal/ExternalTargetFrontier.lean`
- Modify: `MillenniumExternal/All.lean`

**Interfaces:**
- Produces: fail-closed classification separating exact adapters, representation/toolchain mismatches, mathematical gaps, and upstream-incomplete statements.

- [ ] Encode only evidence backed by imports/build status, not aspirational booleans.
- [ ] Mark Hodge/YM as upstream-incomplete at this pin.
- [ ] Record exact upstream declaration strings for RH/NS/BSD/P-vs-NP.
- [ ] Keep direct-adapter status false unless an exact theorem term exists.
- [ ] Commit.

### Task 6: Verification and PR

**Files:** none beyond prior tasks.

- [ ] Run static source audit for forbidden `sorry`/`axiom` in new Lean adapters.
- [ ] Inspect branch diff against `main` for unrelated changes.
- [ ] Open PR with exact pin, architecture, and kernel-verification boundary.
