# RH Inverse-Square Shell Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the literal half-height inverse-square tail bookkeeping, connect it to the existing Route-A adverse budget, then push the branch to the exact width/curvature and compensation boundaries without asserting unpaid analysis.

**Architecture:** Add focused Lean owners for shell geometry, numerical shell summation, and the literal tail-to-budget compiler.  Existing `zetaWindowInverseSquareMass_*`, `threeTapInverseSquareZeroTailAfter`, `ThreeTapUniformCurvatureBound`, and compensation owners remain authoritative.  Update the frontier/workflow and mirror only status/provenance into Agda.

**Tech Stack:** Lean 4, Mathlib, Agda status mirror, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-10-03-rh-inverse-square-shell-max-cut-design.md`

## Global Constraints

- Keep negative ordinates on the literal all-real `Ncount` carrier.
- Do not manufacture a uniform witness-width or curvature constant.
- Do not assert a compensation floor without a source theorem.
- Mid-strip stays downstream of near-line PASS.
- Route B stays independent.
- Exact-head kernel success requires an exact-head workflow run.
- RH remains false/open.

## Review Focus

- Half-open endpoint ownership in left/right shells: every far zero is covered exactly once.
- The first shell at the `t/2` cutoff does not create a zero denominator or overlap.
- Negative ordinates use the existing local all-real zero-count theorem rather than reflection.
- The numerical series theorem has a genuinely summable majorant and the final scale is `log t / t`, not merely `log t`.
- Curvature multiplication uses a nonnegative uniform constant and the exact literal tail object.

---

### Task 1: Regression surface for shell max-cut

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapInverseSquareShellRegression.lean`
- Modify: `.github/workflows/rh-selected-three-tap-kernel.yml`

**Interfaces:**
- Consumes: new shell/series theorem names from Tasks 2–3.
- Produces: compile-time regression that fails until those owners exist and are exported.

- [ ] Add regression examples referring to the intended literal tail bound and Route-A compiler.
- [ ] Add the regression module to the selected-three-tap workflow.
- [ ] Verify the exact red head has a failing workflow because the production owners are absent.

### Task 2: Pure shell geometry and numerical series

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapInverseSquareShells.lean`

**Interfaces:**
- Consumes: real arithmetic and the existing unit-window shell estimates.
- Produces: left/right dyadic shell endpoint definitions, separation lemmas, and a numerical geometric/log summation bound reusable by the literal carrier.

- [ ] Define left/right distance shell endpoints at radius `2^k*(t/2)`.
- [ ] Prove shell separation and disjoint interval geometry.
- [ ] Prove the summability/closed upper bound for the geometric-log shell majorant.
- [ ] Build the module through the workflow.

### Task 3: Literal carrier shell partition and raw tail bound

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapInverseSquareTailBound.lean`

**Interfaces:**
- Consumes: `threeTapInverseSquareZeroTailAfter`, `zetaWindowInverseSquareMass_*`, Task 2 geometry/series.
- Produces: exact half-height raw inverse-square tail `O(log t/t)` on the literal complement carrier and a witness-independent `ThreeTapInverseSquareTailBound` witness.

- [ ] Partition the exact far subtype into left/right shell charts with no overlap.
- [ ] Bound each chart by the existing literal all-real unit/dyadic window owners.
- [ ] Sum the chart bounds using Task 2.
- [ ] Export `exists_threeTapInverseSquareTailBound` with an explicit nonnegative constant.
- [ ] Build and repair until green.

### Task 4: Route-A adverse asymptotic compiler

**Files:**
- Modify: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance.lean`

**Interfaces:**
- Consumes: `exists_threeTapInverseSquareTailBound`, existing finite `O(log t/t)` budget, `ThreeTapUniformCurvatureBound`.
- Produces: one theorem packaging finite+far adverse cost at `O(log t/t)` with the exact tail producer discharged.

- [ ] Instantiate the raw tail producer in the existing adverse-budget theorem.
- [ ] Keep curvature as the only witness-side premise.
- [ ] Add a compiler from a source compensation lower bound of matching scale to paid-cost negativity.
- [ ] Build through the workflow.

### Task 5: Width/curvature max-cut audit

**Files:**
- Create or modify the narrowest existing determinant/curvature owner(s) found by source audit.

**Interfaces:**
- Consumes: existing uniform pole-weight Lipschitz and determinant compiler target.
- Produces: either a proved fixed-width-to-curvature theorem or a smaller explicit analytic premise; never a fabricated uniform bound.

- [ ] Trace the witness-width quantifier through the determinant owner.
- [ ] Close any finite/bookkeeping lemmas that do not require new analysis.
- [ ] If the analytic width theorem remains, package it as the single exact premise feeding `ThreeTapUniformCurvatureBound`.
- [ ] Build affected modules.

### Task 6: Compensation-floor max-cut

**Files:**
- Modify or create the narrowest compensation owner.

**Interfaces:**
- Consumes: exact gamma+pole combination and local slack owners.
- Produces: normalized compensation comparison surface against the adverse `O(log t/t)` coefficient.

- [ ] Prove all algebraic normalization lemmas.
- [ ] Expose the strongest source-backed floor theorem available.
- [ ] If the floor remains analytic, leave one exact eventual inequality premise and compile it to Route-A PASS.
- [ ] Do not fill the mid-strip mesh unless near-line PASS is actually obtained.

### Task 7: Aggregate, workflow, Agda status mirror

**Files:**
- Modify: `Synthesis/RiemannSelectedRHMaxCutFrontier.lean`
- Modify: `Synthesis.lean`
- Modify: `.github/workflows/rh-selected-three-tap-kernel.yml`
- Modify the current RH status/provenance module on Agda PR #1082.

**Interfaces:**
- Consumes: Tasks 2–6.
- Produces: exact live frontier and cross-language status.

- [ ] Import/export all new Lean modules.
- [ ] Update the frontier prose to paid/open boundaries actually present in source.
- [ ] Update Agda booleans/provenance without inventing real analysis.
- [ ] Check exact-head workflows on both PRs and report kernel status precisely.
