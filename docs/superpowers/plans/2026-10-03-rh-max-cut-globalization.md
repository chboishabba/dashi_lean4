# RH Max-Cut Globalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Reduce the remaining one-scale RH lane to its exact signed reflection-tail inequality, add conditional displacement globalization, formalize the two-scale promotion trigger, and package the independent signed-fifth route.

**Architecture:** Add four focused Lean modules consuming existing owners; no existing analytic carrier is redefined. Each module exposes a theorem boundary whose unpaid premise is the actual remaining analytic statement.

**Tech Stack:** Lean 4, Mathlib, existing `Synthesis` and `Zeta23Bridge` modules.

**Spec:** `docs/superpowers/specs/2026-10-03-rh-max-cut-globalization-design.md`

## Global Constraints

- No unsourced sign transfer between unshifted and transformed detectors.
- No general `J4` work before actual smooth `J2 = 0`.
- No claim that near-line positivity alone proves RH.
- Two-scale promotion reuses the existing source and does not invent a completed two-scale margin.
- Signed-fifth remains independent.
- Kernel-green claims require an exact-head workflow run.

## Review Focus

- Endpoint split at `a = delta`: the globalization theorem must cover equality exactly once.
- `delta > 1/2`: the interval glue must still be logically sound.
- Multiplicity is explicit and no positivity is silently assumed where not required.
- Two-scale promotion uses only `t >= 300` source theorems.
- FarExact rewrite keeps the `1/2` reflection-pair factor and subtracts `LocalExact` with the correct sign.

---

### Task 1: Reflection-tail paid-cost cut

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapFarExactCut.lean`

**Interfaces:**
- Consumes: `threeTap_offOrd_eq_half_adaptivePair_tsum`, `threeTapAdaptiveFarExact`, `threeTapResonanceCompensation`.
- Produces: exact FarExact half-tsum normal form and equivalent PASS/FAIL inequalities.

- [ ] State the exact FarExact normal-form theorem.
- [ ] Prove it by unfolding `threeTapAdaptiveFarExact` and rewriting the off-ordinate weld.
- [ ] Add equivalent paid-cost PASS/FAIL/balanced comparisons in the reflection-tail coordinate.
- [ ] Build the module with `lake build Synthesis.RiemannSelectedPrimeSensitiveThreeTapFarExactCut` when a Lean runner is available.

### Task 2: Displacement globalization consumer

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveThreeTapGlobalize.lean`

**Interfaces:**
- Consumes: `threeTapAdaptiveTerminalProfile` and near-line band conclusions.
- Produces: full `0 < a <= 1/2` positivity from near-line plus mid-strip positivity; uniform-margin mid-strip compiler.

- [ ] Define `ThreeTapAllOffLineDisplacementsPositive`.
- [ ] Prove interval gluing from `(0,delta)` and `[delta,1/2]`.
- [ ] Prove the uniform positive mid-strip-margin compiler.
- [ ] Add a direct resonance PASS globalization theorem consuming the existing `FarExact < -compensation` near-line result plus the mid-strip premise.
- [ ] Build the module when a Lean runner is available.

### Task 3: One-scale fail and two-scale promotion

**Files:**
- Create: `Synthesis/RiemannSelectedPrimeSensitiveTwoScalePromotion.lean`

**Interfaces:**
- Consumes: strict one-scale near-line fail compilers and `quarticFourPhysicalDetector_twoScale_samples`.
- Produces: named `ThreeTapNearLineFails` proposition and a promotion theorem exposing independent prime-2/prime-3 samples for both selected endpoint detectors.

- [ ] Define the failure proposition.
- [ ] Compile strict paid-cost failure and balanced positive-J2 failure into it.
- [ ] Package existing two-scale sample isolation for both selected endpoint detectors at `t >= 300`.
- [ ] State the promotion theorem as a conjunction of one-scale failure and available two-scale source data, without claiming completed positivity.
- [ ] Build the module when a Lean runner is available.

### Task 4: Signed-fifth hypothesis package

**Files:**
- Create: `Synthesis/RiemannSelectedSignedFifthMaxCut.lean`

**Interfaces:**
- Consumes: `signedFifthCap_eventual_compiles_terminalMargin`.
- Produces: one named analytic hypothesis structure/Prop and a single compiler to `CanonicalTerminalPositive`.

- [ ] Define `SignedFifthAnalyticInput` containing epsilon positivity, eventual boundary bound, eventual signed interior lower bound, and outer-terminal convergence.
- [ ] Prove the input compiles to `CanonicalTerminalPositive`.
- [ ] Build the module when a Lean runner is available.

### Task 5: Aggregate and workflow

**Files:**
- Create: `Synthesis/RiemannSelectedRHMaxCutFrontier.lean`
- Modify: `Synthesis.lean`
- Modify: `.github/workflows/rh-selected-three-tap-kernel.yml`

**Interfaces:**
- Consumes: Tasks 1–4.
- Produces: one import boundary documenting the exact remaining analytic obligations.

- [ ] Add the four new modules to a frontier aggregate.
- [ ] Export the aggregate from `Synthesis.lean`.
- [ ] Add all new Lean modules to the RH selected-three-tap workflow build list.
- [ ] Verify exact-head workflow status; do not claim kernel success without a passing run.
