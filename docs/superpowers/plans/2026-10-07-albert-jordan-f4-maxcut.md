# Albert Jordan / F4 Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the paid E6 minuscule-27 recognition into an honest Albert-algebra construction boundary, with an external H3(O) donor pin, native scalar/traceless mathematics, a typed Jordan-automorphism/F4 stabilizer target, and separate ternary/E8 promotion gates.

**Architecture:** Keep Cobord/JordanAlgebra as an immutable external proof artifact in its own Lean 4.31 package graph. Prove generic scalar/traceless and automorphism lemmas natively in DASHI Lean 4.35. Connect the paid finite E6 minuscule carrier only to weight-line interfaces; do not identify a 27-element orbit with the 27-dimensional algebra itself.

**Tech Stack:** Lean 4 / Mathlib, Git submodule, GitHub Actions, Python source-surface audit.

**Spec:** user-approved max-cut in conversation, October 7 2026.

## Global Constraints

- Preserve external authorship and do not copy unlicensed donor source into DASHI.
- Keep Lean 4.31 donor and Lean 4.35 DASHI package graphs separate until an explicit compatibility port is verified.
- `27 weights` is not `27-dimensional vector space`; recognition targets one-dimensional weight lines.
- `Aut_Jordan(J) ≅ F4` and `Stab_E6(1) ≅ F4` remain explicit proof obligations until supplied.
- Full ternary-240/E8 recognition remains independent of the Albert/F4 lane.

## Review Focus

- Donor source changes must fail the source-surface audit rather than silently retargeting names.
- Trace/unit normalization must be exactly `trace(1)=3`; scalar projection uses `trace(x)/3`.
- Traceless projection must have trace zero and reconstruct every input exactly.
- Jordan/F4 interfaces must require product/unit preservation and not infer group identity from dimension 52.
- Weight-line realization must remain separate from finite minuscule carrier equality and from full ternary-240 recognition.

---

### Task 1: Pin and audit external Albert donor

**Files:** `.gitmodules`, `vendor/JordanAlgebra`, `vendor/JordanAlgebra.VENDOR`, `scripts/audit_albert_external.py`, `.github/workflows/albert-jordan-f4.yml`

**Interfaces:** Produces exact donor SHA/toolchain/source-surface receipt without importing it into the DASHI kernel.

- [ ] Pin `Cobord/JordanAlgebra` at `a4b0d58554732ced63b4217200baa56be5a2c3d5` as a gitlink.
- [ ] Audit `AlbertAlgebra`, `albertEquiv`, `ofAlbert`, `trace`, `det`, and `detTrace` at the exact pin.
- [ ] Build the donor under its own Lean 4.31 environment in CI.
- [ ] Build DASHI Albert adapter files under the root 4.35 environment separately.

### Task 2: Native scalar/traceless decomposition

**Files:** `Integration/AlbertScalarTraceless.lean`, `Integration/AlbertScalarTracelessRegression.lean`

**Produces:** `TraceUnitData`, scalar/traceless projections, trace-zero theorem, reconstruction theorem, and a linear equivalence `J ≃ₗ[ℝ] ℝ × ker(trace)`.

- [ ] Regress `trace(unit)=3` normalization and reconstruction.
- [ ] Implement scalar coefficient `trace(x)/3` and traceless part `x - (trace(x)/3) • unit`.
- [ ] Prove trace-zero and two-sided scalar/traceless equivalence.

### Task 3: Albert/Jordan automorphism and F4 target

**Files:** `Integration/AlbertJordanAutomorphism.lean`, `Integration/AlbertJordanAutomorphismRegression.lean`

**Produces:** abstract `AlbertStructure`, product/unit/trace/cubic-preserving `JordanAutomorphism`, traceless preservation theorem, and `E6F4StabilizerRecognition` target interface.

- [ ] Require Jordan commutativity/identity/unit and cubic normalization explicitly.
- [ ] Define automorphisms structurally; dimension 52 is not an identification criterion.
- [ ] Prove any trace-preserving automorphism maps `ker(trace)` to itself.
- [ ] Type `F4 ≅ Aut_Jordan(J) ≅ Stab_E6(1)` only as an unpaid recognition record.

### Task 4: Minuscule weight-line and ternary transport seam

**Files:** `Integration/AlbertMinusculeWeightLines.lean`, `Integration/AlbertMinusculeWeightLinesRegression.lean`

**Consumes:** `Integration.E6Minuscule27SameObject`.

**Produces:** `MinusculeWeightLineRecognition` mapping `Omega5Weight` to one-dimensional subspaces of `J`, with distinctness/action/relation obligations.

- [ ] Keep `Omega5Weight` finite carrier separate from `J`.
- [ ] Require each image to be one-dimensional.
- [ ] Require E6 reflection/action intertwining and Schlaefli relation preservation.
- [ ] Type a later ternary `1+26` weld as a separate transport receipt, not a consequence of cardinality.

### Task 5: Albert/F4/E8 capstone

**Files:** `Integration/AlbertF4ExceptionalCapstone.lean`, `Integration/AlbertF4ExceptionalCapstoneRegression.lean`, `Integration/GeometricReasoningEverything.lean`

**Produces:** authoritative frontier ledger distinguishing external donor paid, native decomposition paid, minuscule representation paid, and open Albert/F4/full-E8 promotions.

- [ ] Import the paid E6 minuscule same-object result.
- [ ] Record external donor source surface as externally paid but root-kernel compatibility pending.
- [ ] Keep actual donor instantiation, continuous E6 action, F4 identification, and full ternary-240 recognition independently open.
- [ ] Update rollup and focused workflow.
