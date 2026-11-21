# Alpöge/Claude RH source-admission sidecar (21 November 2026)

**Status:** P0 fork-pinned source dependency and Lean admission adapters committed, **not executed**; no CI. The original full proof is available through the user's existing fork and is consumed by immutable Git reference, not recopied into DASHI. This directory contains only DASHI-authored integration code, lock data and a local checkout script.

## Provenance and exactly what is paid

Original announcement: https://alpo.ge/remark.pdf (20 Nov 2026).
**User-selected source fork:** https://github.com/chboishabba/riemann-hypothesis-lean at pinned commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` (exact `src/Main.lean` Git blob `dbd5db70bc11b35f18fa5751216ab335321e7bfc`, verified against Deicyde's checking mirror). Independent verification comparator mirror: https://github.com/Deicyde/riemann-hypothesis .
Independent verification: https://math.mit.edu/~drew/grh/ (20 Nov 22:05 UTC).

Source archive: 14-part `lean.tar.gz`, **239275554 bytes**, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
Lean/Mathlib: **v4.33.1**; original mirror `Main.lean` blob `dbd5db70bc11b35f18fa5751216ab335321e7bfc`; independent challenge blob `9677ace64b3a5e8b1a571d82d52ee13c53b08026`.
Exported challenge sha256 `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`.
Exported solution sha256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e` (**uncompressed**).
Independent MIT audit reports 175187 modules compile and kernel replay; con-leche, nanoda and lean4lean accept, and independent challenge statement comparison accepts all five. Additional checks were underway at that audit timestamp; **not a DASHI-local acceptance**.

## Git dependency: fork is the intended vendor source

User has already forked the 175,187-file original source into `chboishabba/riemann-hypothesis-lean`. **Do not request a second archive or rewrite theorems.** `fork_pin.json` stores the immutable Git commit, two selected blob hashes, exact mathlib SHA and Lean v4.33.1. `checkout_fork_source.sh` clones/checks out the user's fork at that commit into `dashi_lean4/.local/alpoge-rh-v4331`, checks source identity and stops before any checker. This is an external Git dependency, not copied code or a same-version proof import.

Local opt-in:
```sh
bash proofs/alpoge-lean433/checkout_fork_source.sh
# In the pinned source checkout (separate from root):
cd .local/alpoge-rh-v4331
lake exe cache get
lake build Main
lake env lean ../../proofs/alpoge-lean433/RHAdmission.lean
```

The proof source reportedly has no explicit redistribution license. The user's fork already exists; **reference it, preserving attribution and source identity, without copying its 1.03 GB contents into another public repo**. A fork does not create a license grant, so any further publication or redistribution decisions must respect the author's rights. This does not block source reading and local use where authorized.

## Current P0 priority — minimal top-cut, not full proof-tree reconstruction

A direct fork source readback at pinned commit `7cbf7a0c` found:
`src/Main.lean` imports `Statements` and `Supplements.Kernels.MainTheoremsAll`;
`src/Supplements/Kernels/MainTheoremsAll.lean` imports `MainTheoremsCritical` and `...SmallClassNumbers.CorGKOf`; the core five theorem names are already defined in `src/Supplements/Kernels/MainTheorems.lean`.

**New `RHTopCut.lean` imports ONLY `Statements` and `Supplements.Kernels.MainTheorems`**, and constructs all five original theorem statements directly from `rhOfAll`, `allChi`, `claimAll`, and `critAll`. This is the **shallowest confirmed top-level source cut**; it prunes the explicit `MainTheoremsAll` / `MainTheoremsCritical` / `CorGKOf` wrapper imports. It does **not** prove that the transitive Lean dependency closure of `MainTheorems` is small. Count/measure only if running the opt-in local build.

The **next local check** (not executed here) is `lake build Supplements.Kernels.MainTheorems` on the fork's pinned Lean 4.33.1, followed by `lake env lean <DASHI-root>/proofs/alpoge-lean433/RHTopCut.lean`. The `Main` target may include unrelated downstream modules; do not insist on it when the goal is only importing these five theorems. Compare the source-pinned original `Main.lean` challenge names and the authored `RHTopCut` declarations with a checked type and axiom receipt before promoting.

The terminal **BIDI** into Clay is already available in the independent DASHI Lean root (`MillenniumExternal.ExactTargetSurface.clayRiemannHypothesis_iff_mathlib`), but its v4.35.0-rc3 root is not binary compatible with v4.33.1. Prefer a source-coherent Clay adapter compiled *inside* the v4.33.1 fork if the original pinned Clay definitions can be made available there; otherwise build a genuine typed version translation. A path, file hash or compiled stale olean is not proof transport.

**P1** starts from original theta/automorphic and G2/369 source functions only after this P0 cut. Compare exact operator/domain/action signatures before replacing proof steps; the goal is to *improve* the original proof using geometry, not reproduce the author's 175,187-file proof or synthesize a new dummy positivity target. No world/PG ingestion in the active maximum-cut.

## P0 source-local handoff

The original source tree provides `Main.lean` with exactly:
- `riemannHypothesis : RiemannHypothesis`
- `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`
- `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`
- `LFunction_eq_zero_re : DirichletLZerosOnLine`
- `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`

DASHI's separately authored `RHAdmission.lean` imports **actual** `Main` and exposes these five unchanged statements as typed handoffs. This adapter is NOT compiled here because the fork checkout and the pinned Lean toolchain are not available in this tool environment; current DASHI Lean root uses **Lean 4.35.0-rc3**, while the fork uses **4.33.1**. Neither source identity nor a clone alone transports a proof across those environments. Do not use `sorry`/axioms or swap a similarly named declaration.

The already existing `MillenniumExternal/ExactTargetSurface.lean` in DASHI's root proves:
`Millennium.ClayRiemannHypothesis ↔ Mathlib.RiemannHypothesis`.
The new `MillenniumExternal/AlpogeRHBoundaryExact.lean` directly consumes that **existing BIDI**, with exact forward and reverse terms. It does not replace a theorem or construct a fake external proof.

### Exact remaining version + source weld

1. Use the already-forked source via `checkout_fork_source.sh`; pin Git commit, Main/Statements Git blobs, Mathlib commit and toolchain. The author archive digest is an additional provenance check if original tarball is obtained separately.
2. Build only locally and isolate from DASHI's older-root Lean/Mathlib; **no CI**, no mixed-olean imports.
3. Establish a trusted cross-version theorem transfer or migrate original DASHI Clay BIDI target to 4.33.1 with matched Mathlib definitions. A printed statement or SHA hash is **not** a proof-transfer mechanism.
4. Import `DASHI.AlpogeRH.original_mathlib_rh` as an actual theorem in the **same** environment as `Millennium.ClayRiemannHypothesis.of_mathlib`.
5. Compile exact endpoint, inspect axioms, make explicit chain receipt and transport into Agda's literal `RiemannHypothesisFor` original analytic substrate without assuming `ExternalRHGeometricTransport` is inhabited.
6. Retain original Weil positivity/geometry mechanism as independent P1 and do not reopen 50/77 signed-moment RH producers just to reprove zero-location.

## Steelman / BIDI / reverse solve ownership

Forward: external original Main RH → the same Mathlib RH → pinned `clayRiemannHypothesis_of_mathlib` → Clay proposition.

Reverse: existing pinned Clay proposition → `mathlibRiemannHypothesis_of_clay`. This is an **actual equivalence already existing** on DASHI root, so the only missing external endpoint work is **source admission across toolchains and coherent kernel proof**, not new RH mathematics.

The original announcement says its technique includes Stepanov, Fourier analysis, theta lifts (length about `sqrt X`), multiplicity and a signature `qN = Mk + R`; these are *research direction clues*, not verified internal proof dependency edges until the source graph is inspected.

No source duplication; no CI; no kernel success claimed.
