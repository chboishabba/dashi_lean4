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


## 2026-10-24 native Hamiltonian proof and cross-prover attribution

New proof source `Integration/RationalAlbertJordanHamiltonianSymmetry.lean` imports and REUSES the existing `RationalAlbertNative` literal rational octonionic Jordan product/unit and `RationalAlbertS3Native` genuine order-three Albert product automorphism. On this exact same product it proves `f∘L_h=L_h∘f ↔ f(h)=h` for the actual cyclic actor, with the generic right-unit argument; for native `h=diag(1,0,-1)`, `tr(h)=0`, `h≠0`, `L_h(1)=h` and `cycleA h ≠ h`, hence `L_h` does NOT commute with the source-proved order-three Jordan symmetry. This is an actual source-specific operator obstruction, not a new F4 classifier, a spatial Cube27 basis action or Monster VOA mode. Older `AlbertScalarTraceless` and `TernaryAlbertLinearBasisWeld` already construct the linear 1+26 transport; it is not an algebra intertwiner.

Full local exact Cayley–Dickson/Albert Python (previous already supplied by the original 27−1 programme, now freshly rerun) PASS verifies Jordan spectrum `{-1:1,-1/2:8,0:9,1/2:8,1:1}` and tracefree compression `{−1/√3:1,−1/2:8,0:8,1/2:8,1/√3:1}`. Distinguish the separate open cube path graph 54 edges, F3³ periodic torus 81 edges, complete 351-edge affine-invariant graph, and the actual Jordan L_h.

The other living cross-prover owners (NOT merged local Lean theorem terms) are Agda #1249 exact 26-dimensional **constant-mode-removed path Laplacian**, whose operator is A=D+1*bᵀ with Gram metric G=I−J/27, NOT site-origin-deleted Dirichlet D; Lean #84 handoff and #80 TOE. Do not identify site-origin delta with the actual Jordan unit or the constant Fourier vector. This Lean source is COMMITTED but **Lean/Lake exact-head kernel unverified**, since no Lean executable is available in the current runtime.


### Native S3-equivariance exact local matrix receipt

The separate local Python script `/mnt/data/check_lean_native_albert_s3_hamiltonian.py` and committed `scripts/check_native_albert_s3_hamiltonian.py` calculate the full 27×27 *exact rational matrix shadow* of the native selected `h=diag(1,0,-1)` left-Jordan Hamiltonian and the actual order-three `cycleA` slot permutation from `RationalAlbertS3Native`. They verify `cycleA^3=1`, orthogonal slot permutation, conjugate Hamiltonian isospectral, but commutator `P L_h − L_h P` has **full rank 27** and squared Frobenius norm **18**; the native trace-form amplitude `<L_h(1),h>` equals **2**. Eigenvalues remain {−1:1,−1/2:8,0:9,1/2:8,1:1}. Adding a scalar energy shift to make this finite matrix positive semidefinite does not eliminate its noncommutativity.

The actual Lean source now includes `cycle_conjugates_leftJordan`, `cycle_commutes_iff_fixed`, `selectedH_does_not_commute_with_cycle`, `selectedH_tracePair_norm`, and `selectedH_scalar_traceless_amplitude`. These genuinely reuse the same native octonionic product, native trace pair and existing Albert S3 automorphism. They are SOURCE-WRITTEN; no Lean/Lake executable in local environment. **Build risk:** repository `lean-toolchain` is `v4.35.0-rc3` but `lakefile.toml` pins mathlib `v4.28.0`; reconcile actual toolchain/manifest compatibility before claiming kernel-green. Do not change dependency pins blindly on this multi-project branch.


## 2026-10-24 primary Griess1990 homogeneous basis now executed

The prior remaining homogeneous-product acquisition has moved: `docs/superpowers/plans/2026-10-24-griess1990-albert-homogeneous-jordan-maxcut.md` is the canonical source-specific cut. Griess 1990's original complex Albert construction has `A=F3³` and explicit source coefficient `(-2)^(-c(x,y))ω^g(x,y)`. Full standalone local Python `/mnt/data/check_griess1990_albert_homogeneous_exact.py` executed PASS for 729 nonzero products, all 19,683 invariant bilinear triples, and all 98,658 polarised Jordan polynomial monomials. It computes a nonzero original-source homogeneous cubic (-1/2) and genuine nonassociativity (-1/2 versus +1/4). Every nonzero homogeneous left-multiplication L_(e_a) has cubic-cycle polynomial `(t³−1)(t³+1/8)^8` and NONREAL spectral pairs, so it is NOT a positive-Hilbert selfadjoint Hamiltonian without a new chosen real/Hermitian operator.

This is an executable **reproduction** of the original Griess theorem, not a new theorem attribution or Lean kernel proof. The new repo `scripts/check_griess1990_albert_f3cubed_homogeneous_product.py` matches the full exact test algorithm but the GitHub byte has not separately been replayed. The outstanding mathematical same-object debt is an explicit Q(ω)-scalar extension, cubic/trace/product isomorphism to `RationalAlbertNative` (which is defined over Q), not additional 27=1+26 counting or generic F4 dimension diagnostics. Distinguish the unrelated 196884 Monster Griess VOA and Agda #1249 26-dimensional spatial zero-mean path Laplacian. Source-native Lean/Lake exact-head proof remains not run.
