# Alpöge/Claude RH source-admission sidecar (21 November 2026)

**Status:** P0 admission source adapter committed, **not executed**; no CI. This directory does **not** contain the original author's unlicensed proof source, nor copied challenge proofs. It is an integration recipe and DASHI-authored adapter.

## Provenance and exactly what is paid

Original announcement: https://alpo.ge/remark.pdf (20 Nov 2026).
Byte-exact verification mirror: https://github.com/Deicyde/riemann-hypothesis .
Independent verification: https://math.mit.edu/~drew/grh/ (20 Nov 22:05 UTC).

Source archive: 14-part `lean.tar.gz`, **239275554 bytes**, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
Lean/Mathlib: **v4.33.1**; original mirror `Main.lean` blob `dbd5db70bc11b35f18fa5751216ab335321e7bfc`; independent challenge blob `9677ace64b3a5e8b1a571d82d52ee13c53b08026`.
Exported challenge sha256 `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`.
Exported solution sha256 `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e` (**uncompressed**).
Independent MIT audit reports 175187 modules compile and kernel replay; con-leche, nanoda and lean4lean accept, and independent challenge statement comparison accepts all five. Additional checks were underway at that audit timestamp; **not a DASHI-local acceptance**.

## License constraint

The mirror explicitly says the 175187-module source submission **was published without a license**. Consequently copying it into the public DASHI repository as vendored source is blocked pending author's redistribution permission or an applicable license. Do not silently treat public GitHub visibility as permission to republish. Obtain the archive individually from the original author for local verification, preserve hashes and attribution, and keep it outside version control.

## P0 source-local handoff

The original source tree provides `Main.lean` with exactly:
- `riemannHypothesis : RiemannHypothesis`
- `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`
- `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`
- `LFunction_eq_zero_re : DirichletLZerosOnLine`
- `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`

DASHI's separately authored `RHAdmission.lean` imports **actual** `Main` and exposes these five unchanged statements as typed handoffs. This adapter is NOT compiled here because the 1.03 GB external source package is not materialized and the current DASHI Lean root's Mathlib pin differs. Do not use `sorry`/axioms or swap a similarly named declaration.

The already existing `MillenniumExternal/ExactTargetSurface.lean` in DASHI's root proves:
`Millennium.ClayRiemannHypothesis ↔ Mathlib.RiemannHypothesis`.
The new `MillenniumExternal/AlpogeRHBoundaryExact.lean` directly consumes that **existing BIDI**, with exact forward and reverse terms. It does not replace a theorem or construct a fake external proof.

### Exact remaining version + source weld

1. Individually acquire original source, verify archive sha256 and the precise five statement types in clean Lean 4.33.1.
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
