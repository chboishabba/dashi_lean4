## 21 November 2026 — P0 weld-forward: single ORIGINAL EveryCharacter source, all five terminals

The newest direct source lemma in `RHGRHP0DirectionalSourceCut.lean` is
`all_original_grh_and_rh_endpoints_from_galois_row`.
It combines the **existing original** Galois RowSrc `every_character_of_original_galois_row`
with the actual `DirichletLNonvanishingRightOfHalf`,
`DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine`,
Mathlib `RiemannHypothesis` and original `Claim.Zeta` consumers
in ONE proof term. None of its inputs are a new fake character, toy L-series,
Mellin carrier, or extra axiom. The Lean v4.33.1 external-adapter source
is **uncompiled locally**, while the independent full ORIGINAL author's
`Main.lean` formal proof has been checked separately.

External verification as of MIT 20 Nov 2026 22:05 UTC:
https://math.mit.edu/~drew/grh/ reports all 175,187 original modules
compile, full leanchecker module replay, five theorem axiom audit using only
`propext`, `Classical.choice` and `Quot.sound`, independent nanoda,
con-leche and lean4lean acceptance, and con-leche comparison of the
five challenge statements. The full lake comparator run and a few
export-replay checks remained running at that snapshot.
https://github.com/aapolipponen/rh-lean-check-lumi independently
reports sandboxed original compilation and identical `Main.olean` hash,
but its own audit was marked ongoing when last checked.

**Already-owned Mellin**: Agda `MellinSplitFunctionalEquationExact` and
`RiemannG2GammaMellinProofRelevantActionCompilerExact`; original
BSD E32 `EllipticCMLevel32FrickeMellinExact`. Do not rebuild these.
Their original analytic realization differs from the external
all-Dirichlet `UpperTheory.EveryCharacter` theorem: the exact
per-character Dirichlet L(s,chi) and zero-predicate identification
is not supplied by importing an existing Mellin split.

**Current P0 real gate** is permission-compatible local checkout/pin of the
existing original fork, v4.33.1 adapter kernel/axiom receipt, the root
Mathlib version-compatible proof handoff, and an Agda all-character
same-analytic-object bridge. The Agda #1533
`AlpogeRHOriginalClayEndpointBidiExact.originalClayWitnessToAnalyticRH`
is a valid source-written projection back from the *actual* Clay RH
record, but is not a reverse ordinary-RH-to-GRH theorem.
No universal automorphic/Hecke GRH, BSD or YM proof follows.
New original source file and this README change are not local
Lean kernel acceptance. Preserve Levent Alpöge/Claude authorship,
Sutherland/Lipponen independent verification, and original DASHI
reuse attribution.

---


## 21 November 2026 — P0 GRH-first directional BIDI (CURRENT)

**Primary objective: pinned external original all-character GRH → five exact target statements; do not route P0 through Monster VOA or the 369 finite geometry.** New authored `RHGRHP0DirectionalSourceCut.lean` (in this original-version sidecar) imports the same actual 4.33.1 upstream `Statements`, original `ClaimStrip`, `EveryCharacter`, `CritLine`, `EveryCharacterOfLiteratureOfVWin`, `VwinOfRow`, `RecTExists` and `RowSrc` as the existing selective producer. It adds:
- `halfplane_iff_original_all_character : Claim.HalfPlane ↔ UpperTheory.EveryCharacter := Iff.rfl`, original all-Dirichlet-character right half-plane predicate;
- `original_zeta_zeros_iff_mathlib_rh : RiemannZetaZerosOnLine ↔ RiemannHypothesis := Iff.rfl`, directly verified at the **type-definition** level against pinned `src/Statements.lean`;
- `original_zeta_iff_rh := Claim.zeta_iff`, exact original claim;
- directional `zeta_of_every_character`, `rh_of_original_zeta`, `original_zeta_of_rh`, carefully without an unsupported RH→EveryCharacter theorem;
- `every_character_of_original_galois_row` from the **unchanged original** `galoisLocalGlobalStrong_recParameter` and original `vwin_of_row`; original consumers yielding Mathlib RH and three stronger Dirichlet right-half/critical-strip propositions.

This is a **source-written reassembly of original theorem applications**, not an independent mathematical proof of GRH or a kernel-accepted source transfer. No Lean executable on this task runtime. The direction is intentionally asymmetric: original `EveryCharacter` proves RH and the Dirichlet claims, while `RiemannHypothesis` alone does NOT supply a source proof of every-character nonvanishing. This is **not a mathematical assertion that RH→GRH is impossible**, only a precise missing implication/receipt.

**P0 terminal BIDI:** still use root `MillenniumExternal.AlpogeRHBoundaryExact` / `ExactTargetSurface.clayRiemannHypothesis_iff_mathlib` after independently admitting the *same Mathlib* `RiemannHypothesis` theorem on compatible root Lean/Mathlib, with a transparent 4.33.1→root theorem/proof handoff. Never copy unlicensed 175,187-module source, invent a new RH proposition, or claim an olean from 4.33.1 works under 4.35.0-rc3. Actual source-header/hash readback is not a local trusted kernel replay.

**P0 acceptance order:** (1) pin/refetch original theorem blobs and v4.33.1 mathlib; (2) local version-correct `lake env lean proofs/alpoge-lean433/RHGRHP0DirectionalSourceCut.lean`, inspect `#print axioms`; (3) check original all-character and all five published terminal statements under the pinned source; (4) transfer the *RH* statement into root `ExactTargetSurface` with a trusted compatible proof rather than an assumption; (5) transfer Dirichlet GRH targets separately with original character/formula equivalences; (6) Agda semantic identity/zero/critical-line mapping and proof transport remains independently open. Deep P1 C3/Monster/Hecke only if it repairs a specific P0 original source obligation.

## 21 November — P1: actual selected TLiftK Hecke/IsLift fibre (latest)

New `RHSelectedThetaLiftConsumer.lean` consumes the **real original** `UpperTheory.TP.K.tLiftK` from the pinned fork. The source-readback `UpperTheory.TP.TLiftK` is a universal CM-field/Hecke/theta statement. Our consumer fixes an original (E,B,n,X) and retains literally the resulting (∃ d₀,∀ d≥d₀) telescope, the source `IsHecke`, `ResEtaPow`, `HasExp`, automorphic weights and an actual lifted submodule `U'` with `IsLift`. Its proof is simply application of the original author theorem, not independent reconstruction. Original typecheck/axiom receipt **OPEN**.

In Agda #1533, `RHGRHIndexedZeroZetaResidualFluxExact.agda` now admits source-accounted (r→r+δ) along a (k→k+1) commuting phase-reflection transition and retains mode, sign and observed-zero. Locally executed stdlib Python **1,728/1,728 PASS** on these finite laws. This is strictly **different from** a source `IsLift` theorem: the genuine next source weld requires identification of an actual order-3 restriction of one of the original `χX,χW` Hecke characters (if present) and a proved source theta/Galois consumer action retaining phase/sign/residual. The C3 finite model does not by itself imply a CM automorphic lift.

Do not reimport all 175187 modules just for P0: our minimal RH top-cut remains separate. No CI, no local Lean kernel proof check or Agda check.

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

## 21 November latest — our strongest RH BIDI gap pays a minimal consumer, not G2 cancellation

The smallest mathematical bridge worth importing for DASHI G2 is elementary. Original Mathlib `RiemannHypothesis`, on a **source-identified nontrivial zeta zero**, forces `Re(s)-1/2=0`, hence `cosh((Re(s)-1/2)u)=1`. The new [`RHZeroHorizontalBridge.lean`](RHZeroHorizontalBridge.lean) uses only Mathlib and proves precisely those two consequences, preserving nontrivial-zero and pole-exclusion hypotheses. **It has not been compiled** at the selected toolchain.

This is an explicit, small, cross-version re-elaboratable **consumer theorem**, not a backdoor proof transfer. To consume the *proof* of RH, the original source fork theorem must still be checked/imported in the compatible environment. Compile source `RHTopCut` separately; then apply this bridge to the actual source theorem.

On the Agda side, `DASHI.Analysis.RiemannG2AlpogeZeroLineCosineCollapseExact` consumes the existing original G2 `LiteralTargetCenteredScalarProblem` and the existing `dSigmaIsLiteralKernel` and **conditionally** proves the pure cosine integral identity. The missing actual `G2.ZeroIndex↔Mathlib nontrivialZero` and literal `G2.offRealPart = Re(s)-1/2` identification are isolated and uninhabited. This does not pay arbitrary signed cosine bounds, the balance-breaking premise, or the distinct authoritative universal pole-quotient Off/Gamma taper.

Local finite SymPy regression in Agda #1533 passes the exact source kernel collapse, with positive and negative cosine-integral counterexamples. Do not claim Agda or Lean kernel typechecking. The canonical gap matrix is [RHGRHCurrentBidiVsAlpogeExactGapCut20261121.md](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/roadmaps/RHGRHCurrentBidiVsAlpogeExactGapCut20261121.md). No CI, no source-world/PostgreSQL work.

## Current source-backed BIDI gap comparison (21 November)

New `RHClaimBidiExact.lean` is an authored **Lean 4.33.1 source adapter** that consumes the fork's original `Claim.HalfPlane`, `UpperTheory.EveryCharacter`, `Claim.zeta_iff` and `Formalism.VW.rh_of_every`. No new RH or Dirichlet character carrier is defined:
- `Claim.HalfPlane ↔ UpperTheory.EveryCharacter`: definitionally the same right-half-plane nonvanishing proposition.
- `Claim.Zeta ↔ RiemannHypothesis`: the **original fork's** exact `Claim.zeta_iff`, which is proved by `Iff.rfl`.
- `Claim.HalfPlane → RiemannHypothesis`: original `VW.rh_of_every`.

**Do not mistake this for an equivalence RH ↔ EveryCharacter**: the former is only ordinary Riemann ζ and the latter covers every Dirichlet character, hence stronger GRH scope.

**Our existing mathematical G2/Pole BIDI is NOT the same logical surface**. The Agda original `RiemannG2BidiCutReconciliationExact` has an uninhabited signed scalar→post-Schur estimate; `RiemannAristotleG2CurrentCutExact` records a target-centered signed sum and projective-balance no-go; the later authoritative `RiemannAristotleCurrentFrontierExact` uses a universal pole-quotient Off/Gamma budget rather than G2d's determinant taper. None of their inequalities follows merely from the external RH conclusion. **For terminal Clay, stop at Mathlib RH and reuse the already-existing Clay equivalence; for improved geometric proof, look only for source-typed theta and determinant donor statements.**

The exact original-owner comparison and debt table is in Agda [RHGRHCurrentBidiVsAlpogeExactGapCut20261121.md](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/Docs/roadmaps/RHGRHCurrentBidiVsAlpogeExactGapCut20261121.md).

`RHClaimBidiExact.lean`, `RHTopCut.lean` and `RHSelectiveProducerCut.lean` are all **source-written and uncompiled**, and local kernel / axiom / import-closure receipts remain open. No CI.

## More selective original source splice (P0 candidate, not yet checked)

`RHSelectiveProducerCut.lean` goes one level further than `RHTopCut.lean`: it **avoids importing original `MainConclusion` as well as `MainTheoremsAll`**, and spells out only the few-line composition `every_character_of_literature_of_vWin (... original RowSrc ...) (vwin_of_row ...)` found literally in `MainConclusion.lean`. It then consumes existing `Formalism.VW.rh_of_every`, `Formalism.VW.critLine` and `Claim.strip` without rewriting any deep producer. All five original theorem statements are exposed. This cuts *top-level convenience-wrapper imports*, but there may still be huge source transitive closures (the direct `EveryCharacterOfLiteratureOfVWin.lean` itself has a large import list). **No runtime reduction is measured yet**.

Inspect the first true geometric source chain before replacing anything:
`RowSrc.galoisLocalGlobalStrong_recParameter = galoisRepresentations_of_thetaLift tLiftK`.
`GaloisRepresentationsOfThetaLift.galoisRepresentations_of_thetaLift up = galoisLocalGlobalStrong_of_geometry_lift geoOne_holds up`.
`ThetaKernels/TLiftK.tLiftK = tLift_holds_k`.
These are the fork's actual real theta/geometric producer edges, not an inferred resemblance. A DASHI 369/Monster/Weil substitute must produce **the same** `UpperTheory.TP.TLiftK`, `UpperTheory.GalStar.Row0b recT` or a typed consumer-sufficient map to them before it can shorten the actual proof graph.

Suggested strictly local experiment, **not run**:
```sh
# From pinned fork workspace with exact Lean 4.33.1 + its Mathlib
lake build Supplements.Kernels.MainTheorems
lake env lean /path/to/dashi_lean4/proofs/alpoge-lean433/RHTopCut.lean
# Selective experiment: build its actual direct imports; no full Main target required
lake env lean /path/to/dashi_lean4/proofs/alpoge-lean433/RHSelectiveProducerCut.lean
```
Record missing imported modules/axioms and actual `.olean` closure for each, and keep the smaller cut **only if kernel accepted**. The proof graph's full original dependencies remain necessary wherever the retained original lemmas depend on them; this is not a promise of a small overall proof.

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


## 21 November — independent original RH + Dirichlet-GRH acceptance update (not our local kernel)

[Andrew Sutherland's MIT audit](https://math.mit.edu/~drew/grh/) updated **2026-11-20 22:05 UTC**: the ORIGINAL pinned 4.33.1 author source **175,187/175,187 modules compile**, five `Main.lean` theorem statements' `#print axioms` contain only `propext,Classical.choice,Quot.sound`, `leanchecker` replay accepts all 175,187 modules, full exported proof accepted by independently implemented `nanoda` and `con-leche` kernels, `lean4lean` accepted all module oleans, and `con-leche --compare` checked and accepted all **five original challenge statements**. MIT default/paranoid export-kernel and end-to-end `lake comparator` still running at that update; [LUMI independently compiled all 175,187 modules](https://github.com/aapolipponen/rh-lean-check-lumi). This now amounts to **strong independent formal evidence**, not merely the author's unverified claim. Scope of their theorem: **ordinary Mathlib RH plus all Dirichlet-character GRH**; NOT all Hecke or motivic GRH.

**Local DASHI integration status remains DEFERRED by explicit user choice**: separate v4.33.1 source-version test/axioms/compilation of our `RHGRHP0DirectionalSourceCut.lean`, root v4.35.0-rc3 Mathlib theorem/re-elaboration and Agda original complex/zero predicate transport have not been locally run. External acceptance is not a DASHI kernel receipt; no `sorry`/axiom fallback. Ordinary `Claim.Zeta ↔ Mathlib.RiemannHypothesis`; original `UpperTheory.EveryCharacter` is the strictly broader Dirichlet GRH P0 terminal, implying RH and all character strip results in the original source chain, not the converse.

**Parallel CM special case is independent of the RH zero claim**: [main-derived Lean PR #114](https://github.com/chboishabba/dashi_lean4/pull/114) constructs source-owned (E:y²=x³+1) local CM Hecke Euler candidates, HNF fractional ideal `Psi`, bad p2/p3 factors, Ogg conditional conductor and a **conditional** `σ>3/2` absolute-convergence bridge. Its **all-prime local factor and global analytic-continuation sockets remain open**. This special weight-two infinity-type-one Hecke character is not a finite-order Dirichlet character and does not fall under the externally verified **Dirichlet** GRH scope. None of its Euler or finite SymPy tests proves RH/GRH or supplies a new `UpperTheory.EveryCharacter` proof. Retain weld-forward: reuse original strongest sources; no parallel dummy theorem.
