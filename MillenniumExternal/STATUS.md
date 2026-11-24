## 24 November 2026 — main-source reconciliation, supersedes historical missing-leaf descriptions

Audited main 9ba8f00cf2941850268bc927c0e1a6112996f4d8; root Lean/Mathlib 4.28.0 (not 4.35), isolated author RH/GRH 4.33.1, OpenAI NS 4.34.0-rc2. LeanDojo pinned target 603053dc267cf3efe422f438eb78098c0ececd6f native 4.31.0; re-elaborate source in compatible environment, never cast oleans across versions. No fresh kernel execution: local runtime has neither lean nor lake. No CI requested.

RH: merged #113 contains RHAdmission.lean (direct five original declarations), RHClaimBidiExact.lean, and RHGRHP0DirectionalSourceCut.lean (blob 0c463cf581a4f32fb68bfc4d979ee8cb2627c8c0) directly constructs EveryCharacter from original Galois row / RecT / Vwin, then right-half-plane, all-character and primitive strips, and modulus-one RH. Existing MillenniumExternal/AlpogeRHBoundaryExact.lean (cdbaace36cd1416c339de2ddd8ee047040a39590) uses exact Mathlib <-> Clay. External independent RH/Dirichlet GRH verification reported at https://math.mit.edu/~drew/grh/; internal local compatible admission and Agda same-object semantics still open; independent internal signed Weil route #116 remains conditional and is not prerequisite of external import. Do not reverse RH to all characters or claim an automorphic GRH theorem.

NS: main already contains unconditional SOURCE-WRITTEN dashiExactFeffermanC and dashiExactFeffermanD in ExternalClayNS/LeanDojoExactTerminal.lean (c676a0b7c988a6c6eb83509218184342a5311d47). LeanDojoTargetBridge.lean explicitly supersedes opaque statement equivalence. The five #51/older #109 leaves are implemented in current main: initial decay and force transport, coordinate-word/second derivative and quantitative force transport, momentum and divergence transport, and same-solution energy identity plus measurability (LeanDojoEnergyTransport.lean a403c36b4db702efba671e4c4bf77ae8c89e6a3f). Preserve the exact same-solution smoothness repair; no unconditional arbitrary-field energy-to-MemLp implication. Existing SubmissionAudit.directClayC/D and LiteralABCD.literalAnyOneClayResolution are direct source theorem bodies consuming OpenAI pin f9e8bc5b38b6e212696e8a30e3e91517af887bbd. No new PDE estimate or theorem adapter needed for this external route. Pinned build/axiom receipt and independent mathematical review still open, not GREEN. #53 and #109 merged; #51 open historical stack, do not blindly merge to recover code already on main. Alpoge-Buckmaster unforced breakdown remains separately conditional on missing actual certificate, verifier and patched-source acceptance; no new import until those are available and exact source licenses permit. Keep original A/B/C/D, zero mode, signed residual, indexed geometry and attribution.

Actual acceptance bug: Lean v4.33.1 src/Lean/Elab/Print.lean emits quoted declaration name followed by "depends on axioms: [...]" or "does not depend on any axioms", NOT "axioms of NAME". Existing RH driver rejected legitimate output; old NS script only grepped names and two forbidden strings. Shared exact parser scripts/check_exact_lean_axiom_receipts.py accepts exact names, multiline lists, no-axioms case and identical duplicate receipts; rejects missing, near-name, conflicting and non-foundational reports. Allowlist propext, Classical.choice, Quot.sound. 3 positive + 7 negative local Python fixture tests PASS; Git blob 513b0bc3e9438abf7b5ab7b6783968ca5a5a20c7. Updated drivers not executed against actual kernels. Parser is a local log guard, not authentication of a proof or external archive. For optional RowSrc log and exact LeanDojo terminal log use the same parser with full exact names. Existing checkout script validates fork and blob/toolchain/Mathlib pins; matching the independent checked source/export and trusted root handoff is a separate gate.

BSD merged #115 supplies conditional original Mathlib E32 local Euler vs Frobenius bridge, odd-prime literal good reduction and p2 cusp; actual minimal-reduction/residue and universal rank proof remain open. Hodge remains universal actual primitive cycle lift. P0 four lanes remain; phases/consumers coordinated in Agda #1551. No solved-count change.

# Millennium external acceptance status

Pinned upstream: `lean-dojo/LeanMillenniumPrizeProblems@603053dc267cf3efe422f438eb78098c0ececd6f`.

This layer is fail-closed: `GREEN` means a theorem term has kernel-checked
against the exact pinned upstream proposition. Source-written adapters, theorem
names, registry strings, historical solution status, or Boolean receipts do not
count.

The exact same-kernel audit surface now imports and `#check`s all seven pinned
problem statements. That is a conformance result only: it does not turn an open
mathematical producer, an incomplete upstream specification, or a historically
solved-but-unformalized problem into an exact proof receipt.

| Problem | Current max-cut | State |
|---|---|---|
| P vs NP | Agda literal SAT lower-bound compiler exists; universal polynomial SAT failure remains uninhabited in current source; exact machine-model transport also remains | RED-MATH |
| RH | Exact LeanDojo ↔ Mathlib `RiemannHypothesis` weld source-written; current DASHI global/high-zero producer remains open | RED-MATH |
| Navier–Stokes | Literal independent Clay C/D theorem terms already exist; only `ClaySpec C/D ↔ LeanDojo Fefferman C/D` same-statement/representation weld remains; no new fluid estimate belongs here | RED-TYPE |
| Hodge | Pinned LeanDojo statement explicitly incomplete; stronger DASHI algebraic-cycle programme remains authoritative | UPSTREAM-INCOMPLETE |
| BSD | Exact upstream target compiles from `Rank.Existence + finite rank`; DASHI same-curve rank carriers are wired to a typed weld, while universal rank equality remains open | RED-MATH |
| Yang–Mills | Pinned LeanDojo statement explicitly incomplete; stronger DASHI OS/QFT/mass-gap programme remains authoritative | UPSTREAM-INCOMPLETE |
| Poincare | Pinned statement is historically solved, but upstream explicitly does not include Perelman's Lean proof; retained only as an exact statement/regression surface | UPSTREAM-SOLVED-UNFORMALIZED |

## What the max-cut rules out

The current exact-target work removes statement-name drift and the earlier
cross-toolchain excuse: the pinned LeanDojo statements and the strongest root
DASHI donors can co-elaborate in one Lean environment. The surviving REDs are
therefore intentionally narrow:

- RH: produce Mathlib's actual `_root_.RiemannHypothesis`;
- BSD: inhabit the existing same-object rank/continuation weld and the universal
  rank equality it consumes;
- P vs NP: produce the universal polynomial SAT failure/lower-bound theorem and
  certify the machine-model transport;
- NS C/D: prove the proposition-level representation weld between the already
  proved independent Clay specification and LeanDojo's Fefferman carrier.

No adapter is allowed to add a fresh Millennium hypothesis merely to make one
of these endpoints typecheck.

## Kernel receipts

The GitHub workflow builds the immutable upstream package in its native Lean
4.31 graph, probes the exact faithful target source beside DASHI under DASHI's
kernel, probes the nested literal NS C/D project beside the exact LeanDojo
statements, and runs the DASHI terminal/axiom audit.

The current connector-visible exact head still has no pull-request workflow run.
Therefore the new tranche is **SOURCE-WRITTEN / KERNEL-PENDING** and no lane is
promoted to `GREEN` on static inspection alone.
