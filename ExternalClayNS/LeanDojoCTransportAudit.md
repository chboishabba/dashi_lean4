## 24 November 2026 — main-source reconciliation, supersedes historical missing-leaf descriptions

Audited main 9ba8f00cf2941850268bc927c0e1a6112996f4d8; root Lean/Mathlib 4.28.0 (not 4.35), isolated author RH/GRH 4.33.1, OpenAI NS 4.34.0-rc2. LeanDojo pinned target 603053dc267cf3efe422f438eb78098c0ececd6f native 4.31.0; re-elaborate source in compatible environment, never cast oleans across versions. No fresh kernel execution: local runtime has neither lean nor lake. No CI requested.

RH: merged #113 contains RHAdmission.lean (direct five original declarations), RHClaimBidiExact.lean, and RHGRHP0DirectionalSourceCut.lean (blob 0c463cf581a4f32fb68bfc4d979ee8cb2627c8c0) directly constructs EveryCharacter from original Galois row / RecT / Vwin, then right-half-plane, all-character and primitive strips, and modulus-one RH. Existing MillenniumExternal/AlpogeRHBoundaryExact.lean (cdbaace36cd1416c339de2ddd8ee047040a39590) uses exact Mathlib <-> Clay. External independent RH/Dirichlet GRH verification reported at https://math.mit.edu/~drew/grh/; internal local compatible admission and Agda same-object semantics still open; independent internal signed Weil route #116 remains conditional and is not prerequisite of external import. Do not reverse RH to all characters or claim an automorphic GRH theorem.

NS: main already contains unconditional SOURCE-WRITTEN dashiExactFeffermanC and dashiExactFeffermanD in ExternalClayNS/LeanDojoExactTerminal.lean (c676a0b7c988a6c6eb83509218184342a5311d47). LeanDojoTargetBridge.lean explicitly supersedes opaque statement equivalence. The five #51/older #109 leaves are implemented in current main: initial decay and force transport, coordinate-word/second derivative and quantitative force transport, momentum and divergence transport, and same-solution energy identity plus measurability (LeanDojoEnergyTransport.lean a403c36b4db702efba671e4c4bf77ae8c89e6a3f). Preserve the exact same-solution smoothness repair; no unconditional arbitrary-field energy-to-MemLp implication. Existing SubmissionAudit.directClayC/D and LiteralABCD.literalAnyOneClayResolution are direct source theorem bodies consuming OpenAI pin f9e8bc5b38b6e212696e8a30e3e91517af887bbd. No new PDE estimate or theorem adapter needed for this external route. Pinned build/axiom receipt and independent mathematical review still open, not GREEN. #53 and #109 merged; #51 open historical stack, do not blindly merge to recover code already on main. Alpoge-Buckmaster unforced breakdown remains separately conditional on missing actual certificate, verifier and patched-source acceptance; no new import until those are available and exact source licenses permit. Keep original A/B/C/D, zero mode, signed residual, indexed geometry and attribution.

Actual acceptance bug: Lean v4.33.1 src/Lean/Elab/Print.lean emits quoted declaration name followed by "depends on axioms: [...]" or "does not depend on any axioms", NOT "axioms of NAME". Existing RH driver rejected legitimate output; old NS script only grepped names and two forbidden strings. Shared exact parser scripts/check_exact_lean_axiom_receipts.py accepts exact names, multiline lists, no-axioms case and identical duplicate receipts; rejects missing, near-name, conflicting and non-foundational reports. Allowlist propext, Classical.choice, Quot.sound. 3 positive + 7 negative local Python fixture tests PASS; Git blob 513b0bc3e9438abf7b5ab7b6783968ca5a5a20c7. Updated drivers not executed against actual kernels. Parser is a local log guard, not authentication of a proof or external archive. For optional RowSrc log and exact LeanDojo terminal log use the same parser with full exact names. Existing checkout script validates fork and blob/toolchain/Mathlib pins; matching the independent checked source/export and trusted root handoff is a separate gate.

BSD merged #115 supplies conditional original Mathlib E32 local Euler vs Frobenius bridge, odd-prime literal good reduction and p2 cusp; actual minimal-reduction/residue and universal rank proof remain open. Hodge remains universal actual primitive cycle lift. P0 four lanes remain; phases/consumers coordinated in Agda #1551. No solved-count change.

# Exact LeanDojo Fefferman C transport audit

Acceptance target: pinned `MillenniumNavierStokes.FeffermanC`.

The old statement-level assumption

```text
ClaySpec.ClayOptionC ↔ MillenniumNavierStokes.FeffermanC
```

is not used by the direct max-cut.

The released comparator theorem already supplies the breakdown witness, and `Gap.lean` already pays both semantic directions needed around the independent Clay representation:

```text
comparator data -> ClaySpec.AdmissibleDataR3
ClaySpec.ClaySolutionR3 -> comparator solution
```

`LeanDojoCarrierGeometry.lean` additionally source-writes:

```text
space (spacetime_point t x) = x
time  (spacetime_point t x) = t
pair-field packing/unpacking round-trip
closed-domain membership at spacetime_point
generic ambient-smooth -> pair-spacetime-smooth pullback
ClaySpec initial divergence -> LeanDojo initial divergence
```

The solution initial condition is also source-written directly from `GlobalSmoothSolution.initial_condition` and the carrier round-trip. LeanDojo's own `Breakdown.iff_no_finite_energy_solution` removes the redundant condition-(6) witness from the contradiction branch.

The surviving obligations are therefore exactly five:

1. `ClayInitialDecayToLeanDojo`
   - align ClaySpec coordinate-direction derivative packaging and nonnegative decay constants with LeanDojo `SmoothRapidDecayInitial` coordinate partials and positive constants.
2. `ClayForceToLeanDojo`
   - fixed packing through `pairFieldToLeanDojo` into time-first ambient `Fin 4` spacetime;
   - transport ClaySpec force derivative packaging to LeanDojo `SmoothRapidDecayForce`.
3. `LeanDojoMomentumToClay`
   - transport the ambient positive-time momentum equation to ClaySpec pair coordinates;
   - extend the equality to `t = 0` from the already-paid smoothness.
4. `LeanDojoIncompressibleToClay`
   - transport ambient divergence to ClaySpec pair coordinates;
   - extend from `t > 0` to `t = 0`.
5. `LeanDojoEnergyToClay`
   - identify LeanDojo's finite coordinate-square energy representation with ClaySpec's vector `MemLp` and norm-square integral representation.

The composition is now:

```text
released comparator C
-> existing comparator-data -> ClaySpec weld
-> paid carrier/smoothness/divergence/initial-condition geometry
-> five representation leaves
-> literal ClaySpec.ClaySolutionR3
-> existing ClaySpec-solution -> comparator weld
-> contradiction
-> exact pinned LeanDojo Fefferman C
```

There is no remaining fluid estimate in the external acceptance seam. The two boundary-extension leaves are routine analytic representation obligations, not a new Navier--Stokes estimate.

Promotion rule: NS remains fail-closed until all five residual transports are inhabited and the unconditional exact target theorem kernel-checks. A conditional compiler is not GREEN.


## 12 November 2026 — energy representation source correction

The original fifth transport predicate was quantified over *arbitrary* `VelocityField 3` and assumed only LeanDojo `FiniteEnergy u`, which requires a finite integral of the scalar **sum of coordinate squares** and a uniform energy bound. The target `ClaySpec.BoundedEnergy` additionally requires `MemLp`, hence almost-everywhere strong measurability of the original vector field, not just its scalar squared norm. Without measurability, the unrestricted old implication is generally invalid.

The actual contradiction consumer always has `sol : GlobalSmoothSolution`, supplying `sol.velocity_smooth` on the original closed-half-space domain. The fifth exact leaf is therefore recut **without weakening the Fefferman C endpoint**:

```lean
def LeanDojoEnergyToClay : Prop :=
  ∀ (u : VelocityField 3),
    NavierStokes.velocity_smooth_on_global_spacetime_domain u →
    NavierStokesOnR3.FiniteEnergy u →
      ClaySpec.BoundedEnergy (leanDojoFieldToPair u)
```

The existing compiler now calls `w.energy sol.velocity sol.velocity_smooth henergy`. The remaining proof is genuine **same-field norm-square identity + measurability/finite-integral transport**, not a new Navier–Stokes estimate. This branch is **source-written/Lean kernel pending**; the predicate is recut, not inhabited. The other four leaves are unchanged. All results must be checked at the exact stacked head against PR #51's pinned LeanDojo vendor.


### Positive same-source sublemma added

`smoothLeanDojoVelocitySlice_aestronglyMeasurable` is now source-written directly in `LeanDojoCComparatorBridge.lean`. It consumes the **actual** `velocity_smooth_on_global_spacetime_domain` of the LeanDojo field and composes existing `leanDojoSmooth_to_pair` and `SemanticGap.smooth_space_slice`; the resulting spatial slice is continuous, hence AE strongly measurable with respect to `volume`. This discharges the *source-level measurability substep*, pending exact-head Lean elaboration and axiom inspection.

The positive finite-energy transport still needs the Euclidean coordinate sum-of-squares equals vector-norm-squared identity, integrability conversion using that now available measurability, and uniform bound alignment. **Do not mark `LeanDojoEnergyToClay` inhabited from this sublemma alone.**
