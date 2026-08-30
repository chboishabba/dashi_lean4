# The RH/zeta analytic lane as one domain of the global TOE map

This report covers the analytic-domain pass: what was found in the archive, what
is now proved in Lean, what is classified as a typed dependency, a socket or a
boundary, and exactly what remains open. It is the prose companion of five new
machine-checked Lean modules,

| Lean module | Lines | Role |
| --- | --- | --- |
| `Lean/Integration/RiemannReflection.lean` | 448 | Faithful Lean mirror of the lane's reflection/orbit carriers, with the transports to the ternary hub and the evaluation of the cyclotomic carrier into `ℂ` |
| `Lean/Integration/RiemannStrip.lean` | 368 | The critical strip's two declared symmetries as maps of `ℂ`: fixed locus, displacement, polarity classifier, symmetry group, descent of the discrete model |
| `Lean/Integration/RiemannSubstrate.lean` | 227 | Faithful mirror of the analytic substrate tower, and the proof that it is a socket |
| `Lean/Integration/RiemannXiSymmetry.lean` | 279 | The exact rational symmetry plane of the completed zeta, its injective evaluation into `ℂ`, and the classification of its obligation surfaces |
| `Lean/Integration/RiemannDomain.lean` | 301 | The domain's registry rows, boundaries and sockets, plus the checked summary bundle |

together with the pre-existing `Lean/Spine/RiemannBridge.lean` (531 lines) and
its report `RH_BRIDGE_REPORT.md`, which are reused rather than duplicated.

**No claim about the Riemann zeta function, its zeros, or the Riemann hypothesis
is made anywhere.** Nothing here pursues the analytic specialist frontier: there
is no complex continuation, no tail estimate, no short-interval prime work and
no uniform-taper work in the new modules. No Yang–Mills or Navier–Stokes
material is touched.

---

## 0. What the archive actually contains (honest note)

The handoff describes "the complete available RiemannAnalytic Lean aggregate
plus 23 modules and its source reports". **No such Lean aggregate is present in
this archive.** A recursive search of the repository for a Lean library, module
or namespace named `RiemannAnalytic*` returns nothing; the only Lean file in the
project that mentions the analytic lane is `Lean/Spine/RiemannBridge.lean`, from
the earlier session.

What *is* present, and what this pass therefore treats as the handoff:

* **Lean (authoritative, checked here):** `Lean/Spine/RiemannBridge.lean` plus
  the generic kernel it builds on (`Spine.TwoRegime`, `Spine.AnchoredGram`,
  `Spine.TernaryPhase`, `Spine.MeanSplit`), and the report `RH_BRIDGE_REPORT.md`.
* **Agda (reference/provenance only, never rechecked — no Agda toolchain here):**
  48 `DASHI/Analysis/Riemann*.agda` modules (6 970 lines) plus
  `DASHI/Mathematics/NumberTheory/Riemann{CompletedZetaBoundary,XiSymmetryExact}.agda`,
  and the focused tranche root
  `DASHI/EverythingRiemannReflectionOrbitDefect2026.agda`, which imports exactly
  **24** modules — an aggregate plus 23, matching the shape of the handoff
  description. The natural reading is that the intended Lean mirror of that
  tranche did not make it into the archive.

Consequently the pass did what the Lean-first instruction allows: it mirrored,
in Lean, the members of that tranche whose content is finite or complex-analytic
in an elementary sense (`RiemannReflectionOrbitDefectExact`,
`RiemannReflectionC3OrbitShapeBridgeExact`, `RiemannAnalyticSubstrate`, and the
`MonsterC3CyclotomicEvaluationExact` carrier they import), and bridged those
mirrors to the common kernel. Every Agda-side statement below is source reading,
not typechecking.

---

## 1. Provenance map

### 1.1 Agda import structure of the lane

Mechanically extracted from the 50 `Riemann*` sources:

* Internal hubs: `DASHI.Analysis.WeilTestSpace` (19 importers),
  `RiemannExplicitFormula` (13), `RiemannAnalyticSubstrate` (7),
  `RiemannVonMangoldtSpecification` (5), `WeilConvolutionSquare` (4),
  `RiemannReflectionOrbitDefectExact` (4).
* **Cross-domain imports of the entire lane: three modules only** —
  `DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact` and
  `DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary` (both used only by
  `RiemannReflectionC3OrbitShapeBridgeExact` and
  `RiemannMaassMoonshineCrossPollinationExact`), `DASHI.Core.Q`, and
  `DASHI.TrackedPrimes`.
* In particular the lane imports **no** trit, `Base369`, supervoxel,
  hyperfabric, loom, codec or MDL module. Every bridge in §2 is therefore a
  *proved* link between carriers, not an import-level one — which is exactly the
  distinction the global map's four levels exist to keep.
* 18 non-`Riemann*` modules import the lane (`WeilPositivityCore`,
  `ZetaTheoremSurface`, `PrimeCounting*`, `DashiWeil*`, two
  `Mathematics/CrossPollination/Millennium*` gates, …).

### 1.2 Agda → Lean mirror table

| Agda source | Lean mirror | Faithfulness |
| --- | --- | --- |
| `RiemannReflectionOrbitDefectExact` (`ReflectionSide`, `CentredReflectionState`, `reflect`, `orbitMagnitude`, `squaredDefect`) | `Integration.RiemannReflection.{Side, CentredState, reflect, orbitMagnitude, squaredDefect}` | Constructor-for-constructor; the source's five stated lemmas are re-proved, and `reflectionFixedImpliesCriticalCentre` is strengthened to the iff `reflect_fixed_iff` |
| `RiemannReflectionC3OrbitShapeBridgeExact` (`C3Phase`, `invertC3Phase`, `OrbitRole`, `c3OrbitRole`, `zetaOrbitRole`, `phaseValue`) | `Integration.RiemannReflection.{C3Phase, invertC3Phase, OrbitRole, c3OrbitRole, centredOrbitRole, phaseValueC3, phaseC}` | Faithful; the module's two `Bool` boundary flags are replaced by theorems (§3) |
| `Moonshine.MonsterC3CyclotomicEvaluationExact` (`Cyclotomic3`, `_+c3_`) | `Integration.RiemannReflection.{Cyclotomic3, addC3, evalC3}` | Faithful, plus an evaluation into `ℂ` the source does not have |
| `Mathematics.NumberTheory.RiemannXiSymmetryExact` (`ComplexCoordinate`, `conjugateCoordinate`, `functionalReflection`, `criticalReflection`, `OnCriticalLine`, `InCriticalStrip`, `XiZeroSymmetry`, `NontrivialXiZero`, `HilbertPolyaCandidate`, `RiemannProofStage`) | `Integration.RiemannXiSymmetry.{QCoord, conjugateCoordinate, functionalReflection, criticalReflection, CriticalLine, CriticalStrip, XiZeroSymmetry, NontrivialXiZero, HilbertPolyaCandidate, RiemannProofStage}` | Faithful; the two one-directional critical-line lemmas are strengthened to the iff `criticalLine_iff_fixed`, and an evaluation `qToC` into `ℂ` is added that the source does not have |
| `RiemannAnalyticSubstrate` (four records + `RiemannHypothesisFor`) | `Integration.RiemannSubstrate.{ComplexAnalyticCarrier, GammaMellinLayer, ZetaHalfPlaneLayer, CompletedRiemannZeta, AnalyticSubstrate, RiemannHypothesisFor}` | Field-for-field, Agda `Set` fields mirrored as `Type` fields |
| `RiemannPhiCoshCoercivityReductionExact`, `RiemannCenteredGridRetentionExact`, `RiemannMixedKernelEnvelopeExact`, `RiemannComplexPoissonChannelSplitExact`, `RiemannComplexPoissonFiniteRetentionExact` | `Spine.RiemannBridge` (earlier session) | Ledgers and producer socket mirrored; real-valued content proved separately |

Not mirrored, and deliberately so: everything whose content is an analytic
estimate over an abstract producer (the Hermitian defect/detectability tranche,
the Weil square/separator files, the prime-side and von Mangoldt files). Those
belong to the specialist lane.

---

## 2. Genuine bridges to the common kernel (level iv)

All twelve positive rows live in `Integration.RiemannDomain.analyticEntries`;
`analyticEntries_levels` checks the level of each row *by `rfl` from its evidence
constructor*, so no row can be filed above the level it has a witness for. Of the
thirteen registry entries, eleven are level iv, one is level ii, one is level i.

| # | Bridge | Lean witness | What it says |
| --- | --- | --- | --- |
| 1 | reflection carrier ≅ hub polarity × magnitude | `centredPolarTransport` | The lane's `CentredReflectionState` **is** the ternary hub's digit together with a magnitude, and `reflect` **is** the hub's polarity involution on the digit coordinate |
| 2 | side classifier is polarity-equivariant | `sideTrit_reflect` | Preservation only: surjective, not injective |
| 3 | `C3Phase` ≅ `Trit` | `c3Transport` | The lane's three-phase carrier with `invertC3Phase` is the hub carrier with `Trit.inv` |
| 4 | phases are the cube roots of unity | `phaseC_invert`, `phaseC_sum`, `phaseC_cube`, `phaseC_injective` | Inversion is complex conjugation; the orbit sum vanishes in `ℂ`, not just in the source's finite model |
| 5 | cyclotomic carrier ↪ `ℂ` | `evalC3_add`, `evalC3_injective`, `evalC3_orbit_cancels` | The lane's only cross-domain Agda import evaluates additively and injectively onto `ℤ[ζ] ⊆ ℂ` |
| 6 | critical reflection = the kernel's C₂ generator | `stripC2_swap`, `stripC2_fixed_iff` | Placing `s` at `(Re s, 1 − Re s)` in `Spine.RealC2` turns `s ↦ 1 − conj s` into the swap |
| 7 | critical line = fixed locus | `critReflect_fixed_iff`, `xiReflect_fixed_iff` | `1 − conj s = s ↔ Re s = 1/2`; the functional-equation reflection alone fixes only `s = 1/2` |
| 8 | displacement = transverse coordinate | `displacement_critReflect`, `stripC2_sub_centre_mem_transverse`, `stripC2_sub_centre_zero` | `Re s − 1/2` is negated by the reflection, lies in `RealC2.transverse`, and vanishes exactly on the critical line |
| 9 | strip polarity classifier is the hub digit | `stripTrit_critReflect`, `stripTrit_eq_zer_iff`, `stripTrit_surjective` | The sign of the displacement is a hub digit whose neutral fibre is the critical line |
| 10 | discrete model ↪ real displacement line | `modelDisplacement_reflect/_abs/_sq/_injective`, `signTrit_modelDisplacement` | The Agda's ℕ-magnitude model embeds in `ℝ` compatibly with reflection, magnitude, squared defect and polarity |
| 11 | kernel envelope sees only the magnitude | `envelope_neg`, `envelope_displacement_critReflect` | `Spine.TwoRegime.envelope` is even, so an estimate on one side of the critical line is automatically one on the reflected side |
| 12 | rational plane ↪ complex plane | `qToC_injective`, `qToC_conjugate`, `qToC_functional`, `qToC_critical`, `qToC_criticalLine_iff`, `qToC_displacement_eq_zero_iff` | The lane's exact ℚ-coordinate symmetry model is a faithful sub-picture of the complex one: the evaluation is injective, intertwines all three involutions with those of §2 rows 6–8, and matches the two notions of critical line |

Row 10 is the *available* half of the adapter obligation stated in the Agda
source ("an analytic adapter must separately prove that its zero/reflection data
descends to this shape"): the target shape is now known to be a faithful picture
of the real displacement line. The other half — that actual zero data lands in
it — is not proved anywhere and is listed in §5.

The bundle `Integration.RiemannDomain.analyticDomain` collects the headline
statements of rows 1–11 together with the negatives of §3 and the sockets of §4
into one inhabited record, so the receipt is machine-checked rather than
narrated.

---

## 3. Boundaries (proved negatives)

`Integration.RiemannDomain.analyticBoundaries`; each row stores the refuted
proposition *and* its refutation.

| Refuted claim | Refutation | Note |
| --- | --- | --- |
| `C3Phase ≃ CentredState` | `c3_not_equiv_centred` | The Agda's `Bool` flag `c3AndZetaCarriersIdentified = false`, as a theorem: the reflection carrier is infinite |
| `CentredState ≃ Trit` | `centred_not_equiv_trit` | Only the sign transports; the magnitude survives |
| the two inverse-pair role fibres are in bijection | `role_fibres_not_equiv` | The zeta side's is infinite, the C₃ side's has two elements: this is exactly where the source's analogy stops, generalising its two-example observation |
| `stripTrit` injective | `stripTrit_not_injective` | The strip is not the hub carrier |
| `StripSymmetry ≃ Trit` | `stripSymmetry_not_equiv_trit` | The symmetry group generated by the functional equation and conjugation is Klein four — four elements, all involutions (`act_involutive`), acting faithfully (`act_faithful`) — so the analytic symmetry is binary, not ternary |
| the grid envelope is summable | `Spine.RiemannBridge.grid_envelope_not_summable` | Carried over from the earlier session: the two-regime envelope alone does not dominate an arithmetic-grid tail |

These rows are what stop the shared vocabulary ("phase", "trit", "reflection",
"C₃") from being read as more than it is. The trit enters the analytic lane as a
*classifier of the displacement's sign*, never as its carrier and never as its
symmetry group.

---

## 4. Sockets and typed dependencies

`Integration.RiemannDomain.analyticSockets`; each entry carries a proof of the
underdetermination.

1. **The analytic substrate tower is a socket, not a subject.**
   `substrate_does_not_constrain_rh`: the mirrored tower is inhabited
   (`analyticSubstrate`), and there are inhabitants for which
   `RiemannHypothesisFor` holds (`rh_true_substrate`) *and* inhabitants for which
   it is uninhabited (`rh_false_substrate`). No field of the tower relates
   `criticalLine` to anything else, so the tower places no constraint whatsoever
   on its own headline predicate. This upgrades the earlier session's
   observation ("`RiemannHypothesisFor` currently has no subject") into a proof
   that having a subject would not, by itself, mean anything.
2. **The abstract envelope producer.**
   `Spine.RiemannBridge.producer_socket_is_contentless` — an inhabitant exists in
   which every analytic field is `True`.
3. **The ℕ ledgers.** `Spine.RiemannBridge.ledgers_have_trivial_inhabitants` —
   each of the three ledgers is inhabited with all fields zero; a ledger is an
   encoding of `a ≤ b` (`nat_margin_iff_le`), not an estimate.
4. **The xi-zero-symmetry interface.** `xiZeroSymmetry_is_socket`: the record is
   inhabited by a witness whose zero predicate is empty at every coordinate and
   by one whose zero predicate is inhabited at *every* coordinate, so
   `zeroQuartet` — the theorem the source
   derives from it — is a statement about the interface, not about ξ. The
   companion `nontrivialXiZero_unconstrained` shows the nontrivial-zero record
   admits inhabitants on and off the critical line.
5. **The Hilbert–Pólya interface.** `hilbertPolya_is_socket`: for *any* rational
   sequence there is a candidate with that spectrum, so
   `hilbertPolya_zeros_on_criticalLine` is a definitional consequence of the
   record's own field and constrains nothing.

The nine-element `RiemannProofStage` enumeration is a label ladder and nothing
more: `stageEquiv : RiemannProofStage ≃ Fin 9` and `stage_card`.

**Typed dependency (level ii).** The cosh-coercivity ledger appears as a stored
`ℕ` field projection (`recordDependency`), and is explicitly capped at level ii
in the registry note, since by (3) it cannot be promoted.

**Vocabulary (level i).** The row
`RiemannAnalyticSubstrate.RiemannHypothesisFor → the Riemann hypothesis` is level
i and no higher: no zeta function is defined anywhere in this Lean corpus.

---

## 5. Frontier: exact remaining obligations

Nothing below is claimed, and none of it was attempted in this pass (most of it
is explicitly out of scope for this handoff).

1. **The analytic adapter.** No theorem anywhere states that zeros of any
   analytic object descend to `CentredState`, or that the displacement of such a
   zero is the `modelDisplacement` of a state. Row 10 supplies the target shape
   only.
2. **No zeta function.** Neither the Lean corpus nor the mirrored tower defines
   `ζ`, `ξ`, or a zero set; the tower's fields are abstract types. Giving the
   tower a Mathlib-backed inhabitant (`riemannZeta`, `completedRiemannZeta`,
   their functional equation and conjugation law) is the obvious next Lean step
   and is deliberately left to the specialist lane — it requires the very
   continuation/meromorphy material excluded from this handoff.
3. **Kernel identification.** `Spine.RiemannBridge.fourier_pair_sum_le` still
   carries `k ξ = ‖𝓕 f ξ‖` as a hypothesis; the source marks the corresponding
   field unproved.
4. **Local counts and a summable tail.** The envelope's grid bound is harmonic
   (§3), so a genuine decay rate or zero-counting input is required.
5. **The Hermitian/detectability tranche** (`RiemannHermitian*Exact`, ~15
   modules) has no Lean mirror at all; it is producer-and-ledger shaped, so
   mirroring it would mostly reproduce sockets. Any mirror should first identify
   which of its statements are not `ℕ`-ledger encodings.
6. **Unverified Agda.** No Agda file was typechecked (no toolchain in this
   environment) and no Agda file was edited. Every Agda-side statement in this
   report is source reading.
7. **Mirror faithfulness.** The Lean mirrors of §1.2 are hand-transcribed. Their
   faithfulness is a reading of the source, not a checked fact — the same
   soundness gap recorded for the 107 `AgdaMirror` modules in
   `TOE_GLOBAL_MAP.md`.

---

## 6. Verification status

* `lake build` from the repository root builds all default targets
  (`Synthesis`, `Cuisine`, `AgdaMirror`, `Spine`, `Integration`): success.
* No `sorry`, no project `axiom`, no `@[implemented_by]`, no `native_decide` in
  any new module.
* `Lean/Integration/AxiomAudit.lean` prints the axiom dependencies of every new
  headline result during the build; all are within
  `{propext, Classical.choice, Quot.sound}` (two of them depend on no axioms at
  all).
* The analytic rows are wired into the `Integration` aggregate
  (`Lean/Integration.lean`) and the registry's closing scope note now points at
  the analytic domain instead of denying it exists.
