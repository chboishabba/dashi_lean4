# The weld: `Lean/Spine` × `Lean/Integration`

This report covers the tranche that joins the two halves of the development into
one theorem-bearing object, and the first three domain instances of it.  Everything
below is checked: `lake build` builds all default targets with no `sorry`, no
project axiom, no `@[implemented_by]` and no `native_decide`, and
`Lean/Integration/AxiomAudit.lean` prints the axiom dependencies of every headline
result (all within `propext`, `Classical.choice`, `Quot.sound`).

Nothing in this tranche is an empirical or physical claim.  Every carrier is a
finite set of at most nine elements or a real inner product space of dimension at
most nine.

---

## 1. What was missing, and what now exists

Before this tranche:

| `Lean/Spine` | `Lean/Integration` |
|---|---|
| fixed ⊕ transverse splitting | equivariant quotients |
| anchored Gram coercivity | residual-bearing quotients |
| `C₃` realification / irreducibility | SSP transport algebra |
| nondegeneracy certificates | corpus instances, boundaries, sockets |

Two theorem families, no arrow between them.  The arrow is now
`Integration.StructuredObserver.SymmetryResolvedObserver`
(`Lean/Integration/StructuredObserver.lean`).

### The record

`SymmetryResolvedObserver G Rich Coarse Res n` bundles, as data plus proof
obligations:

1. `reduction : EquivariantQuotient G Rich Coarse` — actions on both layers, a
   surjective projection, and the square `π (g · x) = ḡ · π x`;
2. `residual : Rich → Res`, `reopen : Coarse → Res → Rich` and
   `reopen (π x) (residual x) = x` — a **reopenable residual along the same
   projection**;
3. `rep : FixedIsometryRep G n` — a representation of `G` on
   `EuclideanSpace ℝ (Fin n)` by inner-product-preserving, linear maps that **fix
   the constant direction `ones n`**;
4. `read`, `channel : Rich → EuclideanSpace ℝ (Fin n)` intertwined with the
   action, plus the two nondegeneracy witnesses (nonzero constant mode, nonzero
   transverse part).

### The theorem

`SymmetryResolvedObserver.symmetry_resolved_theorem` proves, from those fields:

* **symmetry-compatible coarse dynamics** — `π` is onto and intertwines the two
  actions (also along words: `coarse_dynamics_word`);
* **faithful fine-state recovery** — `reopen (π x) (residual x) = x`, the pair
  `(π, residual)` is injective, and `residual_nontrivial` shows the residual must
  carry ≥ 2 states whenever the coarse layer is strictly smaller;
* **a positive invariant on genuine transverse motion** —
  `nondegeneracy x = area2 (read x) (fluct (channel x))` is strictly positive
  (`nondegeneracy_pos`, inherited from the spine's anchored Gram coercivity) and
  **constant along the symmetry** (`nondegeneracy_invariant`).

The third bullet is the actual weld.  Its proof is
`FixedIsometryRep.fluct_map` + `FixedIsometryRep.area2_map`: a representation
fixing `ones` preserves the mean, hence commutes with the fixed/transverse
splitting, hence preserves the Gram area.  So the *geometric* certificate of
`Spine` is a function on the `G`-orbits used by `Integration`, and a spine
theorem may legitimately be quoted about a reduced corpus carrier.

### Controls

* `certificate_zero_of_constant_channel` — a constant channel gives a zero
  certificate, so the nondegeneracy witnesses are load-bearing.
* `polar6_no_equivariant_action` — a chart whose origin is not symmetric admits
  *no* coarse action at all, so the equivariance witness is load-bearing too.

### A reusable constructor

`ObserverBuild` + `ObserverBuild.toObserver` build the representation, the
reading and the channel from finite data: an action by bijections, a reopenable
residual, and a `G`-invariant non-constant class coordinate `cls`.  Taking
`cls = residual` covers reductions whose coarse layer moves; taking `cls = proj`
covers covers whose fibre moves.  A domain therefore earns its instantiation with
finite data and four small proofs, not by rebuilding geometry.

---

## 2. Instance 1 — the SSP / 369 lane

`ssp369Observer` (same file), built from corpus material only:

| slot | carrier | source |
|---|---|---|
| `Rich` | nine full phase cells `KernelTrit × DepthWheelPhase` | `SSP369PolarResidualQuotient.agda` (mirrored in `Integration.PolarResidual`) |
| `G` | `FibreOrientation` monoid | `SSPIndexedWeaveHyperfabricExact.agda` (mirrored in `Integration.SSPWeave`) |
| `Coarse` | `KernelTrit` — visible lane polarity, **nontrivial** induced action | — |
| `Res` | `DepthWheelPhase` — retained phase residual | — |
| geometry | permutation representation on the nine cells, `read = ones + e_cell`, channel = phase-column indicator | this tranche |

`ssp369_theorem` is the welded theorem on that lane;
`ssp369_residual_nontrivial` is the "three visible polarities cannot carry nine
states" corollary.

### Why the residual has to sit in the *target*

Two theorems, side by side:

* `polar6_no_equivariant_action` — the residual-free `9 → 6` polar chart admits
  no coarse action whatsoever making the polarity square commute.  (Same failure
  mode as the corpus's native-chart `support` observer: the chart parks the zero
  branch on the negative sheet, so its origin is not symmetric.)
* `polarResultReduction` — the residual-bearing `9 → 6 + 3` projection **is** an
  equivariant quotient, with nontrivial induced action, and is a bijection.

`equivariant_reduction_plus_residual` states the pair together.  This is the
checked form of "equivariant reduction + retained residual = lossless
symmetry-aware compression".

---

## 3. Instances 2 and 3 — two finite physics lanes

The earlier census excluded every path named for the Yang–Mills or
Navier–Stokes lanes.  That exclusion is lifted here for exactly two modules and
only for their **finite chart layers** (`Lean/Integration/PhysicsInstances.lean`):

### 3.1 `SU2SO3369HypervoxelBridge.agda` — the axis-lift double cover

* `TwoSheetedCover` — the source's `TwoSheetedCoverInterface` mirrored, with
  `axisLiftDoubleCover` inhabiting every field: two distinct lifts, free central
  flip, invariant projection, fibre completeness.
* `axisLift_card : |AxisLift| = 6` — the `3 × 2` layer.
* `axisLiftObserver` / `axisLift_theorem` — the cover as a symmetry-resolved
  observer: base axis = coarse layer (induced action trivial, so the base is the
  orbit space), lift polarity = retained residual, positive flip-invariant
  transverse certificate.  `axisLift_residual_nontrivial` closes the loop.
* `matrixSlotNonary : MatrixSlot ≃ NonaryTruth`, `matrixSlot_card = 9` — the
  output-axis × input-axis slot carrier in the nonary chart.
* `matrixSlot_no_canonical_phase_cell` — the honest control: nine slots and nine
  SSP phase cells admit more than one bijection, so the shared numeral nine is
  not a map between the lanes.

### 3.2 `NSTriadKNStage3Ternary369Ledger.agda` — the Stage-3 receipt coordinates

* `stage3SixChart : Trit × Bool ≃ HexTruth`,
  `stage3NonaryChart : Trit × TriTruth ≃ NonaryTruth` — the ledger's six- and
  nine-state coordinates as exact charts (`disposition × maturity ≃ 9`).
* `nsStage3Observer` / `nsStage3_theorem` — the nine-state coordinate as a
  symmetry-resolved observer: signed analytic disposition = coarse layer with the
  polarity involution as induced action, proof maturity = retained residual.

### 3.3 The cross-lane fact

`physics_actions_factor_through_sign`: the SSP lane-state action, the SU(2)
central flip and the Stage-3 disposition flip all factor through the *same*
homomorphism `orientationSign : FibreOrientation → ℤ/2`.  That is a proved
equivariance shared by the three lanes, not a shared word.

`physics_instances_summary` bundles the free flip, the two cardinalities, the
non-canonicity control and the four positivity/invariance statements.

### Scope, stated precisely

No gauge field, connection, curvature, energy estimate, Sobolev tail, shell
decomposition or PDE is imported, mirrored, referenced or used.  Every object in
`PhysicsInstances.lean` is a finite set of at most nine elements.  **No claim
about Yang–Mills, Navier–Stokes, mass gap, regularity, or any physical system is
made or supported.**  The modules' names are the only reason the word "physics"
appears.

---

## 3b. Instance 4 — an honest order-three symmetry

All of the instances above act through the effective `ℤ/2` of the orientation
monoid.  `Lean/Integration/StructuredObserver.lean` closes that gap with a
fourth instance whose acting group is `Phase3` (`C₃`):

* `actWheel : Phase3 → FullPhaseCell → FullPhaseCell` rotates the depth wheel of
  the same SSP nine-cell carrier and fixes the lane polarity.
* `actWheel_order_three` — the generator is **free** (never fixes a cell) and its
  cube is the identity, so this is a genuine order-three action, not an order-two
  one in disguise.
* `wheelReduction : EquivariantQuotient Phase3 FullPhaseCell KernelTrit` — the
  polarity is invariant, so the visible layer is the orbit space `9 → 3`.
* `wheelObserver` / `wheel_theorem` — the same three welded conclusions:
  equivariant coarse dynamics, exact reopening from `(polarity, phase)`, and a
  strictly positive transverse Gram certificate constant along the `C₃` orbit.

The section then connects the instance to the spine's representation theory:

* `phaseEmbed : (DepthWheelPhase → ℝ) → Spine.RealC3.V` and
  `phaseEmbed_rot : shift (phaseEmbed f) = phaseEmbed (f ∘ nextDepthWheelPhase)`
  — the corpus's depth-wheel successor **is** the spine's cyclic shift, i.e. the
  wheel carries a copy of the regular representation `ℝ[C₃]`.
* `wheel_no_invariant_line` — consequently the spine's
  `no_real_eigenvector_transverse` applies verbatim to the wheel: its transverse
  (mean-zero) plane has no invariant real line, so `3 = 1 + 2` here is the
  irreducible splitting, not a dimension count.
* `wheel_c3_summary` bundles freeness, positivity, invariance and the
  intertwining in one statement.

This is the point at which the spine's `C₃` representation theorem and the
integration layer's equivariant-quotient machinery are applied to *the same*
carrier.

---

## 3c. The hierarchy composes — `Lean/Integration/ObserverTower.lean`

The intended picture is a hierarchy, not a single arrow:

```
raw carrier --symmetry reduction--> reduced carrier --observer--> coarser carrier
```

That is now a theorem rather than a diagram.

* `compQuotient` — equivariant quotients for the same symmetry, whose middle
  actions agree, compose to an equivariant quotient.
* `Extension` — the data for one more level: a further equivariant quotient of
  the visible layer, agreeing with the induced action, carrying its own
  reopenable residual.
* `towerOf O E` — a symmetry-resolved observer extended by one level is again a
  symmetry-resolved observer, whose residual is the **pair** of residuals, and
  which keeps the same representation, reading and channel.
* `tower_nondegeneracy` — the transverse certificate is *exactly preserved*:
  coarsening the visible layer can neither manufacture nor destroy transverse
  volume.  `tower_theorem` bundles this with the three welded conclusions for the
  composite.
* `tower_card_bound` — the rich carrier embeds into
  `visible × (new residual × old residual)`: what the coarser layer stops showing
  is paid for in retained residual.

The concrete instance is the SSP nine-cell lane reduced twice:
`9 full phase cells → 3 kernel trits → 2 magnitudes`, retaining
`sign × depth-wheel phase` of size six (`sspTower`, `sspTower_theorem`,
`sspTower_cards`).  `magnitudeStep_proper` checks the second stage is a genuine
further reduction — strictly non-injective, nontrivial upstairs action, trivial
induced action — rather than a relabelling.

---

## 3d. When the certificate descends — `Lean/Integration/ObserverDescent.lean`

The welded certificate is proved constant on `G`-orbits.  Whether it is an
observable of the *visible* layer is a separate question, and this file settles
it with an exact hypothesis.

* `OrbitFibred O` — every fibre of `π` lies in a single `G`-orbit.
* `nondegeneracy_descends` / `certificate_is_coarse_observable` — under that
  hypothesis the certificate factors through `π` as a strictly positive function
  `coarseCertificate` of the visible state.
* `wheel_orbitFibred`, `wheel_certificate_descends` — the `C₃` instance is
  orbit-fibred, so its certificate *is* a visible-layer observable.
* `ssp369_not_orbit_fibred` — the SSP orientation instance is not: the flip moves
  between fibres rather than within them.  So the hypothesis is load-bearing and
  not automatic; for that instance the certificate stays an invariant of the rich
  state.

---

## 4. Wiring

* `Lean/Integration.lean` imports both new modules.
* `Lean/Integration/Registry.lean` gains **five level-iv rows** (SSP 369 weld,
  the `C₃` depth wheel, the magnitude second stage, SU(2) axis-lift, NS Stage-3)
  and **two boundaries** (the residual-free `9 → 6`
  chart has no equivariant structure; nine slots ≠ nine phase cells canonically).
  `registry_levels` still checks every row's level by `rfl`, so none of the new
  rows can be filed above the evidence it carries.
* `Lean/Integration/AxiomAudit.lean` gains 48 new `#print axioms` lines.

---

## 5. Frontier — exactly what is *not* proved

1. **Composition is proved; *refinement* of the representation is not.**
   `towerOf` composes the hierarchy and `tower_nondegeneracy` shows the
   certificate is preserved exactly.  What is still open is the converse
   direction: there is no statement that a symmetry-resolved observer can be
   *lifted* along a finer equivariant quotient, nor any theorem relating the
   certificates of two observers with different readings of the same carrier.
2. **The representation is chosen, not derived.**  Each instance supplies a
   permutation representation on the enumerated carrier.  Nothing proves it is
   canonical, and two different enumerations give two different (though
   isometric) certificates.  A statement that the certificate is independent of
   the chosen enumeration is not proved.
3. **Descent is conditional, and one instance fails the condition.**
   `nondegeneracy_descends` proves the certificate is a visible-layer observable
   exactly when the fibres of `π` are orbits, and `wheel_certificate_descends`
   applies it.  `ssp369_not_orbit_fibred` shows the SSP orientation instance does
   not satisfy the hypothesis; whether its certificate nevertheless factors
   through `π` for some other reason is not settled either way.
4. **The `C₃` instance has trivial *induced* action.**  `wheelObserver` supplies
   a genuine free order-three action on the rich carrier, and `phaseEmbed_rot`
   identifies the wheel with `ℝ[C₃]`, so the spine's irreducible transverse plane
   applies.  What is still missing is a `C₃` equivariant quotient whose *coarse*
   action is nontrivial: `wheelReduction` and the phase reduction `27 → 9` are
   both orbit maps.  Nontrivial induced actions are so far only exhibited for the
   effective `ℤ/2` lanes.
5. **No Hecke / representation-theoretic square.**  The SSP-to-prime-indexed
   representation square remains an open socket, as before.
6. **The physics tranche is chart-level only.**  Nothing connects these finite
   coordinates to any analytic object in the corresponding lanes; the Agda side
   remains unchecked here (no Agda toolchain in this environment), so every
   statement about an Agda module is source reading, not verification.
7. **`matrixSlot_no_canonical_phase_cell` is a negative.**  Whether any *natural*
   map identifies the nine operator slots with the nine SSP phase cells is open;
   equal cardinality does not supply one.

---

## 6. Addendum — gauge reduction and observational resolution

A later tranche adds `Lean/Integration/GaugeReduction.lean`,
`EquivariantChannel.lean`, `GaugeObserver.lean`, `GaugeSU2.lean`,
`GaugeSSP.lean` and `DescentLevel.lean`, reported in
`TOE_GAUGE_DESCENT_REPORT.md`.  Two items above are affected:

* **Frontier item 4 is closed.**  `Integration.GaugeSU2.su2GaugeReduction` is an
  equivariant quotient whose *coarse* action is a faithful `C₃` on a
  three-element carrier.  The reason the earlier `C₃` instances could not have
  one is now itself a theorem
  (`Integration.Gauge.GaugeReduction.coarse_action_trivial_of_orbit`): a full
  orbit quotient necessarily kills the acting group, so an effective residual
  symmetry requires a proper gauge subgroup `H ◁ G` and the quotient `G/H`.
* **Frontier item 3 is refined.**  Beyond "does the certificate descend one
  level?", `Integration.DescentLevel.CoarsestSufficient` locates the coarsest
  observation at which an invariant is still visible, proves it unique, and
  computes it on the axis lane.
