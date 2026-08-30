# TOE common owners — dependency/provenance map and frontier

This tranche acts on one request: several lanes of the corpus had independently
arrived at the *same theorem shapes*, and the shape's owner was still hidden
inside whichever domain first needed it. The work here extracts the common
owners, restates the shared theorems once at that level, and re-derives the
existing lane material as instances.

Everything below is a statement about **Lean code in this repository**. Nothing
here is a physical claim, and nothing here depends on any external source: the
GitHub pull requests referenced in the request were not reachable from this
environment, so the owners were extracted from the local Lean tree and named to
match the request's vocabulary. No Yang–Mills or Navier–Stokes material was read,
written, or reintroduced.

Build status: `lake build` completes with no errors and no `sorry`. Every
headline result listed here appears in `Lean/Integration/AxiomAudit.lean` or
`Lean/Spine/AxiomAudit.lean`; building those modules prints the axiom
dependencies of 366 results, and every one of them uses only `propext`,
`Classical.choice` and `Quot.sound`. There is no project `axiom` and no
`@[implemented_by]` anywhere in the Lean tree.

One incidental cleanup: `Lean/AgdaMirror/MoonshineEarn.lean` and
`Lean/MoonshineFractran.lean` proved their arithmetic facts by `native_decide`,
which puts `Lean.ofReduceBool` in the trusted base. Every one of those goals is
kernel-decidable, so they now use `decide`; both files still compile. After this
change no compiled module in the tree uses `native_decide`. (The unbuilt
`Lean/Main.lean` and the archived copies under `Lean/outputs/` are untouched:
`Lean/Main.lean` does not compile in this cutset for an unrelated reason — it
imports a module excluded from it.)

---

## 1. The owners

| Owner | Module | Defs | Theorems |
| --- | --- | --- | --- |
| `FiniteReindex` | `Lean/Spine/FiniteReindex.lean` | 3 | 23 |
| `SchurBlock` (block hidden-variable elimination) | `Lean/Spine/SchurBlock.lean` | 3 | 7 |
| `StructureMorphism` | `Lean/Integration/StructureMorphism.lean` | 6 | 21 |
| `PhaseGaugeU1` (continuous gauge instance) | `Lean/Integration/PhaseGaugeU1.lean` | 4 | 19 |
| `CertifiedMargin` | `Lean/Integration/CertifiedMargin.lean` | 3 | 13 |
| `PathTransport` | `Lean/Integration/PathTransport.lean` | 4 | 13 |
| `ResidualTaxonomy` | `Lean/Integration/ResidualTaxonomy.lean` | 5 | 11 |
| `CommutatorObservability` | `Lean/Integration/CommutatorObservability.lean` | 10 | 10 |
| `LocalRealisation` | `Lean/Integration/LocalRealisation.lean` | 5 | 10 |
| `FieldControlledDynamics` (+ attractors) | `Lean/Integration/FieldControlledDynamics.lean` | 12 | 10 |
| `MultiscaleDescent` | `Lean/Integration/MultiscaleDescent.lean` | 8 | 9 |
| `EquivarianceObstruction` | `Lean/Integration/EquivarianceObstruction.lean` | 4 | 11 |
| `ObserverBundle` | `Lean/Integration/ObserverBundle.lean` | 5 | 7 |
| `ContrastBoundary` | `Lean/Integration/ContrastBoundary.lean` | 4 | 6 |

All twelve `Integration.*` modules are imported by `Lean/Integration.lean`;
`Spine.FiniteReindex` and `Spine.SchurBlock` are imported by `Lean/Spine.lean`.
Both aggregates build.

`Spine.SchurBlock` is not a new "owner" so much as the closure of a frontier
item the previous tranche left open — see §10.2.

---

## 2. `FiniteReindex` — the first requested refactor

`Spine.FiniteReindex` now owns, once and domain-neutrally, the fact that *a
finite weighted total does not depend on the order in which the carrier is
listed*. It is proved in four layers, each layer consuming the previous one:

```
foldW_perm            foldW w e = foldW w (e ∘ σ)
foldW_of_nodup_mem    two duplicate-free enumerations with the same membership agree
meanW_perm            mean invariance
moment_perm, gramEntry_perm   moment and Gram-entry invariance
gram_comp_perm, det_gram_reindex   Gram matrix and determinant invariance
```

* `perm_of_nodup_mem` is the step the consumers actually need: two `Nodup` lists
  with the same membership are *promoted to a genuine `List.Perm`*, so the
  presentation-independence statement never has to choose an order.
* `foldW_eq_sum_univ` identifies the canonical presentation with `Finset.univ`.
* `sum_comp_equiv` is the indexed form (reindex a family along a bijection).
* `foldW_fiberwise` is the deletion/fibre consumer: a weighted total over a
  marked source set equals the total over the fibres of any classifying map.
  This makes a deletion/residual decomposition an *exact reindexing*, not an
  estimate.
* The coordinate layer (`permVec`, `inner_permVec`, `norm_sq_permVec`,
  `avg_permVec`, `meanPart_permVec`, `fluct_permVec`, `area2_permVec`,
  `gram_comp_perm`, `det_gram_reindex`) was **moved out of**
  `Integration/EnumInvariance.lean`, which now re-exports it
  (`export Spine.FiniteReindex (...)`) instead of re-proving it.

Provenance: the identity previously lived once as spectral-sum presentation
invariance and once as the certificate-presentation layer of
`Integration.EnumInvariance`. It now lives once. Consumers of the moved
declarations continue to resolve through the `export`; the axiom audit confirms
`Integration.EnumInvariance.area2_permVec` and `det_gram_reindex` still print.

---

## 3. `StructureMorphism` — the second requested refactor

One predicate now owns the commuting square, with the lanes as tiers:

```
Exact        q (f a) = g (q a)
Approx ε     dist (q (f a)) (g (q a)) ≤ ε
Sound P      q s = q t → P s → P t
Dynamic      q (f^[n] a) = g^[n] (q a);  reachability transports
Gauge        q (act γ x) = actB (hom γ) (q x)
```

`Exact` is *definitionally* `Integration.ApproximateIntertwiner.IsIntertwiner`,
so there is exactly one definition of "the square commutes" in the tree.

What the owner proves, and which lane it de-duplicates:

| Result | Absorbs |
| --- | --- |
| `tier_exact_le_approx`, `tier_unverified_vacuous` | the exact/approximate tiering; the unverified tier is *proved* vacuous, so filing a square there is an honest statement of ignorance rather than a hidden assumption |
| `exact_iterate`, `exact_fixed`, `Reaches`, `exact_reaches` | the representation/kernel-compatibility lane: one-step commutation, then `n`-step transport, fixed points, finite reachability, all inherited |
| `reaches_not_reflected` | the honest converse failure — an exact square transports forwards only |
| `Sound`, `sound_iff_factors`, `sound_of_factors`, `not_sound_of_collision` | the proof-search lane: a property transports across an observer quotient **exactly when** it factors through the quotient, and an explicit two-state counterexample shows what happens without the witness |
| `Gauge`, `gauge_of_gaugeReduction`, `gauge_of_equivariantQuotient` | the existing `Integration.Gauge` reduction and equivariant-quotient lanes, as instances |
| `approx_of_gauge` | how the group-indexed lane inherits the additive-error composition calculus (a gauge square is an approximate square at error `0`) |
| `structure_morphism_unification` | one checked record asserting all four lanes are instances of the same predicate |

This is the honest content: **no new mathematics**, but the transport theorems
now belong to the square rather than to four separate cores, and the four cores
are proved to be the same predicate.

---

## 4. `PhaseGaugeU1` — the first non-finite gauge instance

Every gauge instance in the tree was previously a finite carrier with a finite
group. `Integration.PhaseGaugeU1` breaks that ceiling with a global phase
`u • x` for `u ∈ Circle` acting on a complex inner product space. The group is
infinite and compact; the carrier is infinite dimensional in general.

The consumer trichotomy is realised for the first time on continuous data:

| Class | Witness |
| --- | --- |
| invariant | `norm_invariant`, and — the weld to the Gram lane — `inner_invariant`: the *whole Hermitian form* is unchanged, so `gram_certificate_invariant` gives gauge invariance of every quadratic/Gram certificate built from it |
| equivariant | `state_equivariant`, `channel_equivariant` (any continuous-linear channel) |
| gauge-sensitive | `arg_sensitive` (the raw phase coordinate), `state_sensitive` |
| all three at once | `u1_consumer_trichotomy` |

Two further results matter architecturally:

* `norm_complete_invariant` — on `ℂ` the norm is a *complete* invariant of the
  phase orbit (`‖z‖ = ‖w‖ ↔ ∃ u, w = u • z`). So the universal property from
  `ConsumerGauge.exists_factor_of_invariant` is realised by an explicit map, not
  by a choice.
* `phaseResidual`, `reopen_phase`, `no_retraction_without_residual` — the
  reconstructive residual for this gauge, and the proof it is not removable.

`phaseGauge` packages the whole thing as a `Gauge.GaugeReduction`, with
`phaseGauge_exact` and `phaseGauge_structureMorphism` filing it under the §3
owner. `phaseGauge_coarse_trivial` records — via the corpus's own
`coarse_action_trivial_of_orbit` — that the surviving action *must* be trivial in
the orbit-quotient case, rather than assuming it.

No physical claim: `Circle` is the unit circle in `ℂ` and nothing here concerns
electromagnetism, a wavefunction, or a measured quantity.

---

## 5. `CertifiedMargin` — certificate beats defect, and the normalisation gate

```
G ≥ g,   B ≤ b,   b < g   ⟹   G − B > 0            (margin_pos)
```

Around that core:

* `strict_of_certified_bound` — the pruning form: a certified lower bound that
  already beats the incumbent settles the comparison without evaluating the
  candidate.
* `relDefect E D = E / D`, with `relDefect_lt_one_iff` and the
  `E ≤ η·D, η < 1` gate (`contraction_of_le_eta`).
* `nogo_of_one_le_relDefect` — the **architecture-level no-go**: if every
  admissible refinement in a family still leaves the ratio at least one, then no
  downstream optimisation produces a strict margin. This is a theorem about the
  whole family, not a failed estimate.
* `eventually_contractive_of_tendsto_zero` and
  `not_eventually_contractive_of_eventually_one_le` — the two asymptotic regimes.
* `compensate`, `deriv_eq_zero_of_even`, `compensated_isLittleO` —
  **compensation before estimation**: if a reference point is fixed by a
  reflection symmetry of the quantity, the compensated difference `F(a) − F(x₀)`
  has vanishing first order there, so subtracting first exposes a strictly
  higher-order transverse quantity that estimating first destroys.
* `normalization_gate`, `normalization_is_part_of_the_theorem` — two source
  normalisations of the *same* structural inequality landing on opposite sides of
  the gate. This is the checked form of "a structural theorem plus a
  source-normalisation morphism is strictly more than the structural theorem".
* `margin_of_pays` — the bridge to the existing `Integration.CertificatePays`
  budget arithmetic.

Every statement is an order/field statement about real numbers. The table of
intended instantiations (coercivity vs. remainder, retained defect vs. arithmetic
error, certified bound vs. approximation discrepancy) is a *reading* of the
theorem; none of those instantiations is proved here, and none is attempted for
the excluded lanes.

---

## 6. `PathTransport`, `ResidualTaxonomy`, `EquivarianceObstruction`, `LocalRealisation`

**`PathTransport`.** `Path` is `Relation.ReflTransGen` of a step relation, with
identity and composition. `Simulation` + `path_transport` is the relational exact
square; `simulation_of_exact` derives it from a functional one and
`path_of_reaches` / `reaches_of_path` identify the deterministic case with
`StructureMorphism.Reaches`. `mono_le_of_path` / `not_path_of_lt` own the
**monotone obstruction** (an invariant that never decreases along a step cannot
decrease along a path, so a smaller-invariant target is unreachable), and
`persistent_obstruction` is its Boolean form. `ProofSystem` / `Provable` /
`provable_transport` are the AND/OR (hyperedge) specialisation, and
`provable_sound_of_simulation` connects it back to `StructureMorphism.Sound`.

**`ResidualTaxonomy`.** Five typed classes with their distinguishing laws:

| Class | Law | Result |
| --- | --- | --- |
| `Reconstructive` | `reopen (π x) (r x) = x` | `reconstructive_injective`, `reconstructive_of_residualQuotient` |
| `Trajectory` | persistence along transitions | `trajectory_obstruction` (delegated to `PathTransport.persistent_obstruction` — the shared theorem) |
| `Contrastive` | relational in two states | `contrast_not_function_of_present` |
| `Ambiguity` | alternatives retained, never collapsed | `resolve_eq_none_of_disagree` |
| combinatorial (no separate type: the law *is* the reindexing identity) | exact fibre decomposition | `combinatorial_residual_exact` (delegated to `Spine.FiniteReindex`) |

and the separations `trajectory_not_reconstructive`,
`contrastive_not_reconstructive`: a residual can be persistent, or genuinely
relational, and still fail to reopen the quotient. The five classes are proved
not to be one type with five names.

**`EquivarianceObstruction`.** `EquivariantEquivalence` forces the orbit
invariants to agree: `fixed_iff`, `stabilizer_eq` (literal equality),
`period_iff`, `orbit_image`. The no-go is `no_equivariant_of_free_and_fixed` (a
free action admits no equivariant equivalence with an action having a fixed point
of a nontrivial element), instantiated by
`card_equal_but_not_equivariantly_equivalent` on two three-element carriers — so
the obstruction is orbit structure, *not* counting.
`translation_free_group` and `no_equivariant_free_shift_to_ramified` give the
`5 × 3` case at the right generality: the free translation of `C₅ × C₃` on
itself admits no equivariant equivalence with *any* action of the same group
having a fixed point of a nontrivial element, the target carrier being
arbitrary.

**`LocalRealisation`.** A `Plan` is a finite list of steps; `eval` is its
semantics and `exposure` its intermediate materialisation count.
`semantic_parity_not_bounded_exposure` exhibits two plans with identical
semantics and different exposure; `exposure_unbounded` shows the semantics is
compatible with *every* exposure bound being exceeded. Hence
`no_localRealisation_from_semantics_alone`: the locality certificate cannot be
manufactured from the semantics. `localRealisation_transfers` records the one
direction that does hold. This is a typed distinction between two certificates,
**not** a complexity lower bound.

---

## 7. `MultiscaleDescent`, `CommutatorObservability`, `ObserverBundle`, `FieldControlledDynamics`, `ContrastBoundary`

**`MultiscaleDescent`.** A `LawTower` carries carriers, coarsenings and a law on
each level. `descendsAt_iff_exact` says descent at one level *is* the exact
square, so all §3 transport applies; `descends_projTo` composes descent along the
whole tower and `trajectory_descends` transports finite trajectories.
`ApproxDescendsAt` / `approx_descends_two` give the certified-approximate tier
with errors adding along the tower. `NoEffectiveLaw` is the strongest negative —
not that a *chosen* coarse operator fails, but that **no** operator makes the
square commute — realised at level one of an explicit three-level tower
(`defect_no_effective_law_at_one`), with the quantitative
`defect_lower_bound` (every candidate effective law has defect at least `1/2`
somewhere).

**`CommutatorObservability`.** The configuration

```
A (B x) ≠ B (A x)            fine noncommutativity
π (A (B x)) = π (B (A x))    coarse flatness
```

is owned here. `coarseFlat_of_exact_pair` is the positive control (coarse
flatness alone is evidence of nothing); `hidden_order_information` and
`no_reconstruction_of_order` are the general statements; `cubie_hidden_order`
verifies both hypotheses on an explicit four-state carrier `Cubie` by decision;
`commDefectVal` / `commutator_defect_pos` / `coarse_defect_zero` quantify the
defect. `cubie_coarsest_sufficient` then answers the resolution question on that
carrier: the commutator defect factors through the two-valued observer and not
through the trivial one, so its coarsest sufficient observation is level one of
the tower. **No connection, curvature tensor or metric is constructed**, and no
physical system is claimed to realise the carrier.

**`ObserverBundle`.** `Bundle`, `Transport`, `BundleObserver`, and
`MeasuredExactly` defined as the §3 exact square applied to the measurement
square. `measured_of_factors` is the positive case; `not_measured_of_collision`
the failure. `pullbackDist` makes the measurement induce a pseudodistance
(`pullbackDist_comm`, `pullbackDist_triangle`), and
`coarse_zero_fine_distinct` is the precise form of "coarse distance zero does not
imply fine distance zero"; `pullbackDist_le_of_nonexpansive` records the one
implication that does hold. The base is an arbitrary type: no manifold, no metric
tensor, no spacetime structure is constructed.

**`FieldControlledDynamics`.** `FieldControlled` gives a fixed carrier with a
state-dependent background field. `field_changes_successor`,
`field_changes_effective_edge` and `field_changes_reachability` are the three
separations on an explicit four-state carrier with two fields;
`structural_edge_insufficient` packages them (same structural edge relation,
different effective edge relations, so the structural carrier does not determine
the effective dynamics). The attractor half gives `Fixed`, `Basin`, `Cycle`,
`eventually_periodic` (finite carrier ⇒ every trajectory repeats) and
`threeClass_classes` (two fixed points and a two-cycle on one carrier).

**`ContrastBoundary`.** `contrast O t = O (t+1) − O t` with `sum_contrast` /
`state_add_contrasts` (telescoping: a trajectory is recovered from its increments
plus one initial condition) and `contrast_not_determined_by_state` — the observer
non-descent theorem in derivative clothing. `Middles` is the two-boundary
constraint system, with `middles_depends_on_future`, `middles_depends_on_past`
and `middles_not_function_of_past`. Nothing here is retrocausal: the statement is
about which two-sided constraints a path satisfies.

---

## 8. Dependency graph of the new material

```
Spine.TransverseGram, Spine.MeanSplit
        └── Spine.FiniteReindex ────────────────┐
                 └── Integration.EnumInvariance │  (re-export)
                                                │
Integration.ApproximateIntertwiner              │
Integration.GaugeReduction                      │
        └── Integration.StructureMorphism       │
                 ├── Integration.PhaseGaugeU1   │   (+ ConsumerGauge)
                 ├── Integration.EquivarianceObstruction
                 ├── Integration.LocalRealisation
                 ├── Integration.ObserverBundle
                 ├── Integration.MultiscaleDescent      (+ DescentLevel)
                 ├── Integration.CommutatorObservability (+ DescentLevel)
                 └── Integration.PathTransport
                          ├── Integration.FieldControlledDynamics
                          ├── Integration.ContrastBoundary
                          └── Integration.ResidualTaxonomy ──┘
                                     (+ Integration.ResidualQuotient)

Integration.CertificatePays
        └── Integration.CertifiedMargin

Spine.SchurComplement (scalar hidden variable)
        └── Spine.SchurBlock (vector hidden block; schurB_eq_schur reduces back)
```

Every arrow is a Lean `import` together with at least one Lean theorem in the
lower module that uses a declaration from the upper one. No arrow is asserted on
the strength of shared vocabulary.

---

## 9. Classification of what is in the new modules

* **Proved theorems** (checked, axiom-audited): everything named in §§2–7.
* **Definitions/structures** (carry no content by themselves): `Tier`,
  `Gauge`, `LawTower`, `Bundle`, `Transport`, `BundleObserver`,
  `FieldControlled`, `ProofSystem`, `Plan`, `EquivariantEquivalence`,
  `Reconstructive`, `Trajectory`, `Contrastive`, `Ambiguity`, `Middles`,
  `CommPair`.
* **Explicit finite instances** used to prove separations (they are witnesses,
  not models): the four-state `Cubie`, the three-level `defectTower`, the
  two-field four-state carrier, `threeClass`, the two three-element `ZMod 3`
  carriers, the `Middles` sample graph.
* **Sockets deliberately left open** (a hypothesis the caller must supply, and
  the point of the design): `Sound` requires a soundness witness before any proof
  transport; `Tier.unverified` is proved vacuous; `LocalRealisation` must be
  supplied, never inferred.
* **Placeholders / postulates / `sorry`**: none in the new material.

---

## 10. Frontier — exactly what is *not* proved

Carried forward from the previous tranche and still open:

1. **Canonical orbit–stabilizer residual.** The canonical injection
   `G ⧸ Stab x ↪ Res` and the index bound are proved; the *bijection*
   `R_[x] ≅ G ⧸ Stab x` under a minimality hypothesis is not.
2. **Matrix-block Schur complement — *closed in this tranche*.**
   `Lean/Spine/SchurBlock.lean` proves the vector-hidden-block version:
   completing the square in the block (`coupledB_eq_schurB_add`), the minimum
   characterisation `S = D − BᵀA⁻¹B` (`schurB_isLeast`, attained at
   `−A⁻¹B y`), and the `S ≥ (δ − η)` transfer in its quadratic-form reading
   (`schurB_coercive`, `schurB_pos_of_coercive`). `schurB_eq_schur` shows the
   existing scalar file is its rank-one case. What is *still* open: the
   hypotheses (self-adjointness, positive semidefiniteness, a right inverse for
   `A`) are supplied by the caller rather than derived from a spectral theorem,
   and there is no version for a merely positive-definite `A` without a supplied
   inverse.
3. **Hecke square.** `Φ ∘ R_p = T_p ∘ Φ` is not stated for any Hecke operator.
   The tiering machinery of §3 is available for it, but bridging out of the
   finite-chart world remains the largest open step.
4. **Certificate-controls-dynamics.** `CertifiedMargin` is budget arithmetic.
   There is no evolution equation, no differential inequality, and therefore no
   claim that any certificate controls any dynamical quantity.
5. **Inserting the canonical observer into a tower.** Both directions of
   tower-relative versus intrinsic sufficiency are proved, but there is no
   construction of a canonical refinement of a tower whose coarsest sufficient
   layer is always equivalent to the canonical observer.
6. **Agda side.** No Agda module has been typechecked in this environment (no
   Agda toolchain is available here). Every claim in this report is a Lean claim
   about Lean definitions.

New to this tranche:

7. **Gauge groups beyond `U(1)` on a complex inner product space.**
   `PhaseGaugeU1` is the only non-finite instance. There is no `SU(2)`, no
   non-abelian compact group, no Lie-algebra statement, and no continuous *family*
   of gauge transformations (only a single global phase).
8. **The multiscale and commutator instances are finite witnesses.**
   `defectTower` has four states and two coarsenings; `Cubie` has four states.
   They prove that the patterns are realisable and that the negatives are
   genuine. They are not models of any physical or biological system, and
   nothing in the tree connects them to one.
9. **No connection, curvature, holonomy or metric tensor is constructed.**
   `CommutatorObservability` proves *fine noncommutativity with coarse flatness*
   and computes its descent level. Upgrading that to a curvature-like quantity
   would additionally require a transport family indexed by a base, a connection
   law, a loop/commutator construction over that base, and the descent statement
   for it. Only the last ingredient exists.
10. **`ObserverBundle` has an arbitrary base.** No manifold structure, no metric
    on the base, no smoothness, no fibre bundle in the geometric sense — the
    "bundle" is a family of fibres over a type together with transport maps.
11. **No instantiation of `CertifiedMargin` into an analytic lane.** The table of
    readings in §5 is a reading, not a theorem. Producing an actual instance
    requires the lane's own analytic bounds, which are not in this repository
    (and the excluded lanes are out of scope by instruction).
12. **`FiniteReindex` layer four is finite-dimensional real.** The determinant and
    anchored-area invariance statements are on `EuclideanSpace ℝ (Fin n)`. There
    is no infinite-dimensional or complex version, and no statement about
    infinite sums.
13. **The `EquivarianceObstruction` no-go is single-element.** It uses one group
    element with a fixed point against a free action (which is enough for the
    `C₃` and `5 × 3` instances). The stronger orbit-size and stabilizer-type
    spectra are proved to be *preserved* (`stabilizer_eq`, `period_iff`) but are
    not packaged into a decision procedure for two given finite actions.

---

## 11. What this tranche does *not* claim

It does not claim a physical theory of everything. It does not claim a mass gap,
a regularity result, or anything about the Riemann hypothesis. It does not claim
that any finite carrier used as an instance *is* a physical, neural or biological
system; the finite carriers instantiate patterns and nothing more. It does not
claim that the brain, or any measurement of it, is described by
`ObserverBundle`, `CommutatorObservability` or `MultiscaleDescent` — those
modules contain no empirical content and reference no data. It does not claim
that shared terminology between modules constitutes a mathematical link: every
link asserted above is a Lean import plus a Lean theorem, and the axiom audit is
the check.
