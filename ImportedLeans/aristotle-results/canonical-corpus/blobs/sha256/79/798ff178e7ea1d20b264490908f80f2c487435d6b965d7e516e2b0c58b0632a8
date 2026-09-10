# The shared inference kernel — consolidation report

This round acted on one request: **extract the kernel that the domain lanes keep
rediscovering** — collision → discriminator → probe → refinement → governed
merge → selective reopening — and make the other lanes thin instances of it,
rather than letting each domain re-derive it.

Everything below is Lean 4 / Mathlib, machine-checked in this repository. Nothing
here is a physical, chemical, legal, historical or social claim.

---

## 0. What was available, and what was not

The request describes an open block of draft pull requests on an external
repository. **No PR head, patch or branch was delivered to this environment**,
and the tracked tree still contains a single commit with no PR refs (see
`PR_HEADS_STATUS.md`, which records the same gap for the earlier block). The
kernel below was therefore built from

* the *descriptions* in the request (used as a specification of what the kernel
  should say, never as evidence that some other repository already proves it),
  and
* the material actually present here: the Lean `Integration.*` spine, in
  particular the experiment/inference lanes.

Consequently this report makes **no statement about the content, correctness or
mergeability of any pull request**, and no theorem here is claimed to be an Agda
result: no Agda toolchain is available here and no Agda file was modified or
rechecked.

---

## 1. The kernel

`Lean/Integration/Kernel/` — six modules, all sorry-free, wired into the
`Integration` aggregate and audited in `Lean/Integration/AxiomAuditKernel.lean`
(131 `#print axioms` lines, every one reporting a subset of
`{propext, Classical.choice, Quot.sound}`).

### 1.1 `ResidualFibre.lean` — the residual calculus

| item | kind | statement |
|---|---|---|
| `Refines F₁ F₀` | definition | `F₁ ⊆ F₀`; reflexive, transitive, antisymmetric |
| `Channel Ω Y`, `event`, `refineBy`, `refine` | definitions | measurement as backward refinement `F_new = F_prior ∩ O⁻¹(y)` |
| `refine_refines`, `refine_mono`, `refine_idem`, `refine_comm` | theorems | every reading refines; monotone in the prior; idempotent; **measurements commute** |
| `refineAll`, `refineAll_append_refines` | definition + theorem | imperfect measurements compose monotonically |
| `truth_survives`, `refine_nonempty_of_truth` | theorems | an honest reading never discards the actual world |
| `Determines`, `Collision`, `determines_iff_not_collision` | definitions + theorem | consumer-relative closure = absence of a consumer collision (**on an inhabited fibre**) |
| `determines_empty` | theorem | the empty fibre determines everything — a closure claim needs an inhabitedness receipt |
| `determines_of_factors` | theorem | mechanistic closure ⇒ decision safety for consumers factoring through the mechanism |
| `narrower_not_mechanism` | **refusal** | narrower residual fibre ⇏ exact mechanism identified |
| `decision_safe_not_mechanism` | **refusal** | decision-safe approximation ⇏ mechanistic closure |
| `witness_coordinates_nonconstant` | theorem | the refusals are not artefacts of degenerate observables |

### 1.2 `Probe.lean` — discriminators and the AND-node terminal bug

| item | kind | statement |
|---|---|---|
| `Discriminates`, `achievable` | definitions | separation of two surviving worlds; the outcomes the fibre can produce |
| `strictly_refines_iff_discriminates` | theorem | strict refinement at an achievable outcome ⇔ discrimination |
| `unachievable_outcome_empties` | theorem | refining by an impossible outcome is refutation, not information |
| `ResolvesFor`, `resolves_of_factors`, `resolving_probe_closes` | definition + theorems | a probe determining the consumer coordinate settles it whatever it returns |
| `discriminating_probe_need_not_resolve` | **refusal** | separating worlds is weaker than answering the question |
| `collision_persists_of_constant` | theorem | a probe constant on the fibre changes nothing |
| `Leaf`, `AndNode`, `contribution`, `vacuouslySucceeds`, `Resolves` | definitions | the AND-node format |
| `vacuous_success_is_not_resolution` | **refusal** | unknown empirical leaf ≠ empty target list: the no-target-terminal convention reports success while the collision survives |
| `real_target_resolves` | theorem | the same node shape with a genuine target does resolve it — the defect is the convention |

### 1.3 `Merge.lean` — four modes kept apart by proof

`fastForward`, `threeWay`, `provedJoin`, `guarded`, all proved to refine the
base (`guarded_never_weakens_base`), with `threeWay` a meet (commutative,
associative, idempotent), `merge_preserves_truth`,
`merge_preserves_determination`, and `threeWay_can_refute` (reconciliation is
also conflict detection). The separations:
`fastForward_ne_threeWay`, `provedJoin_ne_threeWay`, `guarded_ne_threeWay`,
`guarded_ne_fastForward` — together with `fastForward_eq_threeWay_of_not_diverged`,
which isolates the degenerate case where the modes do agree and hence get
confused.

### 1.4 `Authority.lean` — telemetry gap and requirement authority

| item | kind | statement |
|---|---|---|
| `Telemetry`, `Faithful`, `Credulous` | definitions | physical / reported / believed state plus the action |
| `telemetry_layers_separate` | theorem | all three layers can differ at one world |
| `rational_wrt_report_not_rational_wrt_truth` | **refusal** | rational search relative to a bad observation ⇏ rational search relative to the truth |
| `faithful_credulous_transfers` | theorem | the gap is exactly the failure of the two bridges |
| `report_cannot_certify_itself` | **refusal** | no rule reading the report returns the physical state — status must be read from the canonical state |
| `Requirement`, `Satisfies`, `Weakens`, `StrengthPreserving` | definitions | consumer requirements and their revision |
| `weakening_manufactures_satisfaction` | **refusal** | a producer that weakens its consumer manufactures satisfaction with no change on its own side |
| `satisfies_of_strength_preserving`, `authorised_revision_composes`, `authorised_chain_not_weakening` | theorems | non-weakening revision closes the cheat, and composes |

### 1.5 `Reopen.lean` — edge-indexed selective reopening

`DepGraph`, `reopened`, `closedAfter`; `reopen_of_revised_edge`,
`stays_closed_of_disjoint`, `reopened_mono`, `reopened_union`,
`closedAfter_antitone`, `reopening_is_selective`, and `reopen_propagates`
(reopening travels up an inheriting dependency relation). Provenance:
`Origin`, `Coordinate`, `no_rule_recovers_origin`,
`value_agreement_is_not_lineage_agreement` — **introduced downstream ≠ restored
inherited lineage**.

### 1.6 `Loop.lean` — the closed loop, and why it stops

| item | kind | statement |
|---|---|---|
| `Policy`, `step`, `run` | definitions | probe choice, one turn, `n` turns |
| `run_antitone`, `run_refines` | theorems | narrowing is never undone |
| `truth_mem_run`, `run_nonempty` | theorems | the loop never discards the actual world |
| `step_strict_of_discriminates` | theorem | a discriminating probe strictly narrows, whatever it returns |
| `Responsive` | definition | a live collision is always answered with a discriminating probe |
| `responsive_run_card` | theorem | `ncard (run n) + n ≤ ncard F` while collisions persist |
| **`responsive_policy_closes`** | **theorem** | over a finite space the consumer's question is determined within `ncard F` turns, on a fibre still containing the truth |
| `closure_is_consumer_relative` | **refusal** | the loop closes the consumer's coordinate and can halt with another wide open |
| `unresponsive_policy_never_closes` | **refusal** | responsiveness is load-bearing, not decorative |
| `strategy`, `strategy_merges_iff`, `strategy_needs_both_coordinates` | definition + theorems | the outcome-adaptive rule (global-sensitive → refine; local & inherited → merge; local & introduced → refine), characterised |
| `branches_merge_refines`, `merge_preserves_truth_of_runs` | theorems | composition with the merge layer |

---

## 2. Thin instances

`Lean/Integration/Kernel/Instances/`.

### 2.1 `ParameterRegion.lean` — the strongest instance

The continuous parameter-region lane (`Integration.Experiment.ParameterRegion`,
built in an earlier round with its own monotonicity and soundness proofs) is
proved **equal** to the kernel:

```
Compatible F E = refineAll F.prior (E.map (fitEvent F))          -- compatible_eq_refineAll
fitEvent F r  = (predChannel F r).read ⁻¹' Icc (value - tol) (value + tol)
```

so an imperfect reading is the preimage of an *interval*, and the lane's
monotonicity (`evidence_refines`), soundness (`truth_survives_kernel`) and prior
containment (`compatible_refines_prior`) are re-derived as kernel instances.
Consumer closure is identified with envelope collapse in both directions
(`envelope_subsingleton_of_determines`, `determines_of_envelope_subsingleton`),
and the kernel refusal is instantiated as
`region_narrowing_is_not_identification`.

### 2.2 `CollectiveAction.lean`

Seven modes (participation, refusal, withdrawal, rule-change, exit,
organisation, bargaining) proved pairwise non-implying; option-cone
`StrictExpansion`; `organisation_without_expansion` (a union present is not the
theorem); `EffectiveOrganisation` bundling organisation *with* expansion, shown
inhabited; `expansion_is_not_refinement` (affordance growth is the opposite
order to epistemic narrowing); `ProductiveDialecticalJoin` with
`join_irreducible`, `opposition_is_not_synthesis` and `productive_join_exists`.

### 2.3 `Distribution.lean`

Four independent distributions (contributes / benefits / bears / voice);
`aggregate_hides_distribution`; `equal_cost_not_equal_burden`,
`_benefit`, `_voice`; `cheapest_is_not_least_burdensome`; and the two-way
independence of cost and burden. This is the guard the loop's probe-selection
layer needs: a cost function cannot be promoted to social admissibility.

### 2.4 `Translation.lean`

Six-chart records; `clinicalTranslation` preserving the clinical coordinate and
erasing subject authorship; `erased_coordinate_is_unrecoverable`;
`reintroduction_is_not_restoration`. Reception paths: `R ∘ I ≠ I ∘ R`,
`same_present_vocabulary_not_same_history`,
`same_future_cone_not_same_transport_history`,
`coarse_code_is_not_a_history_certificate`.

### 2.5 `Assay.lean`

The eight-leaf assay AND node instantiated on the probe layer, with the two
empirical leaves (matrix/extraction behaviour, LOD/LOQ) unknown and therefore
target-free: `assay_narrows_but_does_not_resolve`, `assay_vacuously_succeeds`,
`assay_collision_survives_vacuous_success`, `new_measurement_separates`,
`reinterpretation_does_not_separate`.

### 2.6 `ObservationalEquivalence.lean` — a second *equality* weld

The lane `Integration.Experiment.ObservationalEquivalence` compares theories,
not parameters, through the distinctions an experiment language forces.  The
weld puts the residual fibre in the space of theories:

* `predChannel e` is the kernel channel reading off what a candidate theory
  permits for experiment `e`; `agreesEvent e H` is the event of running `e` and
  finding agreement with the reference theory;
* **`obsClass_eq_refineAll`** — the observational equivalence class of `H`
  relative to a finite language *is* `refineAll` of the space of all theories by
  those events;
* `obsClass_append_eq_refineAll` / `obsClass_append_refines` — enlarging the
  language is further kernel refinement, so the lane's antitonicity is
  `refineAll_refines`;
* `separates_iff_discriminates` — a separating experiment is exactly a
  discriminating kernel probe on the pair;
* `strictly_refines_iff_separates` — the lane form of
  `strictly_refines_iff_discriminates`;
* `redundant_experiment_does_not_refine`;
* `class_narrowing_is_not_theory_identification` — the lane's instance of
  `narrower_not_mechanism`.

### 2.7 `ModelSelection.lean` — a third *equality* weld

`Integration.Experiment.ModelSelection` derives the admissible-hypothesis flag
from data.  The weld:

* **`refined_admissibleSet_eq_refineBy`** — the refined admissible set *is*
  `refineBy` of the prior fibre by the observation event `agreeEvent e m y`;
* **`exact_agreeEvent_eq_event`** — for the exact instrument that event is
  literally `event (traceChannel e) y`.  Instrument tolerance is precisely the
  gap between a channel event and a general event;
* `refineAll_observations` — a sequence of observations is iterated refinement;
* `refined_refines_prior`, `truth_survives_kernel`;
* `identical_traces_are_a_persistent_collision` — the lane's
  `data_cannot_separate_identical_traces` as `collision_persists_of_constant`;
* `coarser_instrument_refines_less` — tolerance is paid for in fibre width;
* `refutation_empties_the_fibre` — an observation nothing predicts empties the
  fibre, and `determines_empty` then closes every consumer question
  *vacuously*: refutation of the family, not identification inside it.

---

## 3. Dependency and provenance map

```
Mathlib
  └── Integration.Kernel.ResidualFibre        (no project dependency)
        └── Integration.Kernel.Probe
              └── Integration.Kernel.Merge
                    └── Integration.Kernel.Authority
                          └── Integration.Kernel.Reopen
                                └── Integration.Kernel.Loop
                                      ├── Instances.ParameterRegion  (+ Integration.Experiment.ParameterRegion)
                                      ├── Instances.CollectiveAction
                                      └── Instances.Distribution
                          Instances.Translation   (← Reopen)
                          Instances.Assay         (← Probe)
                          Instances.ObservationalEquivalence
                              (← Probe, + Integration.Experiment.ObservationalEquivalence)
                          Instances.ModelSelection
                              (← Probe, + Integration.Experiment.ModelSelection)

Integration            imports all of the above
Integration.AxiomAuditKernel   #print axioms for all of them
```

Provenance of each statement:

* **From the request's description of the open branches** — the *shapes* the
  kernel had to express: residual refinement and its two refusals; the merge-mode
  distinction; the physical/reported/believed layering; the non-weakening rule;
  edge-indexed reopening; the outcome-adaptive branch rule; the AND-node
  vacuity bug; the four distributions; option-cone expansion; the productive
  join criterion; path-dependent reception. Each was restated as a Lean
  proposition **here** and proved or refused **here**; none is imported from
  anywhere.
* **From the tracked tree** — `Integration.Experiment.ParameterRegion` is the
  only pre-existing lane the kernel is welded to, and the weld is an equality,
  not an analogy.
* **Nothing** is inferred from shared vocabulary, and no Agda module was read,
  rechecked or modified.

---

## 4. Honest frontier — exactly what is *not* proved

1. **Termination is finite-space only.** `responsive_policy_closes` needs
   `Finite Ω` and a strictly discriminating probe at each turn. There is no
   termination statement for infinite possibility spaces, no rate, and no
   treatment of a policy that must *search* for a discriminating probe.
2. **Probes are total functions.** Nothing models cost of execution,
   feasibility, latency, failure to run, or noisy read-outs. The `Distribution`
   instance shows why cost cannot be the ranking criterion, but no admissibility
   *ordering* is defined.
3. **Receipts and guards are opaque `Prop`s.** `provedJoin` and `guarded` take
   the receipt/guard as given; nothing checks a proof object, a signature, or an
   authority. `Authority` models authority only as the non-weakening side
   condition.
4. **Reopening has no recomputation semantics.** `closedAfter` says which
   certificates survive a revision; nothing re-derives the reopened ones, and no
   fixed-point of reopen-then-rebuild is proved.
5. **The merge layer is set-valued only.** Merging combines residual fibres; it
   does not merge *derivations*, so "same fibre, different provenance" is
   representable (`Reopen.Origin`) but the merge operations ignore it.
6. **No lane other than the parameter region is welded by equality.** The other
   four instances are faithful *instantiations* of the kernel on their own toy
   carriers, not identifications with an existing corpus lane. Extending the
   `compatible_eq_refineAll`-style weld to the model-selection, coverage and
   Bayes lanes is the obvious next step and is not done here.
7. **No cross-language transport.** Everything is Lean. Restating the kernel in
   Agda and checking it there remains open.
8. **The adaptive strategy is a two-coordinate table.** `strategy` is
   characterised but not connected to a proof that its `refine`/`merge` choices
   are optimal in any sense.

---

## 5. Claim boundary

`Ω` is an arbitrary type of possibilities; a channel is an arbitrary function; a
"programme" is four pairs of rationals; an "assay" is a two-bit space; a
"reception path" is a composite of two functions on two bits. No theorem in this
round is a claim about chemistry, medicine, law, labour, history, Indigenous
knowledge, any physical theory, or the state of any external repository. No
theory-of-everything claim is made or implied: what is proved is that six
distinct-looking lanes can be phrased in one refinement calculus, and which of
their slogans survive as theorems and which are refuted as witnesses.
