# Ingestion and consolidation round

This round did three things: mined the supplied handoff archive and deleted it,
promoted the material in it that survives review into the built Lean libraries,
and turned the promotion policy itself into checked theorems.

Nothing in this round touches Yang–Mills or Navier–Stokes material; paths under
those names were filtered out of the ingest and are recorded below as skipped.

---

## 1. What came out of the archive

The attachment was a 474 MiB tarball holding two trees: a snapshot of the Agda
repository, and a content-addressed store of 55 earlier handoffs (32 337 unique
blobs, indexed by a manifest and eight JSON Lines record shards).

### Agda

| | count |
|---|---|
| Agda modules in the snapshot that already matched the tracked tree byte-for-byte | 13 678 |
| new module paths ingested | 278 |
| tracked modules replaced by a newer version | 27 |
| further modules recovered from the content store (paths absent from both trees) | 23 |
| Yang–Mills / Navier–Stokes paths skipped | 62 |

`Agda/` now holds 14 019 modules.  The newly ingested lanes are, by size:
`DASHI/Cognition/PNF` (33), `DASHI/Physics/Closure` (30), the Bishop
constructive-analysis group recovered from the store (21, under
`DASHI/Analysis` and `DASHI/Foundations`), `DASHI/Culture` (the Ital, witch
history, John Anthony Brown and Two-Eyed-Seeing tranches), `DASHI/Geology`
(the salt lane), `DASHI/Governance`, `DASHI/Chemistry`, the 2026 mathematics
claim-audit modules and a batch of `*Validation.agda` regressions, plus updated
`Everything` aggregates for Core, Culture, Reasoning, Biology, Chemistry,
Governance and Ontology.

**Authority:** no Agda toolchain exists in this environment, so *no Agda module
was typechecked here*.  Ingesting a module is not evidence that it checks; that
is exactly the distinction §3 formalises.

### Lean

Of the 2 472 distinct Lean blobs in the store, 370 were already in the tracked
tree byte-for-byte.  After dropping Yang–Mills and Navier–Stokes paths and
keeping, for each logical module path, only the copy from the most recent
handoff, 2 427 files were materialised under `Lean/Imported`, with
`Lean/Imported/INGESTION_INDEX.csv` listing each path and the date of the
handoff it came from.  Twenty-two of those were then either promoted (§2) or
deleted as strictly older copies of tracked modules; a second, content-level
dedupe (identical bytes reachable by more than one path) removed a further 998;
eight files were removed because their paths had escaped the Yang–Mills filter
(`ym-mass-gap-lean-verification/`, an Eriksson lakefile/oracle pair importing
`YangMills.*`, and four Agda transcriptions naming the mass gap); and 58 were
moved out into the new `Promoted` library (§2.1).  `Lean/Imported` now holds
**1 341 files**.

Four further archives were found already inside the project, under
`Lean/outputs/aristotle_mirror_waves/wave1/results/`.  They were unpacked and
diffed by content against the whole tracked tree: of their 250 distinct Lean and
Agda blobs, 245 were already present byte-for-byte and the remaining five were
Yang–Mills and Navier–Stokes files, which are outside this cutset.  They
therefore carried nothing to ingest, and they too were deleted.

The archives, the extraction trees and every tarball hash, blob shard and member
path were then **deleted**.  What is kept is the source and the date; the
plumbing is gone.

The larger blocks still sitting in `Lean/Imported` — awaiting review, not
promoted, and not built — are, after the dedupe and the promotion, the
Riemann-analytic lane, `Zeta23Bridge`, the Monster Lean shards, the earlier
`RequestProject` epistemic/Wikidata trees and the Lean transcriptions of Agda
modules under `AgdaCheck`/`AgdaVendor`.

---

## 2. What was promoted into the built libraries

Seven Lean modules and two updated aggregates were found in the ingested
material, absent from the tracked tree, and **compile unchanged in this
toolchain**.  They are now part of the `Synthesis` library, imported by
`Synthesis.lean` and audited by `Synthesis.AxiomAudit`:

| module | what it settles |
|---|---|
| `Synthesis.PhysicsInterfaces` | the gauge, spin and unitary interface records constrain nothing: explicit countermodels |
| `Synthesis.SpinCoverBridge` | the quaternion cover `Q8 → V4` is genuinely two-to-one (`8 = 2·4`, every fibre a pair) and instantiates the spin interface with real content; the continuous-cover record is inhabited with every obligation set to `True` |
| `Synthesis.CircleCover` | a *continuous* double cover: squaring on the circle group is a two-to-one continuous homomorphism of an infinite group |
| `Synthesis.InferenceFibre` | the "statistical" decision surface is exactly a mask detector: fail-to-reject iff the carrier is the Boolean indicator of its support mask |
| `Synthesis.ExponentFibre` | exponent vectors over the fifteen-prime base; the residue `maskProduct m + 1 ≡ 1` proved for every mask and every prime it keeps, replacing three numeral checks |
| `Synthesis.MonsterOrder` | the order numeral's prime factors are exactly the fifteen base primes, and its radical is the full mask product (no group is constructed) |
| `Synthesis.RelationSeam` | the Loom bucket/root classifiers as a strict refinement, with promotion provably unconstrained by the bucket |

A build regression was also repaired: the `AgdaMirror` library glob had reverted
to `AgdaMirror.*`, which pulls in a root aggregate importing an excluded module,
so `lake build` failed before elaborating anything.  It is back to
`AgdaMirror.+`, as its own comment in `lakefile.toml` documents.

### 2.1 The `Promoted` library

Every file under `Lean/Imported` was then put through a mechanical classifier,
`scripts/promotion_status.py`, which records for each one the rung of
`Integration.CorpusPromotion.Stage` it actually reaches.  The bar is deliberately
crude and entirely checkable: a file is *attempted* only if it imports nothing
but `Mathlib` (otherwise it needs a library root that does not exist here), and
it *elaborates* only if `lake env lean` exits zero in this toolchain.  A file
that elaborates but contains `sorry` is filed separately, because elaboration is
not a proof.  The result is `Lean/Imported/PROMOTION_STATUS.csv`:

| rung | files |
|---|---|
| `wired` (built by the `Promoted` library) | 58 |
| `elaborates` (clean here, held out of the library) | 4 |
| `elaborates-with-sorry` | 15 |
| `fails` (error in this toolchain) | 244 |
| `not-attempted` (needs a non-Mathlib library root) | 1 078 |

The 58 in the first row are files that elaborate cleanly *and* contain no
`sorry`, no `axiom`, no `native_decide` and no `@[implemented_by]`.  They have
been moved to `Lean/Promoted/` and are now a default build target, the new
`Promoted` library in `lakefile.toml`: 24 modules of the older `RequestProject`
tree (balanced ternary, `GF27`, the Ogg primes, the Hecke-23 and Pascal-tower
lanes, the epistemic observer/trit pair, the Wikidata reachability pair, …),
nine of the Riemann-analytic lane, four of `Zeta23Bridge`, sixteen leaves of the
`zeta23` reference tree, one each from the Monster, moonshine and Tao lanes and
two from the full-stack architecture lane.

The four in the second row elaborate but are deliberately held back, and the
reason is recorded per file: two prove by `native_decide` (so their theorems rest
on the compiler's evaluator, `Lean.ofReduceBool`, not on the kernel), one
declares an `axiom` of its own (univalence), and one is a Monster/moonshine file
that also uses `native_decide`.  Keeping them out is what makes the claim "no
module of `Promoted` uses `sorry`, an axiom or `native_decide`" a checkable one.

The library's own docstring states the limit of what this means: promotion here
is the rung `elaborates` → `wired` and nothing further.  These modules have not
been reviewed against a source, no statement-correspondence receipt is claimed
for them, and their theorem names are the names their authors gave them.  Being
in a build target means the kernel accepts the file; it means nothing else.

---

## 3. New theorems this round

Three new modules, all sorry-free and axiom-audited to subsets of
`{propext, Classical.choice, Quot.sound}`.

### `Integration.RecordConstraintAdequacy` — one owner for the audit pattern

The corpus had found the same defect independently in the cuisine ledgers, the
publication and carrying-capacity records and the three physics interfaces: a
field whose name states a property and whose type imposes nothing.  This module
owns the pattern.

* `Adequate Contract Intended`, `Countermodel`, `Countermodel.not_adequate`.
* `adequate_iff_no_countermodel` — adequacy **is** the absence of a
  countermodel, so adversarial inhabitance is a complete criterion.
* `empty_contract_is_adequate` — soundness alone is worthless; hence `Audited`,
  which additionally demands a witness with the property, and
  `empty_contract_not_audited`, showing the two requirements are independent.
* `FlagFree`, `free_flag_not_determined`, `freeFlagCollision`,
  `free_flag_not_a_function_of_data` — a free field is not determined by the
  record's data, and (as a collision) no downstream reading repairs it.
* `Ledger`, `ledger_no_information` — the `Bool`-plus-equation pattern
  generalised: uniquely inhabited, so it separates nothing.  The cuisine result
  is now an instance of this.

### `Integration.CorpusPromotion` — the ladder this round's ingest needs

`Stage` = `ingested < elaborates < wired < audited < cited`, linearly ordered;
`Promotion` = a downward-closed set of reached rungs.

* `Promotion.reached_of_le` — reaching a rung implies the earlier rungs.
* `no_upward_implication`, `notAdequate`, `every_rung_but_cited_is_strict` — and
  no rung implies the next, for every rung below the top.
* `presence_does_not_determine_elaboration`,
  `no_store_reading_gives_status` — the load-bearing one: an artefact is a source
  *plus* the environment it elaborates in, the store sees only the source, so
  elaboration status does not factor through the store and no digest, index or
  report computed from the stored text recovers it.
* `store_membership_is_a_ledger` — "this content is in the store" is a ledger:
  true, and empty of information about the content.

### `Synthesis.ContractRepair` — the three physics contracts repaired

For each interface: a strengthened contract, a proof that the earlier
countermodel is refuted, a proof that the repair is still inhabited, and the
boundary.

| interface | repair | consequence proved | countermodel refuted |
|---|---|---|---|
| gauge | an admissible state must be exhibited | `substantive_forces_SM`: some state picks `SM` | `nonSM_witness_impossible`: the empty admissibility predicate cannot be completed |
| spin | the field asserts the fibre count | `DoubleCover.not_injective`, `DoubleCover.surjective`; inhabited by `q8DoubleCover` | `injective_cover_not_double`, `trivial_spin_not_double` |
| unitary | the inner product must separate | `unitary_real_is_pm_id`: over `ℝ` with `⟪x,y⟫ = xy` a unitary map is `±id` pointwise | `trivialIPS_not_separating`; `scaling_not_unitary` |

`substantiveGaugeAudited`, `spinRepairAudited` and `unitaryRepairAudited` file
each repair as an `Audited` contract in the sense of §3.1 — sound *and*
witnessed.

**Boundary.**  `substantive_still_permits_non_SM_elsewhere` records that the
gauge repair buys non-vacuity, not gauge uniqueness; `V4Rotation` is the Klein
four-group and not `SO(3,1)`, and `Q8` is not `Spin(3,1)`.  No physical claim is
made anywhere in this round.

---

## 4. Dependency map of the new work

```
Integration.CoordinateSufficiency
        │
Integration.FactorisationCollision ──────────┐
        │                                    │
Integration.RecordConstraintAdequacy ───► Integration.CorpusPromotion
        │                                    (Stage, Promotion, Artefact)
        └────────────────► Synthesis.ContractRepair
                                    ▲
AgdaMirror.GaugeGroupContract ──────┤
AgdaMirror.SpinEmergence ───────────┤
AgdaMirror.QuantumUnitary ──────────┤
Synthesis.PhysicsInterfaces ────────┤   (the countermodels being repaired)
Synthesis.SpinCoverBridge ──────────┘   (the witness for the spin repair)
```

Aggregates: `Integration.lean` (entries 51ak, 51al) and `Synthesis.lean`;
audits: `Integration.AxiomAudit`, `Synthesis.AxiomAudit`.

---

## 5. Honest frontier

Exact obligations left open by this round, in the order they would be attacked.

1. **The ingested Agda is unverified here.**  305 + 23 modules were brought in
   and not typechecked, because no Agda toolchain is available.  Their status is
   `ingested`, rung 0 of §3.2, and nothing in the corpus should cite them as
   theorems until an Agda run is possible.
2. **1 341 Lean files remain unpromoted**, none of them built, and the
   classifier of §2.1 now says exactly why.  4 of them elaborate cleanly but are
   held out of the library because they use `native_decide` or declare their own
   axiom.  15 more elaborate but contain `sorry`, so they are proofs of nothing.  244 **fail** in this toolchain — those are the
   real compatibility debt, and the first error line of each is recorded in
   `PROMOTION_STATUS.csv`.  The remaining 1 078 have never been attempted because
   they import a library root that does not exist here; the Monster shards and
   the `AgdaCheck`/`AgdaVendor` transcriptions are almost all of that block.
3. **The repairs are of the *mirror* records, not of the Agda sources.**
   `Synthesis.ContractRepair` strengthens the Lean transcriptions.  Transporting
   the repair means editing the Agda records and rechecking them, which this
   environment cannot do; until then the Agda side still admits the
   countermodels.
4. **The unitary repair is one-dimensional and real.**  `unitary_real_is_pm_id`
   is proved for `ℝ` with the product pairing.  A complex, multi-dimensional
   instance — where "unitary" should give a genuine isometry group — is not
   done.
5. **The spin repair is finite.**  `DoubleCover` is stated for a `Fintype`
   source via fibre cardinality.  The continuous statement (a covering map of
   topological groups with two-element fibres) is available in
   `Synthesis.CircleCover` for the circle only, and is not connected to the
   `DoubleCover` structure.
6. **The promotion ladder is now observed, but only to rung `wired`.**
   `scripts/promotion_status.py` decides `ingested`, `elaborates` and (by
   construction of the `Promoted` library) `wired` mechanically, and
   `Lean/Imported/PROMOTION_STATUS.csv` is its output.  The two rungs above —
   `audited` and `cited` — are still policy: nothing in the repository certifies
   that a promoted module's statement corresponds to the source it came from, and
   the classifier makes no attempt to.  That is the gap `Integration.CorpusPromotion`
   was written to keep visible, and it stays open.
7. **Free-field auditing is not yet applied module-by-module.**  The owner
   exists; the corpus's remaining records have not been swept against it.

---

## 6. Bridges: `Integration.BridgeStatus`

One further owner was added after the ingest, for the discipline the whole round
depends on.  The corpus already proves that equal cardinality gives no canonical
identification (`Spine.EqualCardinality`) and already owns the commuting square
(`Integration.StructureMorphism`).  What was missing is the object in between: a
**bridge that declares what it preserves**.

A `System` is a carrier with a dynamics and an observation.  A `Bridge` is a map
*together with* `preserves_obs` and `preserves_step`, so it cannot be constructed
from a map, and never from a shared name or a shared size.  On top of that:

* `isEquivalence_iff` and `not_equivalence_and_quotient` — the four statuses
  (equivalence / refinement / quotient / incompatible) are related by proof, not
  by convention;
* `IsQuotient.state_not_recoverable` — a quotient bridge *exhibits* its loss, as
  a `FactorisationCollision.Collision`: no reading of the target returns the
  source state;
* `Bridge.transport_orbit` — the dynamics law iterates, so a bridge transports
  whole orbits and hence reachability;
* `no_bridge_of_fixed_point_mismatch`, `no_bridge_of_observation_mismatch` — the
  incompatible status with a proof attached: a fixed point on one side and none
  on the other refutes *every* map, whatever else it preserves;
* `bridge_existence_is_directional` — and the sharpest of them.  Take two systems
  on the *same* carrier type, with the *same* cardinality and the *same*
  observation language, differing only in their dynamics.  A bridge exists one
  way (`flipToFixed`, the constant map) and provably cannot exist the other
  (`map_without_laws_is_not_a_bridge`).  So "these two correspond" is not a
  symmetric relation, and a bridge found in one direction licenses nothing in the
  other.

All ten headline results are sorry-free and audited in
`Integration.AxiomAudit`; their axiom profiles are empty, `[propext]`, or
`[propext, Classical.choice, Quot.sound]`.
