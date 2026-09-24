# Cuisine ↔ corpus: the four-level bridge map

This document reconciles two earlier statements in this repository:

* `CUISINE_DEPENDENCY_MAP.md` §2.1 / §5.2(6) — *"cuisine has no formal link to
  the Monster, MDL, moonshine, cubical, supervoxel, trit-algebra or
  dialectic-loom material; `Base369` is module-reachable only"*; and
* `CUISINE_TOE_TRANSPORT.md` — *"cuisine carries a proved type-level transport
  into the trit algebra, the ternary fibre over the fifteen supersingular
  primes, the `369` carrier, the MDL prime-subset code and the supplied
  moonshine numerals"*.

Both are accurate about different questions, and the confusion between them is
exactly the confusion this map is designed to prevent.  The first is a statement
about the **Agda import graph of the supplied cuisine lane**: what the cuisine
records *store*.  The second is a statement about **maps proved in Lean between
the carriers those records use and the carriers of the other lanes**.  A lane
can be absent from the import graph and still be the target of a proved
transport, and a lane can be present in the import graph and contribute nothing
but a `String`.

So the single-sentence verdict is replaced by a four-level scale, applied lane
by lane, with the evidence for each entry named.

| level | meaning | what would be dishonest |
|---|---|---|
| 1 `vocabulary` | the lanes share words only: no import path, no shared type, no map | calling a shared word a connection |
| 2 `recordDependency` | a cuisine record really stores a value of the other lane's type (or reaches it through the Agda import graph), but the stored value carries no information | calling a canonical record field a theorem |
| 3 `sharedType` | both lanes instantiate one implementation-level type or interface defined here, so their statements are comparable | calling comparability a transport |
| 4 `provedTransport` | a checked map or equivalence between cuisine data and the other lane's carrier, preserving the structure at issue | over-reading what the map preserves |

The scale is also formalised, in `Lean/Cuisine/FourLevelLedger.lean`:
`bridgeLevel : TargetLane → BridgeLevel` is the assignment below, and
`LedgerWitnesses` / `fourLevelLedger` require the actual theorem for every
level-4 entry and the actual proved obstruction for every lower entry.  The
level assignment itself is a judgement and is labelled as such; what is machine
checked is that no entry is *unsupported*.

---

## 0. Provenance of the sources

Three Lean trees are in play, and they are kept distinguishable:

| tree | files | provenance | build status |
|---|---|---|---|
| `Lean/AgdaMirror/` | 107 | Lean mirrors of Agda modules, returned by the earlier synthesis run (project `bf6411b6`) | now a default build target (`AgdaMirror` library, submodule glob) |
| `Lean/Synthesis/` | 12 | the cross-domain finite synthesis spine from the same run | default target, unchanged this session |
| `Lean/Cuisine/` | 31 | this line of work: the cuisine lane and its bridges | default target |

Two integration fixes were needed and made:

* `Lean/AgdaMirror/{Core,Algebra,Analysis}.lean` had their module docstring
  *above* the `import` block, which Lean rejects; the docstring was moved below
  the imports.  No mathematical content changed.
* The `AgdaMirror` library glob is now `AgdaMirror.+` (submodules only).  The
  root aggregate `Lean/AgdaMirror.lean` imports `AgdaMirror.Physics.YangMills`,
  which is excluded from this cutset by the YM/NS filter and is deliberately
  **not** reinstated.  With that one aggregate excluded, all 107 mirror modules
  build.

`lake build` (default targets `Synthesis`, `Cuisine`, `AgdaMirror`) completes:
8182 jobs, no `sorry`, no `axiom`, no `native_decide`.  Agda is still not
installed in this environment, so every Agda-side statement below is source
reading (or a mechanical computation over the import graph), never a
typecheck.  Lean mirrors are labelled as mirrors.

No Yang–Mills or Navier–Stokes material is touched or referenced.

---

## 1. The Agda import evidence (level-2 facts)

Computed mechanically over the supplied Agda sources: the import closure of the
fourteen `DASHI.Culture.Cuisine.*` modules is **30 modules**.  It contains:

```
Base369                                        <- DASHI.Interop.SensibLawResidualLattice
                                               <- DASHI.Interop.SweetgrassCarrierSpine
                                               <- DASHI.Culture.Cuisine.SituatedMoleWorld
DASHI.Foundations.Base369Nat                   <- Base369 <- (as above)
DASHI.Interop.SweetgrassCarrierSpine           <- DASHI.Culture.Cuisine.SituatedMoleWorld
DASHI.Interop.SensibLawResidualLattice         <- SweetgrassCarrierSpine <- SituatedMoleWorld
DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge
                                               <- DASHI.Culture.Cuisine.SituatedMoleWorld
DASHI.Culture.KnotWeaveTopologyCultureBridge   <- DASHI.Culture.Cuisine.SituatedMoleWorld
```

and it contains **no** module whose name mentions Monster, moonshine, MDL,
Cubical, supervoxel, trit, loom, codec or dialectic.  That is the whole of the
level-2 evidence, and it is why the earlier report's sentence was written.  Note
what it does *not* say: it says nothing about whether the carriers of those
lanes admit maps to cuisine carriers.

---

## 2. The map, lane by lane

### Level 4 — proved transport

| lane | the map | the theorem(s) | what it does *not* say |
|---|---|---|---|
| **Monster prime base** | `umamiFabric : ℕ → Fabric`, cuisine intensity ↦ ternary section over the 15 supersingular primes | `Cuisine.UmamiTransport.umamiFabric_compose` (homomorphism), `umamiFabric_surjective`, `supportMask_umamiFabric_maskIntensity`, `maskIntensity_injective` | nothing about the Monster group; `SSP` is a 15-element set of primes |
| **Moonshine numerals** | the trivector mask's cuisine intensity | `maskIntensity_trivector` (`= 196882`), `repDim_eq_maskIntensity_succ`, `jCoefficient_eq_maskIntensity_add_two`, `NineSheet.repDim_eq_ten_mul_nine_sheet` | these are numeral identities about supplied constants; no representation, no `j`-invariant |
| **MDL two-part code** | the prime-subset model on transported intensities | `Cuisine.MdlPrimeModel.mdl_optimal_iff`, `mdl_optimal_of_maskIntensity`, `mdl_optimal_length` | the supplied Agda `MDL` files are an interface with no theorem content; the optimality statement is new here |
| **`Base369` tone** | `hexToSafety`, the mod-3 descent of the hexadic residual ladder onto cuisine safety verdicts | `Cuisine.SeveritySeam.hexToSafety_surjective`, `hexToSafety_rotate`, `hexSeverity_seam`, `severity_const_of_monotone_perm` | the fail-closed *order* still does not transport, and that is proved to be forced |
| **Trit algebra** | `knotWeaveEquivTrit`, `knotWeaveFabric` | `Cuisine.KnotWeave.knotWeaveEquivTrit_rotate`, `knotWeaveFabric_rotateField`, `knotWeave_rotation_is_seasoning`, `exists_intensity` | the guard's eight *named* "triad surfaces" are still not trits: `HyperfabricGuard.no_injective_trit_labelling` |
| **Dialectic (stage action)** | the sixfold stage action on the fabric | `Cuisine.UmamiTransport.dialectic_stage_is_seasoning`, `umamiFabric_season_iter` | this is the `Stage6` action, *not* the loom relation algebra (see level 3) |
| **Codec kernel** (new) | `umamiCodec = fabricKernelEquiv ∘ umamiFabric : ℕ → (Fin 15 → ZMod 3)` | `Cuisine.CodecTransport.umamiCodec_compose` (the law is the **affine** `x+y+1`), `umamiCodec_surjective`, `umamiCodec_selfBlend` (`x ↦ -x+1`), `blendDoubleOrbits_eq/_value` (`= orbitCount 15 = 7174454`), `fabricShift_conjugates` | self-seasoning is **never** literally the codec inversion: `fabricXor_self_ne_fabricInv`.  The two involutions are *conjugate*, which is why the orbit counts agree; they are not identified |
| **Supervoxel refinement** (new) | the cuisine transport as a depth-15 clopen-ball projection; cuisine neutrality constraints as supervoxel constraints | `Cuisine.SupervoxelClopen.umamiFabric_eq_iff_ball`, `neutrality_refines_iff` (refinement order = Monster mask order), `card_neutralFabric` (`3^k` admissible shadows) | the Agda's *psychological* instance is not mirrored: its hidden-state fields are uninterpreted and its two refinement lemmas are `cong`/`trans` bookkeeping |

### Level 3 — shared implementation type, no transport

| lane | what is shared | the obstruction that keeps it at level 3 |
|---|---|---|
| **Dialectic loom relation algebra** | the loom classifiers, the cuisine publication classifiers and the supervoxel constraint interface are three instances of one interface: `Cuisine.SupervoxelClopen.ConstraintSystem` / `FineExtendsCoarse`.  Proved: `LoomBridge.rootOfBucket_bucketFor` (bucket determines root), `loomBucket_refines_root`, `publicationRisk_refines_decision`, and non-atomicity in all of them (`loomRoot_not_atomic`, `publicationDecision_not_atomic`, `cuisineNeutrality_not_atomic`, `no_atomic_ball`) | `LoomBridge.no_free_order3_root_preserving`: no fixed-point-free order-three permutation of the nine relation types preserves the root classifier (the `invalidates` class has two elements, `loom_root_fibre_sizes` = 3,2,3,1).  So the nine relation types do **not** carry the nonary rotation of `Cuisine.NonaryAction`; the shared numeral `9` is not a map |
| **Klüver spiral** | the four-element form-constant carrier supplies a referent for the guard's `spiral` surface (`Cuisine.SpiralCarrier`, `SurfaceInterpretation.spiral_matched`) | `SpiralCarrier.no_injective_klueverForm_to_trit`: four form constants do not inject into three digits, so `spiral` does not join the ternary spine.  The real-analytic spiral geometry under `Lean/DASHI/Klüver's Form Constants_aristotle/` is not a finite carrier and is not linked to the spine by anything proved |

### Level 2 — stored record dependency, no information

| lane | what is stored | the audit |
|---|---|---|
| **Hyperfabric body-memory bridge** | `SituatedMoleWorld` stores `hyperfabricBridge`, `hyperfabricPowerAxes` and a canonicity proof | `Cuisine.HyperfabricGuard`: the stored facet type is a singleton (`Unique`), the eight triad surfaces are separated only by their names, exactly one of seven interpretive routes is admissible (`exists_unique_admissible`) |
| **Sweetgrass motif fabric** | reached through the single `String` field `sweetgrassAttribution` | `Cuisine.SweetgrassSpine`: 13 of 35 motifs are realised by types in this repository; `sweetgrass_itself_unrealised` — the motif the record actually names is not one of them; two anchors are declared and never used, one of them `anchorMonsterMoonshineSSPQuotient` |

Note that `Base369` sits in the import graph at level 2 (a `String` attribution
chain, as the earlier report said) **and** at level 4 (via `hexToSafety`).  The
two facts are about different things; both are recorded.

### Level 1 — vocabulary only

| lane | evidence |
|---|---|
| **Cubical** | the 30-module cuisine import closure contains no cubical module; the Agda cubical material (`Agda/cubical`, `DASHI.Cubical.UnificationCandidate`) is reachable from neither the cuisine lane nor any Lean module here, and no cubical type appears in the Lean trees.  Nothing beyond the word is shared |

---

## 3. What changed this session

New, all sorry-free and wired into the `Cuisine` library, its aggregate module
and its axiom audit:

| module | lines | content |
|---|---|---|
| `Lean/Cuisine/SupervoxelClopen.lean` | 399 | the supervoxel interface mirrored (`ConstraintSystem`, `FineExtendsCoarse`, `AdmissibleRegion`, preorder laws); `BTBranch ≃ Trit`; the checked ternary clopen-ball instance `ternaryBallSystem`; `no_atomic_ball`, `children_disjoint`, `ball_complement_union`; the cuisine constraint system with `neutrality_refines_iff` and `card_neutralFabric`; `umamiFabric_eq_iff_ball`; `cuisine_supervoxel_not_atomic` |
| `Lean/Cuisine/TransportKernel.lean` | 192 | `umamiFabric_eq_iff`, `primePow_dvd_self` (the supersingular part divides), `umamiFabric_eq_zero_iff` (the kernel, exactly), and the two special cases as corollaries |
| `Lean/Cuisine/CodecTransport.lean` | 205 | `umamiCodec` and its affine law, `umamiCodec_selfBlend`, `fabricXor_self_ne_fabricInv`, `fabricDouble_involutive`, `blendDoubleOrbits_eq/_value` |
| `Lean/Cuisine/LoomBridge.lean` | 210 | `rootOfBucket_bucketFor`, the loom and publication constraint systems, four non-atomicity results, `loom_root_fibre_sizes`, `no_free_order3_root_preserving` |
| `Lean/Cuisine/FourLevelLedger.lean` | 206 | the typed four-level map and its witness bundle |

Two `Bool`-ledger idioms of the Agda supervoxel lane are now theorems rather
than declarations:

* `publicZeroIsAtomic ≡ false` ⟶ `no_atomic_ball` (for the ternary ball
  system), `cuisineNeutrality_not_atomic`, `loomRoot_not_atomic`,
  `publicationDecision_not_atomic` — one definition (`Atomic`) discharged in
  four lanes;
* `SamePublicZeroDifferentDynamics` (an inhabited record) ⟶
  `cuisine_supervoxel_not_atomic`, an explicit pair of distinct cuisine
  intensities in one depth-15 ball.

---

## 4. Frontier: the exact missing transport lemmas

Stated so that nothing above is over-read.  Items 1–2 and 5–8 carry over
unchanged from `CUISINE_TOE_TRANSPORT.md` §4; items 3, 4, 9–12 are new or
sharpened.

1. **The `3 · 5` indexing of the supersingular base is a choice.**
   `NineSheet.sspToneTaste` is one of `15!` bijections; no canonical `3 × 5`
   structure on that base is defined anywhere in the corpus.
2. **The moonshine identities are numeral identities.**  Nothing here defines
   the Monster group, a representation of it, or the `j`-invariant.
3. **The kernel of the transport is now described** —
   `Cuisine.TransportKernel.umamiFabric_eq_zero_iff` proves exactly
   `umamiFabric u = fabricZero ↔ ∃ c d, 0 < c ∧ 0 < d ∧ u + 1 = c ^ 3 * d ∧ ∀ p : SSP, ¬ (prime p ∣ d)`,
   and `umamiFabric_eq_iff` gives the induced congruence.  What is *still*
   missing is the packaging: the quotient of the cuisine monoid by that
   congruence is not constructed, and the induced monoid isomorphism onto the
   affine codec structure is therefore not stated.
4. **The ball system is not shown to be a metric or a topology.**
   `ternaryBallSystem` supplies the containment/covering laws and
   `ball_complement_union` supplies the combinatorial content of clopenness, but
   the ultrametric on `TritStream` and the statement that `Cyl` generates a
   topology in which each ball is clopen are *not* proved.  Missing lemmas:
   `dStream : TritStream → TritStream → ℝ≥0` with the ultrametric triangle
   inequality, and `IsClopen {p | Cyl d c p}` for the product topology.
5. **Nothing transports the fail-closed order** (proved forced by
   `severity_const_of_monotone_perm`).
6. **`spiral`'s referent is finite; its geometry is not linked.**
7. **Twenty-two Sweetgrass motifs remain unrealised.**  `motifSupervoxel` now
   *has* a candidate referent (the constraint/ball interface of this session),
   but the realisation table was deliberately **not** edited: deciding that a
   motif name denotes a particular type is a naming judgement, and the ledger
   keeps naming judgements out of the theorem layer.
8. **The two order-three base symmetries are still unrelated**; the group they
   generate inside `Sym(SSP)` is not computed.
9. **The loom lane has no positive transport.**  What is missing, exactly: a map
   `LoomRelationType → C` into some carrier of the ternary spine that
   intertwines *some* declared loom operation with a spine operation.  The
   source declares no operation on relation types at all — only classifiers —
   so this obligation may well be unsatisfiable as stated, and
   `no_free_order3_root_preserving` rules out the most tempting candidate.
10. **The codec orbit-count agreement is now explained**, not merely computed:
    `Cuisine.CodecTransport.fabricShift_conjugates` exhibits the conjugating
    equivalence (translation of codec coordinates by the neutral digit) and
    `blendDoubleOrbits_eq_fabricOrbits` derives the equality of the two
    quotients from it.
11. **The cubical lane has no bridge and no obstruction.**  Level 1 is a
    negative *observation* (no path in the import graph), not a theorem; if a
    cubical carrier were mirrored in Lean, the question would reopen.
12. **The Agda side is unchecked and unedited.**  All new modules are Lean.
    Transcribing `neutrality_refines_iff`, `umamiFabric_eq_iff_ball` and
    `umamiCodec_compose` back into Agda remains open and cannot responsibly be
    attempted without a typechecker.

---

## 5. Boundary

Every carrier named above is a finite set, a list of naturals, or a function
between such.  Nothing here is a claim about food, chemistry, safety, history,
psychology, law, cultural authority, perception, or physics, and no physical or
mathematical theory-of-everything claim is made or supported.  "Hyperfabric"
means sections of a finite fibre over a finite base; "supervoxel" means a
satisfaction relation with a refinement order; "codec" means a finite
balanced-ternary algebra.
