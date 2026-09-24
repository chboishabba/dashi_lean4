# Cuisine ⟶ trit ⟶ fibre ⟶ 369 ⟶ hyperfabric ⟶ Monster: the transport, proved

This document supersedes the headline of `CUISINE_DEPENDENCY_MAP.md` §2.1 and
§5.2(6).  That earlier report was right about what was *then* in the repository
and wrong as a statement about what the material supports.  The corrected
headline is:

> Cuisine is conceptually and record-level connected to the
> hyperfabric / knot-weave / Sweetgrass ontology, and it now also carries a
> **proved type-level transport** into the trit algebra, the ternary fibre over
> the fifteen supersingular ("Monster") primes, the `369` carrier, the MDL
> prime-subset code, and the supplied moonshine numerals.

Everything below is checked: `lake build` builds the `Synthesis` and `Cuisine`
libraries with no `sorry`, no `axiom`, no `native_decide`, and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound` (printed by
`Lean/Cuisine/AxiomAudit.lean` during the build).  Agda is still not installed in
this environment, so no Agda module was typechecked; every Agda-side statement
here is source reading, and the Lean mirrors are labelled as mirrors.

No Yang–Mills and no Navier–Stokes material is touched or referenced.

---

## 1. What was actually missing, and what closes it

The earlier report established two things that remain true:

* the cuisine record's *direct* use of `SweetgrassCarrierSpine` is the single
  `String` field `sweetgrassAttribution`; and
* the hyperfabric guard's words `trit`, `prime`, `dialectic`, … are its own
  enumerated semantic surfaces, not values of the repository's `Trit`, `SSP` or
  Monster types (eight surfaces cannot even inject into a three- or six-element
  carrier: `Cuisine.HyperfabricGuard.no_injective_trit_labelling`).

What was missing was the stronger link: *a structure-preserving map between a
carrier the cuisine lane really has and the implementation-level machinery.*
The negative results above are about the wrong carrier.  The cuisine lane's
genuine algebraic content is not its three-element safety enum; it is the
**umami interaction law**

```
combinedIntensity = g + n + g·n        equivalently   1 + c = (1+g)(1+n)
```

which the Agda record `UmamiBlend` states and `Cuisine.SensoryCore` proves
(`UmamiBlend.succ_combined_eq`).  That is a *multiplicative* law, and the Monster
prime base is a *multiplicative* object (`Synthesis.MoonshineBase.maskProduct`).
Joining them is the transport.

### The chain

```
   cuisine umami monoid                (ℕ, u ⊕ v = u+v+uv, unit 0)
        │  u ↦ u+1                     Cuisine.UmamiTransport.umamiSuccEquiv
        ▼
   (ℕ>0, ×)                            multiplicative monoid of positive naturals
        │  p-adic valuations at the 15 supersingular primes
        ▼
   (ℕ^15, +)                           exponent vectors over the Monster base
        │  mod 3                       "369" reduction
        ▼
   (ℤ/3)^15  =  Fabric                 Synthesis.Hyperfabric: sections of the
                                       balanced-ternary fibre over SSP
```

Composite: `Cuisine.UmamiTransport.umamiFabric : ℕ → Fabric`.

---

## 2. The theorems

All in `Lean/Cuisine/`, all sorry-free.

### 2.1 `Cuisine.UmamiTransport` — the transport itself

| theorem | statement |
|---|---|
| `umamiSuccEquiv`, `umamiSuccEquiv_hom` | the cuisine combination law is the multiplicative monoid of positive naturals, via `u ↦ u+1` |
| `umamiFabric_compose` | **homomorphism**: `umamiFabric (a ⊕ b) = fabricXor (umamiFabric a) (umamiFabric b)` — combining umami loads is `(ℤ/3)^15` addition |
| `umamiFabric_surjective` | **onto**: every one of the `3^15` hyperfabric sections is the shadow of a cuisine intensity (`fabricIntensity` is the explicit preimage) |
| `umamiFabric_cube` | cubes are neutral: the transport is reduction of the cuisine monoid modulo cubes |
| `umamiFabric_season` | composing with the radical intensity `∏p − 1` rotates every fibre: one `Synthesis.Hyperfabric.fabricRot` step |
| `dialectic_stage_is_seasoning` | **the sixfold dialectic acts through the cuisine monoid**: `fabricAct s` is seasoning with `stageIndex s` copies of the radical |
| `supportMask_umamiFabric_maskIntensity`, `maskIntensity_injective` | the Monster mask lattice embeds in cuisine intensities, support recovered exactly |
| `maskIntensity_trivector`, `repDim_eq_maskIntensity_succ`, `jCoefficient_eq_maskIntensity_add_two` | the mask `{47,59,71}` has cuisine intensity `196882`; `+1` is the supplied `repDim = 196883`, `+2` the supplied `jCoefficient = 196884` |
| `factorization_primePow` | the arithmetic core: exponent vectors over fifteen *distinct primes* are read back by factorisation |

### 2.2 `Cuisine.NineSheet` — the `3·5 = 15` shape and `3^9 = 19683`

| theorem | statement |
|---|---|
| `card_supported` | sections supported on `s ⊆ SSP` number `3 ^ |s|` |
| `card_supported_nine`, `card_fabric_split` | a depth-nine sheet has `19683` sections; `3^15 = 3^9 · 3^6` |
| `sspToneTaste` | a chosen bijection `SSP ≃ TriTruth × TasteDimension`: the base in the shape `3 · 5`, the `5` being the cuisine taste dimensions.  Flagged in the source as a *choice*, as for any two fifteen-element sets |
| `card_taste_sheet` | any three of the five taste dimensions carry a depth-nine sheet: `19683` sections |
| `repDim_eq_ten_mul_nine_sheet`, `jCoefficient_eq_ten_mul_nine_sheet`, `repDim_eq_graded` | `196883 = 10·3^9 + 53 = 3^11 + 3^9 + 53`, `196884 = 10·3^9 + 54` — the identities the Agda modules `TernaryMonsterSymmetryCandidateExact` and `MonsterStructuredBulkCarrierExact` state |
| `moonshine_nine_sheet_bridge` | the commuting statement: all of the above against the *same* `N = card` of a depth-nine sheet, with the cuisine intensity on the same line |

### 2.3 `Cuisine.SafetyFabric` — cuisine safety data in the Monster geometry

| theorem | statement |
|---|---|
| `severity_eq_zmod_val` | the fail-closed severity `verified < unknown < rejected` *is* the canonical `ℤ/3` representative of the tone |
| `worst_comm/_assoc/_idem`, `safetyLevel_worst` | fail-closed aggregation is a commutative idempotent monoid = `max` of severities |
| `safetyFabric` | safety fields `SSP → SafetyEvidence` **are** hyperfabric sections |
| `doubtMask_eq_supportMask` | the "not verified" mask of a field is the support mask of its section |
| `doubtMask_worstField` | **fail-closed aggregation is a semilattice homomorphism** onto the Monster mask fibre — in contrast to `Synthesis.Hyperfabric.support_not_hom`, where ternary XOR does *not* descend |
| `dSafety_eq_zero_iff`, `dSafety_not_separating`, `safety_projection_contractive` | the supplied Monster ultrametric and contractive projection pulled back to safety data, with the honest caveat that it is a pseudometric (`unknown` and `rejected` share a doubt mask) |
| `safety_intensity_roundtrip` | safety data has an umami-arithmetic encoding whose hyperfabric shadow is the original doubt pattern |

### 2.4 `Cuisine.SeveritySeam` — the `369` carrier, and one explanation for two facts

Mirrors of `DASHI.Interop.SensibLawResidualLattice` (`SixResidualLevel`,
`sixResidualSeverity`, `hexToSixResidual`, `hexSeverity`, `joinSixResidual`),
plus:

| theorem | statement |
|---|---|
| `hexSeverity_rotate_le`, `hexSeverity_rotate_wrap`, `hexSeverity_seam` | the Agda file's five non-wrap steps and its `rotateHexWrapSeam`, in Lean |
| `severity_const_of_monotone_perm` | **general**: a severity that never decreases along a permutation of a finite carrier is constant along it |
| `exists_severity_seam` | hence any rotation of a non-constant severity has a seam — one explanation for *both* the hexadic wrap seam and `Cuisine.ToneSeparation.no_order_three_monotone_selfmap` |
| `hexToSafety`, `hexToSafety_rotate`, `hexToSafety_surjective`, `hexToSafety_fibre_card` | **positive**: the `369` carrier maps onto the cuisine safety carrier, two-to-one and rotation-equivariantly, via the mod-3 descent `Synthesis.DialecticTone.hexToTri` |
| `safetyLevel_hexToSafety`, `safetyLevel_hexToSafety_wrap` | the two gradings agree mod 3 except at the wrap, where the residual ladder jumps `4 → 9` |

### 2.5 `Cuisine.MdlPrimeModel` — MDL, instantiated

Mirrors of the `Agda/MDL` interface (`CodeLength`, `MdlModel`,
`modelTotalLength`, `Better`, `Lyapunov`, `limit71`), then:

| theorem | statement |
|---|---|
| `primeSubsetModel` | the concrete prime-subset model: parameter = a Monster mask, parameter cost = primes kept, data cost = 2 per uncovered non-neutral point |
| `mdl_lower_bound`, `total_supportMask`, `mdl_optimal_iff` | **the support mask is the unique minimiser of total code length** |
| `mdl_optimal_of_maskIntensity`, `mdl_optimal_length` | for a transported cuisine intensity, the MDL-optimal subset of supersingular primes is exactly the mask it came from, and the optimal length is the number of primes in it |
| `ssp_le_limit71` | the MDL bound `limit71 = 71` is the largest supersingular prime of the base — a numeral identification, recorded as such |

Note on the supplied Agda: `MDL.Core.restrictSafe` and
`MDL.PrimeSubsetModel.subsetBoundedCost` are the identity function on their
hypothesis, so the MDL files are an interface with no theorem content.  The
optimality statement above is new.

### 2.6 `Cuisine.SurfaceInterpretation` — the guard's words, given referents

`interpret : TriadSurface → SurfaceCarrier` sends each of the guard's eight
semantic surfaces to the implementation carrier of the same name, with
`carrierCard_eq` matching the sizes against real `Fintype.card`s
(`Trit` 3, `Stage` 4, `Stage6` 6, `SSP` 15, depth-nine sheet 19683,
`MaskSSP` 32768, `Fabric` 14348907).  `interpret_injective` shows the eight names
denote eight different things.

The table is now **total**: an earlier version recorded `spiral` as having no
referent, which was a gap in the search rather than in the corpus.
`Cuisine.SpiralCarrier` mirrors `Agda/DASHI/Cognition/
KlueverFormConstantProjection`, whose four-element `KlueverForm` has `spiral` as
one of its values, with `hint_unique` / `hintSigmaEquiv` showing the
geometry-hint family is a singleton over each form.  Honest limitations:
`no_injective_klueverForm_to_trit` (four elements do not inject into three, so
`spiral` still does not join the ternary spine) and
`carrierCard_nodup_except_stage_spiral` (`stage` and `spiral` are the one pair
of distinct surfaces that cardinality cannot separate).

### 2.7 `Cuisine.KnotWeave` — the second typed cross-domain dependency

`SituatedMoleWorld` stores *two* bridges as fields.  The hyperfabric one is
audited in §2.6; the other, `DASHI.Culture.KnotWeaveTopologyCultureBridge`, is
audited here.

Negatives, as before: `knotWeaveGate` is constant and `KnotWeaveGuard` is a
singleton (`knotWeaveGuard_unique`), so the admissibility gate carries nothing;
the four lanes and four guards are bare enumerations (`lanes_nodup`,
`guards_nodup`).

But — unlike the eight-name triad-surface vocabulary — this carrier is
*genuinely ternary*, and it does transport:

| statement | content |
|---|---|
| `observe_injective`, `topologicalRole_bijective`, `semanticRole_bijective`, `operator_bijective` | the carrier, the two role families and the operator family are one three-element object |
| `knotWeaveEquivTrit : KnotWeaveCarrier ≃ Trit` | canonical identification with the balanced-ternary digit, fixed by the Agda enumeration order |
| `knotWeaveEquivTrit_rotate` | knot → weave → braid **is** the `369` tone rotation |
| `knotWeaveFabric : KnotWeaveField ≃ Fabric` | knot-weave fields over the Monster prime base *are* hyperfabric sections |
| `knotWeave_rotation_is_seasoning` | rotating every carrier of such a field is, cuisine-side, seasoning the blend with the radical intensity |
| `exists_intensity` | every knot-weave field is the transport of a cuisine intensity, so the previous line is never vacuous |

There is no fail-closed order on this carrier, which is exactly why the
obstruction of §2.4 does not apply to it.

### 2.8 `Cuisine.NonaryAction` — base rotation, fibre rotation, and the nonary group

The `3 · 5` grid of §2.2 gives the *base* an order-three rotation `baseRot` of
its own (advance the tone coordinate, keep the taste column).

| statement | content |
|---|---|
| `baseRot_cube`, `baseRot_no_fixpoint` | order three, fixed-point free |
| `fabricPull_fabricRot` | **the base rotation and the fibre rotation commute** |
| `nonary_period`, `nonary_faithful` | the hyperfabric therefore carries a *faithful* action of `ℤ/3 × ℤ/3`: nine distinct operators.  This is the honest referent of the corpus's "Tlurey triadic/nonary" motif |
| `baseInvariantEquiv`, `card_baseInvariant` | the base-invariant sections are exactly the taste-indexed ones: `3^5 = 243` of them, realising `3^15 = (3^5)^3` as an orbit count |
| `no_rot_invariant` | the fibre rotation, by contrast, fixes **no** section at all |
| `base_rotation_moves_moonshine` | honest negative: the base rotation carries the trivector mask `{47,59,71}` to `{19,23,29}` and the mask product from `196883` to `12673`, so it is **not** a symmetry of the moonshine data |
| `moonshine_preserving_symmetry` | the repair: the three-cycle `47 → 59 → 71 → 47` of the trivector primes *is* an order-three base symmetry, commutes with the fibre rotation, and fixes both the trivector mask and its product `196883` |
| `card_moonshineInvariant` | its invariant sections number `3 ^ 13 = 1594323` (twelve free primes plus one collapsed orbit) |
| `moonshine_nonary_faithful` | its joint action with the fibre rotation is again a faithful `ℤ/3 × ℤ/3` |
| `moonshineRot_fixes_small` | honest caveat: unlike `baseRot` it is not fixed-point free — it fixes the twelve primes below `47` |

`Cuisine.NineSheet.grid_flip` and `card_fabric_grid` supply the commuting square
behind this: the two readings of a section agree, and
`3^15 = (3^5)^3 = (3^3)^5 = 3^9 · 3^6` with `3^9 = 27^3 = 19683`.

### 2.9 `Cuisine.SweetgrassSpine` — the motif vocabulary, audited and realised

`SweetgrassCarrierSpine` is the module the cuisine record reaches through
`sweetgrassAttribution : String`.  It enumerates thirty-five motifs, thirty-three
anchors, thirty-nine roles and seven named threads.

Audit (all proved):

| statement | content |
|---|---|
| `canonicalCarrierMotifs_nodup`, `motifs_complete` | the thirty-five motifs are distinct and the canonical list is complete |
| `motifAnchor_not_injective`, `motifAnchor_collision` | anchors do not separate motifs |
| `unreachedAnchors_eq`, `anchors_not_surjective` | exactly two anchors are declared and never used — `anchorLocalDocs369` and, tellingly, `anchorMonsterMoonshineSSPQuotient`, the one anchor that would have met the fifteen-prime base |
| `heckeOperatorRole_unused` | the role named for the Hecke *operator* is never assigned; the Hecke motif gets `eigenProfileRole` |
| `projectionTarget_image`, `projectionTarget_missing`, `motifProjectionTarget_not_injective` | the PNF projection collapses thirty-nine roles onto five of the eight targets |

Realisation (the part that was missing):

* `realise : CarrierMotif → SpineCarrier` — the typed table saying which
  implementation type each motif names, with `unrealised` where none exists;
* `carrierCard_eq` — every size checked against the real `Fintype.card`
  (`TriTruth` 3, `KnotWeaveCarrier` 3, `Stage` 4, `Stage6` 6, `TriTruth²` 9,
  `SSP` 15, sheet 19683, `MaskSSP` 32768, `Fabric` 14348907, `jCoefficient`
  196884);
* `card_realised`, `realised_iff` — **thirteen of thirty-five** motifs are
  realised;
* `sweetgrass_itself_unrealised` — honesty clause: the Sweetgrass braid/fabric
  motif, the one the cuisine record actually names, is *not* one of them;
* `SweetgrassRealisation` / `sweetgrass_spine_realised` — the structural bundle:
  the `369` fibre, the `3 · 5` prime base, the hyperfabric over it, knot-weave
  fields as sections, the dialectical action as seasoning, the surjective umami
  homomorphism, the Monster mask embedding, the depth-nine sheet, the moonshine
  numerals, the ultrametric contraction, and the faithful nonary action — all
  about one object, with the two honest clauses above attached.

### 2.10 `Cuisine.ToeBridge` — the package

`CuisineToeBridge` collects the statements above as a nineteen-field typed
interface;
`cuisineToeBridge` inhabits it from the proved theorems; `cuisine_toe_bridge` is
the composite existence statement.

---

## 3. Provenance

| new Lean module | inputs it uses (none re-defined) |
|---|---|
| `Cuisine.UmamiTransport` | `Cuisine.SensoryCore.UmamiBlend` (Agda `QualitativeSensoryCore`); `Synthesis.Hyperfabric` (`Fabric`, `fabricXor`, `fabricZMod`, `fabricRot`, `fabricAct`, `supportMask`); `Synthesis.MoonshineBase` (`maskProduct`, `trivectorMask`); `AgdaMirror.Moonshine` (`repDim`, `jCoefficient`); Mathlib `Nat.factorization` |
| `Cuisine.NineSheet` | the above, plus `Cuisine.SensoryCore.TasteDimension` and `AgdaMirror.Base369.TriTruth` |
| `Cuisine.SafetyFabric` | `Cuisine.ToneSeparation` (`safetyTritEquiv`, `safetyLevel`, `safetyRotate`); `Synthesis.MonsterFibre` (`MaskSSP`, `dSSP`, `USSP`, `projectSSP`, `Ultrametric.comap`) |
| `Cuisine.SeveritySeam` | Agda `DASHI.Interop.SensibLawResidualLattice` (mirrored); `AgdaMirror.Base369` (`HexTruth`, `rotateHex`); `Synthesis.DialecticTone.hexToTri` |
| `Cuisine.MdlPrimeModel` | Agda `MDL.Core`, `MDL.PrimeSubsetModel` (mirrored); the transport |
| `Cuisine.SurfaceInterpretation` | `Cuisine.HyperfabricGuard.TriadSurface`; `AgdaMirror.DASHIAlgebra`, `AgdaMirror.LogicTlurey`, `Synthesis.MonsterFibre`, `Synthesis.Hyperfabric` |
| `Cuisine.SpiralCarrier` | Agda `DASHI.Cognition.KlueverFormConstantProjection` (mirrored); `AgdaMirror.Base369` |
| `Cuisine.KnotWeave` | Agda `DASHI.Culture.KnotWeaveTopologyCultureBridge` (mirrored); `AgdaMirror.TritBridge`, `Synthesis.Hyperfabric`, the transport |
| `Cuisine.NonaryAction` | `Cuisine.NineSheet` (`sspToneTaste`, the `3 · 5` grid); `Synthesis.MoonshineBase` (`maskProduct`, `trivectorMask`) |
| `Cuisine.SweetgrassSpine` | Agda `DASHI.Interop.SweetgrassCarrierSpine` and the `ProjectionTarget` enumeration of `DASHI.Interop.PNFRoleVectorAlgebra` (both mirrored); all of the above |

The dependency map of the cuisine Agda lane itself (imports, callers, module
counts, classification of the supplied material) is unchanged; see
`CUISINE_DEPENDENCY_MAP.md` §1, §3, §4.

---

## 4. Frontier: what is still *not* proved

Stated exactly, so that nothing above is over-read.

1. **The `3 · 5` indexing is a choice.**  `sspToneTaste` is one of the `15!`
   bijections.  Nothing distinguishes it; no theorem here depends on which one
   is picked, only on the product shape.  A canonical `3 × 5` structure on the
   supersingular base — if one is wanted — is not defined anywhere in the
   corpus, and would be the natural next obligation.
2. **The moonshine identities are numeral identities.**  `196883 = 10·3^9 + 53`
   is arithmetic about the supplied constants.  Nothing in this repository
   defines the Monster group, a representation of it, or the `j`-invariant, and
   nothing here proves anything about them.  Reading `repDim` as a
   representation dimension is provenance, not theorem.
3. **The transport's kernel is only partly described.**  `umamiFabric_cube`
   shows cubes die; the full kernel (intensities `u` with all fifteen exponents
   of `u+1` divisible by 3) is not characterised, and neither is the induced
   isomorphism from the quotient.
4. **Nothing transports the fail-closed order.**  This is now known to be
   forced, not accidental (`severity_const_of_monotone_perm`), but it does mean
   the cuisine severity order and the tone rotation remain irreconcilable.
5. **`spiral`'s referent is finite, but its geometry is not.**  The Klüver
   form-constant carrier supplies the referent, but the actual spiral geometry
   in this repository is the real-analytic log-polar development under
   `Lean/DASHI/Klüver’s Form Constants_aristotle/`, which is not a finite
   carrier and is not linked to the ternary spine by anything proved here.
6. **The Sweetgrass motifs that remain unrealised.**  Twenty-two of the
   thirty-five name nothing this repository defines.  The ones a future session
   could most plausibly realise are `motifCarry` (carry memory),
   `motifSupervoxel` (supervoxel admissibility), `motifHeckeEigen`, and the
   BT-tree / BT-braid pair; `motifSweetgrassBraidFabric` itself is a source
   attribution and probably should stay unrealised.
7. **The two order-three base symmetries are not related to each other.**
   `base_rotation_moves_moonshine` shows the `3 · 5` grid rotation moves the
   trivector mask; `moonshine_preserving_symmetry` shows the trivector
   three-cycle does not.  Both give faithful nonary actions on the hyperfabric,
   but nothing here identifies, compares or combines them, and the group they
   generate inside `Sym(SSP)` is not computed.  That is the natural next
   question.
8. **The Agda side is unchecked.**  All nine new modules are Lean.  Transcribing
   the transport back into Agda — in particular `umamiFabric_compose` and
   `mdl_optimal_iff` — remains open, and cannot responsibly be attempted here
   without a typechecker.
9. **The earlier defect list is unchanged.**  `CUISINE_DEPENDENCY_MAP.md`
   §5.1(a)–(f) — phantom route indices, free `overallRisk`, free `standing`,
   unchecked source distinctness, the `Bool` ledger idiom, the incomplete
   surface ledger — are still unrepaired *in the Agda sources*.
10. **No physical or mathematical theory-of-everything claim is made or
   supported.**  Every carrier above is a finite set or a natural number.
