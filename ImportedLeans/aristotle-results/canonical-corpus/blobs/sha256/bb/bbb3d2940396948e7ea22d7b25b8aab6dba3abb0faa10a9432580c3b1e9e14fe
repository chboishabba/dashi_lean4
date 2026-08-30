# The global TOE map

A corpus-wide integration pass over the supplied non-Yang–Mills / non-Navier–Stokes
DASHI material. This document is the prose half; the machine-checked half is
`Lean/Integration/Registry.lean`, whose rows carry their own witnesses. Where the
two disagree, the Lean file is authoritative.

**Scope and honesty statement.** Nothing here asserts a physical, empirical,
mathematical-theory-of-everything, Riemann-hypothesis, Monster-group, moonshine,
vertex-operator-algebra or unitarity result. Every carrier discussed below is a
finite type; every distance is a natural number. No Yang–Mills or Navier–Stokes
module is imported, referenced or modified by any file in the `Integration`
spine (checked: zero matches for `YangMills`/`NavierStokes`/`NSTriad` in
`Lean/Integration`). The Agda sources are read-only in this environment — no
Agda toolchain is installed, so **no Agda module has been rechecked here**; the
Agda statements cited are source readings. Everything asserted as proved is a
Lean statement checked by `lake build`.

---

## 1. Import / dependency provenance

Computed by `scripts/toe_import_map.py`, which walks `Agda/`, excludes the
vendored `Agda/cubical` standard library and excludes YM/NS-named paths.

- **8 713 Agda modules, 2 146 283 lines** in the surveyed cutset.

### 1.1 Domain sizes (modules)

| Domain | Modules | | Domain | Modules |
|---|---:|---|---|---:|
| `DASHI.Physics` | 5 247 | | `DASHI.Interop` | 131 |
| `DASHI.Biology` | 537 | | `DASHI.Algebra` | 117 |
| `DASHI.Foundations` | 321 | | `DASHI.Reasoning` | 91 |
| `DASHI.Core` | 274 | | `DASHI.Promotion` | 90 |
| `DASHI.Cognition` | 257 | | `DASHI.Ontology` | 80 |
| `DASHI.Geometry` | 206 | | `DASHI.Mathematics` | 65 |
| `DASHI.Analysis` | 173 | | `DASHI.<root>` | 59 |
| `DASHI.Moonshine` | 164 | | `DASHI.Arithmetic` | 53 |
| `DASHI.Governance` | 161 | | `DASHI.Philosophy` | 51 |
| `DASHI.Crypto` | 140 | | top-level | 41 |

`DASHI.Physics` is 60% of the corpus and contains the Navier–Stokes closure
material; it is **excluded from the integration work** and appears here only as
a size statistic.

### 1.2 Hubs (in-degree = number of modules importing it)

Excluding `DASHI.Physics.Closure.*` (NS material):

| Hub | In-degree | Role |
|---|---:|---|
| `DASHI.Core.Prelude` | 897 | universal prelude |
| `DASHI.Algebra.Trit` | 180 | the ternary digit |
| `Base369` | 140 | 3/6/9 tone, hex and nonary layers |
| `DASHI.Core.GenericReceipt` | 108 | the receipt/socket idiom |
| `MonsterOntos` | 107 | the 15 supersingular primes |
| `Ultrametric` | 73 | the corpus-wide distance record |
| `DASHI.Interop.SensibLawResidualLattice` | 59 | interop lattice |
| `DASHI.Foundations.SSPTritCarrier` | 58 | trit carrier + receipt |
| `DASHI.TrackedPrimes` | 51 | prime bookkeeping |

The shape of the corpus is therefore: one prelude, then **two genuine structural
hubs (`Trit`/`Base369` and `MonsterOntos`/`Ultrametric`)**, then a receipt idiom
that is used everywhere. That is what determined the junctions attacked below.

### 1.3 Heaviest cross-domain import edges

`Biology→Core` 357, `Physics→Geometry` 328, `Governance→Core` 189,
`Cognition→Core` 185, `Foundations→Core` 146, `Physics→Algebra` 141,
`Ontology→Core` 111, `Physics→Foundations` 90, `Moonshine→Foundations` 88,
`Interop→Core` 82, `Reasoning→Core` 81, `Promotion→Physics` 80.

Almost all heavy edges terminate in `Core`, `Algebra`, `Foundations` or
`Geometry`. Domain-to-domain edges that are *not* mediated by those four are
rare; this is the main structural reason why the corpus's cross-domain content
is concentrated in the ternary and 15-prime layers.

### 1.4 Vocabulary spread (textual mentions, by domain)

| Term | Mentions | Top domains |
|---|---:|---|
| `Moonshine` | 437 | Moonshine 164, Physics 152, Biology 45 |
| `Monster` | 376 | Physics 126, Moonshine 83, Biology 65 |
| `Trit` | 238 | Physics 93, Cognition 26, Foundations 22, Core 18, Codec 14 |
| `Base369` | 221 | Foundations 91, Physics 35, Cognition 20, Interop 12 |
| `Hyperfabric` | 178 | Biology 53, Reasoning 24, Ontology 22, Physics 18 |
| `Codec` | 132 | Codec 38, Physics 36, Foundations 11 |
| `Supervoxel` | 50 | Physics 14, Promotion 10, Interop 7, Cognition 5 |
| `Loom` | 31 | Promotion 8, Governance 4, Biology 3, Cognition 3 |
| `Clopen` | 28 | Cognition 6, Physics 4, Geometry 4, Sheaf 3 |

Mention counts are **level-1 evidence only**. The point of the classification
below is to say, for each of these, how much more than a shared word there is.

### 1.5 Lean provenance

- `Lean/AgdaMirror/` — 107 modules, hand transcriptions of named Agda modules.
  Each mirror's docstring names its Agda source. Mirrors are Lean definitions
  that *reproduce* the Agda ones; they are not extracted, so a mirror is only as
  faithful as its transcription. `scripts/mirror_provenance.py` and
  `MIRROR_PROVENANCE.md` now audit that layer mechanically at *name* level: 123
  (mirror, cited source) pairs, 116 resolving to a file in this tree, one
  dangling citation, three non-aggregate mirrors with no source declared, and
  66.0 % of the 1 012 cited Agda declarations having a same-named Lean
  counterpart. Name-level correspondence is provenance, not faithfulness — see
  frontier item 8. `scripts/mirror_signature_compare.py` / `MIRROR_SIGNATURES.md`
  add a *signature-shape* comparison on top of that: of 515 name-matched pairs,
  495 (96.1 %) agree on both arity (explicitly quantified arguments, implicit
  and instance binders excluded) and the head connective of the conclusion, and
  the 20 that disagree are listed individually as a review queue. No Agda
  `postulate` in a cited source has a name-matched mirror declaration. Shape
  agreement is necessary but not sufficient for faithfulness; it rules out gross
  mis-transcription of arity and conclusion form, and nothing more.
- `Lean/Synthesis/`, `Lean/Cuisine/`, `Lean/Spine/` — earlier development on top
  of the mirrors (68 Lean files across these and `Integration`).
- `Lean/Integration/` — this pass. It imports mirrors and `Synthesis`; it does
  not import `Cuisine` except for two records (`Cuisine.SupervoxelClopen`,
  `Cuisine.LoomBridge`) that already mirror the relevant Agda structures.

---

## 2. The four-level classification

Levels, as encoded in `Integration.Levels.BridgeLevel`:

1. **vocabulary** — the same word appears in two places, and nothing else is
   shared. Witness: a `String`. No formal content.
2. **recordDependency** — one side's record stores the other side's value; there
   is a field projection between the carriers. A real import-level dependency
   that proves nothing structural.
3. **sharedType** — a defined bijection `A ≃ B` of the two carriers, with no
   preservation claim.
4. **provedTransport** — a bijection proved to intertwine the two sides'
   operations (`Transport`), or a map proved to preserve a binary invariant
   (`Evidence.provedPreservation`, in practice always a distance).

The classification is enforced by types: `Evidence` has one constructor per
level, and `Entry.level` reads the level off the constructor. A row cannot claim
level 4 without a Lean object of the right type. Negative results are `Boundary`
values, which store the refuted proposition *and its refutation*; unconstrained
record fields are `Socket` values, which store a proof that nothing is
constrained.

### 2.1 The registry (positive rows)

`Integration.Registry.registry`, with `registry_levels` checking the level of
each row by `rfl`.

| # | Source | Target | Level | Witness |
|---:|---|---|:--:|---|
| 1 | `DASHI.Algebra.Trit` | `ZMod 3` | **iv** | `ternaryHub.trit` |
| 2 | `Base369` tone `TriTruth` | `ZMod 3` | **iv** | `ternaryHub.tone` |
| 3 | `SSP369Ultrametric.Digit369` | `ZMod 3` | **iv** | `ternaryHub.digit` |
| 4 | `SSPTritCarrier.SSPTrit` | `ZMod 3` | **iv** | `ternaryHub.ssp` |
| 5 | `TriadicMaskSign.TritCode` | `ZMod 3` | **iv** | `ternaryHub.code` |
| 6 | `ConstraintClopenRefinement.BTBranch` | `ZMod 3` | iii | `ternaryHub.branch` |
| 7 | `Base369` hexadic beat | `ZMod 2 × ZMod 3` | **iv** | `hexSplitTransport`, `hexSplit_xor` |
| 8 | `Base369` nonary layer | `ZMod 9` | **iv** | `nonaryRotateTransport` |
| 9 | codec kernels `Kernel d` | `Address369 d` (polarity) | **iv** | `kernelPolarityTransport` |
| 10 | codec kernels, prefix distance | `Address369 15`, prefix distance | **iv** | `kernelIsometry` |
| 11 | Monster 15-prime mask fibre + supplied ultrametric | depth-15 boolean prefix addresses | **iv** | `dSSP_eq_dist` |
| 12 | hyperfabric sections `SSP → Trit` | `Address369 15` | iii | `fabricAddr369Equiv` |
| 13 | loom relation taxonomy | loom relation roots | ii | `rootOfBucket` |
| 14 | `MonsterOntos.SSP` | the Monster sporadic group | i | shared word only |
| 15 | `MonsterUltrametric15.UMask15` (supplied record) | depth-15 prefix geometry | **iv** | `d15_eq_prefix` |
| 16 | cuisine safety fields (culture domain instance) | depth-15 prefix geometry | **iv** | `dSafety_eq_prefix` |
| 17 | cognition `Phase3` | `ZMod 3` with rotation | **iv** | `phase3Transport` |
| 18 | cognition observable `observeTrit` | the hub's digit with polarity | **iv** | `observeTrit_flip` (preservation only: surjective, not injective) |
| 19 | cognition hidden state | the hub's digit | ii | `balancedProjection` |
| 20 | "supervoxel"/"clopen" talk | the prefix-ball topology | iii | `PrefixBall`, `ball_open`, `ball_closed` |
| 21 | ternary endomorphism codes `T³` mod the output `C₃` | the nine-state phase quotient `T × T` | **iv** | `phaseEncode_rotate_snd`, `quotient_eq_iff_orbit` |
| 22 | the phase quotient | the `Base369` nonary labels | iii | `nonaryChart` |
| 23 | the nonary labels with the *transported* phase-quotient law | `ZMod 3 × ZMod 3` | **iv** | `phaseZModEquiv_add` |
| 24 | SSP fibre orientations | `ZMod 2` | **iv** | `orientationSign_hom` |
| 25 | SSP path composition | composition of lane transports | **iv** | `laneAction_comp`, `transportSSP_comp` |
| 26 | SSP lane states | the hub with polarity | **iv** | `laneStateHub` |
| 27 | signed multiplicity defect orientation | the hub with polarity | **iv** | `defectOrientationHub`, `orientation_swap` |
| 28 | signed defect orientation | the SSP `FibreOrientation` carrier | **iv** | `defectToFibreOrientation_equiv` |
| 29 | the polarity-invariant Boolean observer | the induced (trivial) action on masks | **iv** | `polarPresence_equivariant`, `laneAction_descends` |
| 30 | the residual-bearing 9 → 6 polar projection | polar cells ⊕ retained phase | **iv** | `polarTransport`, `polarEquiv` |
| 31 | the closure lane's `KernelTrit` | the hub with polarity | **iv** | `kernelTritHub` |
| 32 | the free C₃ output-phase action on the 27 endomorphism codes | the nine-state orbit carrier | **iv** | `phaseReduction`, `phaseQuotient_invariant` |
| 33 | the SSP orientation acting on a pair of lane states | its action on one lane state | **iv** | `laneReduction`, `laneReduction_action_nontrivial` |

Row 6 stops at level iii because the source equips `BTBranch` with no
involution, so there is no operation to preserve — an absence, not a failure.
Row 13 cannot be promoted: see boundary B3. Row 14 is level i: `SSP` is a 15-element enumeration of the supersingular
primes, and no group, character or vertex algebra is defined anywhere in the
Lean cutset, so there is nothing available to raise it with.

### 2.2 Boundaries (negative rows, each with a proof)

`Integration.Registry.boundaries`.

| # | Claim refuted | Refutation |
|---:|---|---|
| B1 | the nonary layer *with its cyclic law* ≅ two ternary layers with componentwise XOR | `nonary_not_ternary_square`. Scope: this refutes an identification of the two **operations**; the carrier chart exists (`nonaryChart`, row 22) and the same nine labels do carry an exponent-three law once the phase quotient's addition is transported along it (row 23). The honest statement is *the address carrier does not determine the algebra*. |
| B2 | `Base369` `triXor` is `ZMod 3` addition **in the balanced chart** | `balTone_triXor_ne_add` (it is `x+y+1` there). Scope: in its own native index chart `triXor` **is** addition (`triIdx_xor`); the two charts differ by a translation, and only the balanced one is polarity-compatible (`triXor_chart_dichotomy`). |
| B3 | the loom relation taxonomy is a product over its roots | `loom_root_not_product` (class sizes 3,2,3,1) |
| B4 | hyperfabric support is an isometry onto the mask geometry | `support_not_isometry`. Observer-level: bounds the Boolean observer, not the SSP layer (rows 24–26). |
| B5 | hyperfabric support is injective | `support_not_injective`; the lost information is exactly the sign (`polarPresence_orbit`, `no_equivariant_section`). |
| B6 | **some** binary Boolean operation makes support a homomorphism for ternary XOR | `support_no_descent` — strictly stronger than the corpus's `support_not_hom`, which refutes only boolean OR, and equally true of the polarity-invariant observer (`polarPresence_no_descent`). Observer-loss boundary: the *symmetry action* does descend (row 29); only the binary law does not. |
| B9 | support is polarity-invariant | `support_not_polarity_invariant`: support is the indicator of "not the `tritXor` identity", so it is aligned with the native chart's origin, not the polarity-fixed one. |
| B10 | the SSP orientation monoid is a group | `not_a_group`: `forward` is a non-unit idempotent; the universal group quotient is `ZMod 2` (row 24). |
| B11 | a direct 9 → 6 retraction of the polar projection exists | `no_retraction_to_polar`: no injection of the nine full phase cells into the six polar cells, so the retained residual is not removable (row 30). |
| B7 | the `Monster` walk distance is a prefix distance under some map | `walk_not_prefix` (its strong triangle law is false) |
| B8 | the cognition "public zero" constraint is atomic | `publicZero_not_atomic` |
| B12 | support intertwines the polarity involution with **some** map on the Boolean layer | `support_no_equivariant_action` / `support_not_a_reduction`: the square fails already at the *unary* symmetry, before any binary law. This is the correctly scoped form of the `support_*` negatives — a property of that observer's origin, not of the SSP layer, whose action does descend along the polarity-invariant observer (row 29, `polarReduction`). |

### 2.3 Sockets (unconstrained records, each with a proof)

`Integration.Registry.sockets`.

| Site | Nominal role | Proof that it constrains nothing |
|---|---|---|
| `SSP369ClopenBallBridge.PrefixBallClopenAuthority` | certifying a ball is clopen | `authorityContentless`: for every ball the record is the same four-element type |
| `SSPTritCarrier.SSPTritCarrierReceipt` | certifying a trit-carrier bridge | `alignment_unconstrained`: for **every** digit there is a receipt whose stored "negative value" is that digit |
| `ClopenPsychologicalSupervoxel.ClopenPsychologyBoundary` | recording non-atomicity and lack of clinical validation as `Bool`s | `boundaryContentless`: the record is equivalent to `Unit` |

In each case the spine supplies the real content the socket was standing in for:
`ball_open`/`ball_closed` for the first, `AlignedReceipt`/`aligned_forced` for
the second, `publicZero_not_atomic` for the structural half of the third. The
third socket's *empirical* half (clinical validation) is left as a socket on
purpose — it is not a mathematical claim and nothing here bears on it.

Totals: 33 positive rows (26 at level iv, 4 at iii, 2 at ii, 1 at i), 12
boundaries, 3 sockets. `registry_levels` checks all 33 levels by `rfl`.

---

## 3. What the integration pass actually built

### 3.1 The ternary hub — `Lean/Integration/TernaryHub.lean`

The corpus has at least six independently-declared ternary carriers. Each is
given a balanced coordinate to `ZMod 3` under which the supplied polarity map
(`Trit.inv`, `triReflect`, `invert369`, `sspTritInv`, `invertCode`) becomes
negation, and `bal_unique_up_to_sign` shows the coordinate is forced up to sign
by that requirement alone — so the identification is canonical rather than
chosen. `ternaryHub : TernaryHubBundle` bundles all of it, together with the
checks that the supplied `trit→369` and `BTBranch ≃ Trit` maps agree with the hub.

Boundary discovered here: the corpus's `Base369` XOR satisfies
`bal(x ⊕ y) = bal x + bal y + 1`, i.e. it is affine, not additive. So the two
"ternary operations" of the corpus (`tritXor`-style addition and the `Base369`
XOR) are *not* the same group law, and any argument that silently identifies
them is wrong. Rotation, by contrast, is `+1` in both.

### 3.2 Base369 as group theory — `Lean/Integration/Base369Group.lean`

`hexSplit : HexTruth ≃ ZMod 2 × ZMod 3` realises the loom's declared
`projection2x3` tag, additively (`hexSplit_xor`) and with both components
homomorphisms onto the corpus's own carriers. The declared `projection2x9` tag
has **no carrier among the `Base369` layers** (`base369_carrier_cards` records
that they have 3, 6 and 9 elements, so none has the 18 needed), and no such
carrier was found elsewhere in the surveyed sources; the tag is currently
vocabulary.

`nonary_not_ternary_square` is the sharpest negative *about the cyclic law*: the
nonary layer with `nonaryXor` is cyclic of order 9, so no bijection at all
carries it to componentwise ternary XOR. The ternary layer does embed
(`triInNonary`, a homomorphism) and does quotient (`nonaryReduce`), but the
extension does not split. This is **not** a statement that nine states are never
two ternary coordinates: see §3.10, where the corpus's own symmetry-reduced
nine-state carrier and the second algebra it induces on the same nine labels are
constructed.

### 3.3 The prefix geometry — `Lean/Integration/Address.lean`

Developed once for an arbitrary finite digit alphabet, so that comparisons
between the corpus's several distance definitions become theorems rather than
coincidences. `agree_ge_iff` is the single characterisation from which symmetry,
self-agreement and the strong triangle inequality follow; `Addr.ultrametric`
instantiates the corpus's own `Ultrametric` record; `dist_map` shows any
injective relabelling is an isometry and `dist_mono_map` that any coarsening is
non-expansive.

Gap closed: the Agda `TriadicPAdicCodec369Bridge` proves only that `kernel→369`
sends an address to distance zero from *itself*. `kernelIsometry` proves it is
distance-preserving, and `kernelEquiv369` that it is bijective — so the codec
lane and the 3/6/9 geometry lane are literally one metric object.

### 3.4 Supervoxel / clopen refinement — `Lean/Integration/ClopenBalls.lean`

`member_iff_dist_le` identifies a prefix ball with a closed metric ball;
`ball_open` and `ball_closed` prove clopen-ness (which the Agda asserts by
inhabiting a token record); `refinement_iff_subset` upgrades the source's
one-way implication to a biconditional (needing `[Nontrivial α]`, which is
genuinely necessary); `no_atomic_ball` shows the refinement never bottoms out
above full depth; `ternaryAddressBallSystem` is a checked inhabitant of the
corpus's clopen-ball-system record.

### 3.5 Refinement systems — `Lean/Integration/Refinement.lean`

`ConstraintClopenRefinement.RefinementSystem` is never instantiated anywhere in
the Agda corpus. Two inhabitants are supplied: the dialectic loom's relation
taxonomy (with coherent, surjective projections) and the tower of truncated
ternary addresses. So the record is non-vacuous, and the loom and the geometry
lane share one interface — which is a genuine level-iii bridge between the
dialectic and geometry domains. `loom_root_not_product` bounds it: the loom is a
refinement, not a bundle.

### 3.6 The Monster 15-prime junction — `Lean/Integration/MonsterFifteen.lean`

The main new bridge. `lcpLen_ofFn` proves that the list-recursive
longest-common-prefix length of `MonsterUltrametric15` equals the indexed
agreement depth of the address geometry; hence `dSSP_eq_dist`: the supplied
Monster mask ultrametric **is** the depth-15 prefix distance over a two-letter
alphabet, and `USSP_d_eq_dist` that the two `Ultrametric` records carry the same
distance function. These are two constructions in unrelated files with no import
between them.

On top of that: a hyperfabric (a section `SSP → Trit`) is a depth-15 ternary
address, hence a 3/6/9 address (`fabricAddr369Equiv`), isometrically
(`fabric369_isometry`). The corpus's `support : Trit → Bool` then maps the
ternary fabric geometry into the Monster mask geometry, and
`support_nonexpansive` proves it is non-expansive. The boundary theorems B4–B6
show this cannot be improved to an isometry, a bijection, or an algebra map —
but all three are statements about *this Boolean observer*, not about the
SSP-indexed layer, whose own transport is functorial (§3.11) and whose symmetry
action does descend to the Boolean layer (§3.12).
`monster_ternary_junction` packages the junction as one conjunction.

### 3.7 Census of the `Ultrametric` hub — `Lean/Integration/UltrametricCensus.lean`

`Ultrametric.agda` has in-degree 73 and is a socket: it constrains a `Nat`-valued
distance to be reflexive-zero, symmetric and strongly triangular, and nothing
more. Consumers build instances all over the corpus and never compare them, so
the source does not reveal whether "the ultrametric" is one geometry or many.
Every live instance in the Lean cutset is classified here:

| Instance | Verdict |
|---|---|
| `MonsterProjection15.UMask15` | prefix geometry (`d15_eq_prefix`) |
| `Synthesis.MonsterFibre.USSP` | prefix geometry (`dSSP_eq_dist`) |
| `Integration.MonsterFifteen.fabricUltrametric` | prefix geometry by definition |
| `Integration.Address.Addr.ultrametric` | the geometry itself |
| `Cuisine.SafetyFabric.USafety` | prefix geometry pulled back along `doubtMask` (`dSafety_eq_prefix`) |
| `AgdaMirror.MonsterWalk.UMask` | **not** an ultrametric, and provably not a prefix geometry (`walk_not_prefix`, `walk_not_mask15`) |

So the corpus's "ultrametric" vocabulary denotes exactly one geometry, plus one
outlier. The outlier matters: the Agda `Monster/Ultrametric.agda` *postulates*
the strong triangle law for its first-difference distance, and the mirror's
`dMask_ultratriangle_false` refutes the postulate. `walk_not_prefix` draws the
structural consequence — no relabelling whatsoever can present the walk distance
as a prefix distance — so the two "Monster distances" in the corpus are not
isomorphic, and results proved against the postulated one do not transfer.

The `USafety` row is also the pass's clearest **domain instance**: a culture-layer
construction (cuisine safety verdicts) whose geometry is literally the ternary
prefix geometry, with `doubtMask` as the only domain-specific ingredient.

### 3.8 A cognition domain instance — `Lean/Integration/CognitionSupervoxel.lean`

The cognition layer is the largest consumer of the supervoxel/clopen vocabulary
after physics. `DASHI/Cognition/ClopenPsychologicalSupervoxel.agda` is its
cleanest statement, and it is mirrored here in full: the phase-enriched trit,
the nine-constraint system over a hidden psychological state, and the two
refinements of the "public zero" constraint.

What the pass adds. The Agda module states its central structural claim as a
**`Bool` placeholder** — a record field `publicZeroIsAtomic : Bool` together
with `publicZeroIsAtomicIsFalse : publicZeroIsAtomic ≡ false`, which records a
value and proves nothing about the constraint system.
`publicZero_not_atomic` proves the corresponding statement about `Atomic`, in
the same interface already used by the cuisine, loom and publication lanes, so
`Atomic` is now refuted in four different domains.

Two further links the source does not state: `phase3Transport` identifies the
cognition layer's cyclic `Phase3` with the hub's `ZMod 3` and its rotation with
`+1`; `observeTrit_flip` shows the cognition observable intertwines weight
reversal with the hub's polarity involution — the precise sense in which the
cognition layer's "balanced trit" is the corpus's balanced trit. It is a
preservation theorem only: `observeTrit` is surjective but not injective, and
that non-injectivity is exactly the non-atomicity above.

The record's *other* `Bool` field, `subvoxelMechanismClinicallyValidated ≡
false`, is an **empirical** socket and is deliberately left as one:
`boundaryContentless` shows the whole record is equivalent to `Unit`, and
nothing in this development is clinical, psychological or empirical evidence.

### 3.9 The analytic (RH/zeta) domain — `Lean/Integration/Riemann*.lean`

The map originally carried no analytic row: every carrier above is finite and
every distance a natural number. The RH/zeta lane is now registered as a
separate domain in the same vocabulary, in
`Integration.RiemannDomain.{analyticEntries, analyticBoundaries, analyticSockets}`
with `analyticEntries_levels` checking each row's level by `rfl`:

* **Eleven level-iv rows.** The lane's discrete reflection carrier *is* the ternary
  hub's polarity carrier tensored with a magnitude; its `C3Phase` *is* the hub
  carrier, realised by the actual cube roots of unity of `Spine.TernaryPhase`
  (with inversion becoming complex conjugation, and the orbit sum vanishing in
  `ℂ`); the Moonshine cyclotomic carrier — the lane's only cross-domain Agda
  import — evaluates additively and injectively onto `ℤ[ζ] ⊆ ℂ`; and, over `ℂ`,
  the composite of the lane's two declared symmetries `s ↦ 1 − conj s` is the
  `C₂` generator of `Spine.RealC2`, whose fixed locus is exactly the critical
  line and whose transverse coordinate is exactly the displacement `Re s − 1/2`.
  The lane's separate *exact rational* symmetry plane evaluates injectively into
  `ℂ` intertwining all three of its involutions, so the rational and complex
  models are one object.
* **Six boundaries**, including the Agda flag `c3AndZetaCarriersIdentified =
  false` promoted to a theorem, and the proof that the strip's symmetry group is
  Klein four (hence binary, not ternary).
* **Five sockets**, including the analytic substrate tower — it is inhabited,
  and both truth values of its own `RiemannHypothesisFor` occur among its
  inhabitants, so it constrains nothing — and the lane's xi-zero-symmetry and
  Hilbert–Pólya interfaces, each inhabited by content-free witnesses, so the
  theorems the sources derive from them are statements about the interfaces.

No statement about the Riemann zeta function, its zeros or the Riemann
hypothesis is made. Details, provenance and the analytic frontier are in
`RH_TOE_DOMAIN_MAP.md`; the earlier estimate-level work is in
`RH_BRIDGE_REPORT.md`.

---

### 3.10 The nine-state phase quotient — `Lean/Integration/PhaseQuotient.lean`

The corpus builds a nine-state carrier by *symmetry reduction*, not by
numerology: `TernaryEndomorphismPhaseQuotientExact.agda` quotients the 27
level-two ternary endomorphism codes by the free order-three output phase. Here
`rotateOutputCode_ne` proves the action free, `phaseEquiv` splits the carrier as
`Phase3 × PhaseQuotient9` (so `27 = 3 × 9` on the nose), and
`quotient_eq_iff_orbit` proves the nine-element coordinate is exactly the orbit
space `T³/C₃` — invariant under the action and separating its orbits.

`nonaryChart` mirrors the corpus's two-sided chart `PhaseQuotient9 ↔
NonaryTruth`. Transporting the quotient's componentwise addition along it gives
`nonaryPhaseAdd`, a *second* algebra on the corpus's own nine labels;
`phaseZModEquiv_add` identifies it with `ZMod 3 × ZMod 3`, and
`nonaryPhaseAdd_exponent_three` versus `nonaryXor_order_nine` separates the two.
`q9_nonary_group_iso_impossible` shows no relabelling identifies them. The
resulting statement — B1 in its corrected form — is that the address carrier does
not determine the algebra.

One level down, the same phenomenon is the *two origins* of the ternary carrier:
`triXor_chart_dichotomy` collects the fact that `triXor` is the group law in the
native index chart (origin `tri-low`) and the affine law `x+y+1` in the balanced
chart (origin the polarity-fixed `tri-mid`), that the charts differ by a
translation, and that the native chart is not polarity-compatible
(`triIdx_not_polarity_compatible`), while the balanced one is and is unique up to
sign (`bal_unique_up_to_sign`).

### 3.11 The lawful SSP weave — `Lean/Integration/SSPWeave.lean`

The 15-lane layer carries preserved algebra, which the support boundaries do not
touch. `composeOrientation` on `{inverse, mediated, forward}` is a monoid
(`compose_assoc`, unit `mediated`) and provably not a group (`not_a_group`); its
universal group quotient is `ZMod 2` via `orientationSign_hom`, through which the
lane action factors (`laneAction_factors_through_sign`). Paths between lanes
compose associatively with units (`thenSSP_assoc`, `thenSSP_id_left/right`) and
transport is **functorial**: `transportSSP_comp` is `T_{q∘p} = T_q ∘ T_p`. The
lane-state carrier is the ternary hub, with the `inverse` orientation equal to
the hub's polarity involution (`laneStateHub`), and in balanced coordinates the
action is multiplication by `±1` (`laneBal_action`). The residual is also
functorial (`residualAfter_comp`).

### 3.12 What the Boolean observer keeps and forgets — `Lean/Integration/ObserverQuotient.lean`

`support t = decide (t ≠ neg)` is the indicator of "not the `tritXor` identity",
so it is a *native-chart* observer and is not polarity-invariant (B9). The
polarity-invariant Boolean observer is the magnitude test `polarPresence t =
decide (t ≠ zer)`, and `polarPresence_orbit` proves it is **exactly** the
quotient map of the polarity involution. Along it the symmetry action descends,
and uniquely: `polarPresence_equivariant` gives the commuting square with the
induced action, and `laneAction_descends` proves that induced action is forced to
be the identity. What does *not* descend is the binary law, for either observer
(`support_no_descent`, `polarPresence_no_descent`, both stronger than the
corpus's `support_not_hom`), and the exact loss is the sign
(`no_equivariant_section`).

The file also mirrors the corpus's signed relational layer
(`SignedMultiplicityObstructionExact.agda`): the integer defect `delta A B`, its
three-way orientation, the anti-symmetry `orientation_swap`, the proof that
Boolean presence forgets multiplicity (`presence_lossy`), and the two
identifications `defectOrientationHub` (defect orientation = the ternary hub) and
`defectToFibreOrientation_equiv` (defect reversal = the SSP forward/inverse
exchange). So the layer that keeps the sign is the layer the preserved SSP
algebra lives on.

### 3.13 The residual-bearing 9 → 6 projection — `Lean/Integration/PolarResidual.lean`

`SSP369PolarResidualQuotient.agda` insists its `9 → 6` projection is not a
retraction: the zero branch's phase is retained as a typed residual. `polarEquiv`
makes that exact — the projection is a **bijection** onto `PolarPhaseCell ⊕
DepthWheelPhase`, i.e. `9 ≃ 6 + 3`, whose inverse is the source's `reopen`;
`project_preserves_phase` shows the phase survives on both branches;
`no_retraction_to_polar` shows a genuine `9 → 6` retraction is impossible (B11);
and `polarTransport` shows the projection is polarity-equivariant. `kernelTritHub`
adds this lane's `KernelTrit` to the ternary hub as a seventh carrier.

### 3.14 Residual-bearing quotients as one structure — `Lean/Integration/ResidualQuotient.lean`

The pattern "coarse state + retained residual reopens the rich state" occurs at
least twice in the corpus (the polar `9 → 6` projection, and the magnitude
observer whose residual is the sign). `Integration.Residual.ResidualQuotient`
makes it a structure: a projection, a residual, and a proof that the pair
reconstructs the rich state. `injective_pair` and `card_le` are the generic
consequences, `residual_not_subsingleton` says the residual can never be dropped
when the projection is not injective, and `polarQuotient` / `signQuotient` are
the two instances.

### 3.15 Symmetry reduction as a typed obligation — `Lean/Integration/SymmetryReduction.lean`

Several projections in the corpus are described as "symmetry reductions".
`EquivariantQuotient G Rich Coarse` turns that description into data: a monoid
action on each layer, a surjective projection, and the commuting square

    π (g · x) = ḡ · π x .

The coarse action is a *field*, so an instance must exhibit the reduced action
rather than assert that one exists; `orbit_invariant` isolates the case where it
is trivial, which is quotient-by-a-symmetry.

Three inhabitants:

* `phaseReduction` — the free C₃ output-phase reduction `27 → 9` of
  `TernaryEndomorphismPhaseQuotientExact.agda` (row 32). The induced action is
  trivial, so the nine-state carrier is the orbit space — a fact about the
  *reduction*, independent of which of the two algebras (§3.10) the nine labels
  are later given.
* `polarReduction` — the SSP orientation action descending along the
  polarity-invariant Boolean observer, again with trivial induced action.
* `laneReduction` — the diagonal orientation action on a pair of lane states,
  projected to one coordinate. Its induced action is **not** trivial
  (`laneReduction_action_nontrivial`), so the structure is not inhabited only by
  orbit maps.

And one boundary, which is the correctly scoped version of the `support_*`
negatives (B12): `support_no_equivariant_action` shows the native-chart support
observer admits **no** map on the Boolean layer making the square commute for
the polarity generator, and `support_not_a_reduction` upgrades that to "no
`EquivariantQuotient` has `support` as its projection". The failure is therefore
prior to any binary law, and it is a statement about that observer's choice of
origin — the same action descends along `polarPresence`.

---

### 3.16 The weld — `Lean/Integration/StructuredObserver.lean`

`SymmetryResolvedObserver G Rich Coarse Res n` is the single object carrying both
theorem families: an `EquivariantQuotient`, a reopenable residual along the same
projection, a representation of the symmetry by inner-product-preserving maps
fixing the constant direction `ones n`, an intertwined reading and transverse
channel, and the two nondegeneracy witnesses.  From those,
`symmetry_resolved_theorem` proves symmetry-compatible coarse dynamics, faithful
fine-state recovery, and a strictly positive transverse Gram certificate that is
invariant under the symmetry — the last being the actual bridge, since it shows
the spine's geometric certificate is a function on the integration layer's
orbits.  `ObserverBuild.toObserver` builds the geometry automatically from finite
data.  `ssp369Observer` is the first inhabitant (nine SSP phase cells, orientation
monoid, visible polarity, retained phase); `polar6_no_equivariant_action` versus
`polarResultReduction` shows that retaining the residual *in the target* is
exactly what repairs equivariance.

### 3.17 Two finite physics lanes — `Lean/Integration/PhysicsInstances.lean`

The YM/NS path exclusion is lifted for exactly two modules and only for their
finite chart layers: the SU(2)/SO(3) axis-lift double cover (`3 × 2 = 6`, the
`TwoSheetedCoverInterface` mirrored and inhabited, `axisLiftObserver`) and the NS
Stage-3 receipt coordinates (`disposition × maturity ≃ 9`, `nsStage3Observer`),
plus the `3 × 3 = 9` operator-slot chart and the control that nine slots and nine
SSP phase cells are not canonically identified.
`physics_actions_factor_through_sign` proves the three lanes act through one
effective `ℤ/2`.  Nothing analytic is imported and no physical claim is made; see
`TOE_WELD_REPORT.md` for the full scope statement and frontier.

### 3.18 The order-three instance and `ℝ[C₃]`

The fourth inhabitant of the welded record acts by an honest `C₃`: `actWheel`
rotates the depth wheel of the SSP nine-cell carrier, fixing the lane polarity.
`actWheel_order_three` proves the generator is free with cube the identity;
`wheelReduction` is the resulting `9 → 3` orbit quotient; `wheelObserver` /
`wheel_theorem` give the three welded conclusions.  `phaseEmbed_rot` then
intertwines the corpus's `nextDepthWheelPhase` with `Spine.RealC3.shift`, so the
depth wheel carries the regular representation `ℝ[C₃]` and the spine's
`no_real_eigenvector_transverse` transfers to it (`wheel_no_invariant_line`):
the wheel's mean-zero plane is an irreducible real transverse plane, not a
dimension count.  This is the only registry row whose acting group is not an
effective `ℤ/2`; its *induced* coarse action is still trivial (it is an orbit
map), which is recorded as an open frontier item.

### 3.19 Towers — `Lean/Integration/ObserverTower.lean`

The welded record is closed under further reduction.  `compQuotient` composes
equivariant quotients for a shared symmetry; `Extension` packages one more level
(a further quotient of the visible layer, agreeing with the induced action, with
its own reopenable residual); `towerOf` produces the composite symmetry-resolved
observer, whose residual is the pair of residuals and whose representation,
reading and channel are carried through unchanged.  `tower_nondegeneracy` is the
point: the transverse certificate is *exactly* preserved by descending one more
level, so coarsening cannot manufacture or destroy transverse volume, and
`tower_card_bound` charges the loss to the residual.  The concrete tower is the
SSP lane reduced twice, `9 → 3 → 2` with residual `sign × phase` of size six
(`sspTower`, `sspTower_theorem`, `sspTower_cards`); `magnitudeStep_proper`
checks the second stage is a genuine reduction, not a relabelling.

### 3.20 Descent of the certificate — `Lean/Integration/ObserverDescent.lean`

`OrbitFibred O` (every fibre of the projection lies in one orbit) is the exact
hypothesis under which the welded transverse certificate stops being merely
orbit-constant and becomes a function of the *visible* state:
`nondegeneracy_descends` and `certificate_is_coarse_observable` produce a
strictly positive `coarseCertificate` with `nondegeneracy = coarseCertificate ∘
π`.  The `C₃` wheel instance satisfies the hypothesis
(`wheel_orbitFibred`, `wheel_certificate_descends`); the SSP orientation
instance does not (`ssp369_not_orbit_fibred`), since its flip moves between
fibres rather than within them.  The pair shows the hypothesis is load-bearing.

## 4. Frontier: exact remaining obligations

Stated as precise Lean-shaped goals, not aspirations. None of these is currently
proved anywhere in the repository.

1. **`projection2x9`.** The loom declares a `projection2x9` tag. No
   18-element carrier was found in the surveyed sources. *Obligation:* either supply a carrier `C`
   with `C ≃ ZMod 2 × ZMod 9` and an operation for the transport to preserve, or
   record the tag as vocabulary. (Currently recorded as an absence.)
2. **`projectionThreeStrand`.** Same status: declared as a tag, with no carrier and no
   map found in the surveyed sources. *Obligation:* a definition of the three-strand carrier and
   a map from the loom to it.
3. **Descent of the ternary algebra to the mask layer.** Now settled in the
   negative for the digit layer: `support_no_descent` and
   `polarPresence_no_descent` show that *no* binary Boolean operation works, for
   either Boolean observer. What remains open is the intermediate question:
   is there a quotient of the fabric algebra, strictly coarser than the ternary
   one and strictly finer than the Boolean mask, on which the XOR does descend?
   The `ZMod 2` symmetry quotient of §3.11 descends (row 29) but is an action,
   not the binary law.
4. **Domain instances.** The `ConstraintSystem` interface now has four
   instances (cuisine neutrality, loom, publication, cognition) and the
   `RefinementSystem` record has two (loom, addresses). *Obligation:* biology,
   governance and crypto modules that use "refinement" vocabulary still have
   none; each would need a Lean mirror of its Agda source followed by `Level`,
   `StateAt`, `Refines`, `project` and a coherence proof.
5. **Receipt sockets generally.** `DASHI.Core.GenericReceipt` has in-degree 108.
   `alignment_unconstrained` shows the archetype constrains nothing.
   *Obligation:* for each heavy consumer, either add the alignment field (as in
   `AlignedReceipt`) or prove the analogous underdetermination.
6. **`Ultrametric` consumers beyond the Lean cutset.** §3.7 classifies every
   instance that exists in Lean. *Obligation:* the Agda corpus has many more
   consumers of the record (in-degree 73 at module level); each is either
   another prefix geometry, provable by the same route, or an outlier like the
   walk distance, and none has been checked.
7. **Agda recheck.** No Agda module has been typechecked in this environment.
   *Obligation:* run `agda --safe` over the non-YM/NS cutset to confirm the Lean
   mirrors' sources are themselves checkable; until then "the Agda proves X" in
   this document means "the Agda source states X".
8. **Mirror faithfulness.** The 107 `AgdaMirror` modules are hand transcriptions.
   Two mechanical layers now audit them (see §1.5): `MIRROR_PROVENANCE.md` at
   *name* level, exposing the dangling citation, the three mirrors with no
   declared source, and the Agda declarations with no same-named Lean
   counterpart; and `MIRROR_SIGNATURES.md` at *signature-shape* level, comparing
   arity and conclusion head for the 515 name-matched pairs (96.1 % agree) and
   listing the 20 disagreements as a review queue, together with the check that
   no Agda `postulate` is mirrored under the same name. Neither is faithfulness:
   nothing yet checks that a mirrored theorem *states* its Agda original, and two
   different propositions can share a shape. *Obligation:* a statement-level
   comparison, which needs an Agda toolchain (item 7). This remains the largest
   soundness gap between the Lean results and any claim about the Agda corpus,
   though it is now a smaller and an enumerable one.
9. **The SSP/Hecke intertwiner.** `SSPRepresentationHeckeIntertwinerBoundaryExact.agda`
   asks for a commuting square `Φ ∘ R_p = T_p ∘ Φ` between a representation-side
   action and the SSP transport, and records that it has not been constructed.
   Nothing in this pass constructs it either: §3.11 supplies the SSP side (a
   monoid with functorial transport), and the representation side has no Lean
   carrier at all in this cutset. *Obligation:* a carrier for `R_p`, a map `Φ`,
   and the square — which would be an `Evidence.provedEquivariance` row, or
   equivalently an `EquivariantQuotient` instance in the sense of §3.15. The
   shape of the obligation is now typed; nothing about it is discharged.
10. **The transported nonary law in the corpus.** `nonaryPhaseAdd` (row 23) is
   defined here, not in the Agda: the source has both halves (the chart and
   `q9Add`) and never composes them. *Obligation:* add the operation on the Agda
   side and re-derive the exponent-three law there, so that the corpus's nine
   labels carry both algebras explicitly.

---

## 5. How to check this

```
lake build Integration                     # the whole spine
lake build Integration.AxiomAudit          # prints axioms of every headline result
python3 scripts/mirror_provenance.py       # name-level mirror census
python3 scripts/mirror_signature_compare.py  # signature-shape comparison
```

`Integration.AxiomAudit` prints, for every result named above, a dependency set
contained in `{propext, Classical.choice, Quot.sound}`. There is no `sorry`, no
project axiom, and no `native_decide` (no `Lean.ofReduceBool`) anywhere in the
spine.
