# The QFT/GR common-variation frontier — audit and the smallest theorem cutset

This round does the thing the handoff asked for: a fresh audit of the
common-action / stress-weld lane, and a collapse of the QFT/GR frontier into the
smallest set of statements that are *actual mathematics* rather than further
architecture — with those statements proved in Lean where they are tractable,
and the rest listed exactly.

Lean: `Lean/Integration/Variation/` (seven modules), wired into the `Integration`
aggregate and audited in `Lean/Integration/AxiomAuditVariation.lean`.

## 0. Sources and what was checked

| source | status |
|---|---|
| `toe-dashi-full-agda-and-lean-handoff-20260830.tar.gz` → `agda-suite/` (Agda master `758e1cfa`) | read here; the common-action lane below was read module by module |
| the follow-up frontier overlays described in the handoff message (the finite→continuum stress follow-up and the common metric-variation language) | **not present in the pinned baseline.**  A whole-archive name search finds no `CommonMetricVariation*`, `PairingSeparation*`, `*ContinuumStress*Interchange*` module.  They are treated here as *described* frontier statements, not as code that was read |
| this project's Lean corpus | the tranche below is new; no Yang–Mills or Navier–Stokes Lean file was read, referenced or modified |

No Agda toolchain is available in this environment, so **nothing in the Agda
suite was re-typechecked**; the classification below is a reading of the source
text, not a machine check.

## 1. Audit of the Agda common-action lane (master `758e1cfa`)

The lane is five modules deep.  Classified honestly:

| module | definitions / interfaces | checked proof terms | obligations (record fields) | Bool ledger |
|---|---|---|---|---|
| `Foundations/SameCandidateQFTGRRecoveryExact` | `UnifiedCandidate` — a large record of carriers (`Candidate`, `Regime`, `SharedStressEnergy`, the recovery tokens, `grStressToShared`, `qftSectorStressToShared`, `QFTStressAggregation`) | the promotion compilers | every physical recovery is a token or a `Set`-valued field | — |
| `Foundations/CommonEffectiveActionVariationExact` | `CommonEffectiveActionVariation` | `variationBuildsSharedEffectiveSource`, `commonVariationImpliesStressWeld` | `effectiveSourceVariation` (the "variation" is a *field*, not a derivative), `sourceVariationCommutesWithCoarseGraining` | `CommonActionVariationBoundary` (4 flags) |
| `Foundations/EinsteinCommonActionVariationFrontierExact` | `EinsteinTensorVariationReceipt` | `einsteinTensorVariationBuildsGRIdentification` (routes through the literal field equation `G = T`) | `commonVariationEqualsEinsteinTensor` | `EinsteinVariationBoundary` (3 flags) |
| `Foundations/BalabanCommonActionVariationFrontierExact` | `BalabanSectorFlow`, `BalabanSectorMetricVariation` (with an explicitly owned `stressMetricPairing`), `BalabanAllSectorVariationReceipt` | `balabanSectorFirstVariationIsLiteralStressPairing`, `balabanSectorFamilyBuildsQFTVariationIdentification`, `balabanSectorSection2FormAvailable` | `densityFirstVariationRepresentedByLiteralSectorStress`, `commonVariationIsAggregateLiteralSectorStress`, `aggregateLiteralSectorStressIsDeclaredTotal` | `BalabanCommonVariationBoundary` (6 flags) |
| `Foundations/CommonActionQFTGRVariationCompilerExact` | — | `commonEinsteinAndBalabanVariationImpliesStressWeld` | — | `CommonActionQFTGRCompilerBoundary` (3 flags) |

Reading of the audit, in one line: **the compiler layer is complete and the
physics is entirely in the record fields.**  Every arrow from "receipts" to
"stress weld" is a checked proof term; every arrow from *anything physical* to a
receipt is a field to be supplied.  The `*Boundary` records are `Bool`-valued
ledger entries with `≡ false`/`≡ true` proofs: they record intent, and prove
nothing about metrics, actions or stress tensors.

Two corrections that the lane has already absorbed, and which this round keeps:

* a *single* pure-gauge sector density is never identified with total gravitating
  stress — aggregation over sectors is explicit;
* the first metric variation is a *functional* of a perturbation `h`, related to
  a stress *tensor* only through an owned pairing.

## 2. The collapse: seven statements, six of them now proved

Stripping the architecture away, the frontier is exactly this list.  "Proved"
below means a Lean theorem in this repository with no `sorry` and only
`propext`, `Classical.choice`, `Quot.sound`.

| # | statement | status |
|---|---|---|
| A | **Einstein-side first variation.**  `δ_g S_common[h] = ⟨G, h⟩` for the actual common action | **open**, but its first computational ingredient is now discharged: `MetricDensity.hasDerivAt_det_add_smul` is Jacobi's formula `d/dt det(g + t h)|_0 = det g·tr(g⁻¹ h)`, and `MetricDensity.hasDerivAt_sqrt_neg_det` is the volume-density variation `δ√(-g) = ½√(-g) g^{μν}δg_{μν}`.  The curvature terms, the manifold and the integration remain entirely absent |
| B | **Pairing separation.**  Equality of pairings against all admitted `h` ⇒ equality of tensors | **proved** — `Pairing.eq_of_pair_eq_on_spanning`, sharpened to an iff (`Pairing.separates_iff_eq_top`): *algebraic* separation holds exactly when the admitted fibre is everything.  Sharpened again topologically: `Pairing.eq_of_pair_eq_on_dense` separates from a merely **dense** fibre, and `Pairing.separates_iff_dense` shows density is exactly the condition over a complete space — the physically attainable form |
| C | **Finite cutoff → continuum.**  `δ_g S_k[h] = ⟨T_k,h⟩`, `δ_g S_k[h] → δ_g S_∞[h]`, `⟨T_k,h⟩ → ⟨T_c,h⟩` ⇒ `δ_g S_∞[h] = ⟨T_c,h⟩`; and the existence of `T_c` | **proved** — `CutoffLimit.scalar_limit_interchange` for the interchange, and `CutoffLimit.exists_unique_continuum_stress` for the stronger statement that `T_c` need not be postulated: pointwise convergence of the cutoff pairings on a complete perturbation space *produces* a unique continuum stress (Banach–Steinhaus + Riesz) |
| D | **Sector aggregation** commuting with the pairing and with the cutoff limit | **proved** — `CutoffLimit.sector_aggregate_variation` and `CutoffLimit.sector_aggregation_commutes_with_cutoff_limit` for a `Finset` of sectors, and `CutoffLimit.sector_aggregate_variation_tsum` (via `Pairing.pair_tsum`) for an infinite summable family |
| E | **One common perturbation language.**  Both sectors induced from one carrier, with the weld as a consequence | **proved** — `CommonLanguage.CommonVariation`, `CommonLanguage.stress_weld_of_common_carrier`, its dense-fibre strengthening `CommonLanguage.stress_weld_of_dense_carrier`, and `CommonLanguage.stress_weld` |
| F | **Source-coordinate discipline.**  `D²(E∘A) = D²E[A',A'] + DE[A'']` | **proved** — in one dimension (`SourceCoordinate.second_deriv_comp`, with the affine corollary and an explicit counterexample to the naive identification) and on arbitrary Banach spaces (`SourceCoordinate.second_fderiv_comp`, `second_fderiv_comp_of_const_fderiv`), plus the sharp negative `correction_is_detected_by_a_linear_energy`: a nonzero `D²A[v,w]` is already visible to some *linear* energy |

| G | **The physical fibre is symmetric.**  A metric perturbation is a symmetric 2-tensor, so the separation step of B must survive restriction to that proper subspace | **proved** — `SymmetricFibre.eq_of_trace_eq_on_symmetric` (symmetric perturbations separate *symmetric* tensors) together with `SymmetricFibre.symmetric_perturbations_do_not_separate_general_tensors` (and nothing more).  Packaged as `SymmetricFibre.symmetry_of_the_stress_is_load_bearing` |

`Variation.Weld.qftgr_stress_weld_of_cutset` assembles B–E into one implication:
a GR receipt, finite-cutoff sectorwise receipts, cutoff convergence, aggregation
and a *dense* admitted fibre give unique continuum sector stresses **and**
`G = Σ_i T_c^(i)`.  Its hypothesis list *is* the remaining frontier.

## 3. What the negatives rule out

The value of this tranche is as much in the negatives as the positives: each one
shows that a step the architecture might treat as bookkeeping is load-bearing.

| negative | what it kills |
|---|---|
| `Pairing.exists_ne_agreeing_of_ne_top`, `Pairing.plane_pairing_does_not_separate` | a variational identity on a proper admitted fibre never determines a tensor; no relabelling repairs it |
| `CommonLanguage.mismatched_carrier_maps_do_not_weld` | two maps out of a common carrier that are *separately* called "the metric variation": both receipts hold, the fibre spans, and still `G ≠ T` |
| `CommonLanguage.non_spanning_fibre_does_not_weld` | one common map but a fibre that only probes part of the space |
| `CommonLanguage.separate_actions_do_not_weld` | two separately named actions with no common carrier constrain nothing |
| `CutoffLimit.pairing_convergence_is_not_tensor_convergence` (with an explicit `ℓ²` witness) | pairing convergence is *weak*: the finite stresses may converge in every pairing and not converge at all as tensors |
| `CutoffLimit.divergent_cutoff_family_has_no_continuum_pairing` | the convergence hypothesis is not free |
| `CutoffLimit.one_sector_is_not_the_total` | sector aggregation is not a relabelling |
| `SourceCoordinate.naive_hessian_identification_fails` | identifying a substituted-coordinate Hessian with the bare one |
| `SourceCoordinate.correction_is_detected_by_a_linear_energy` | the hope that the `D²A` correction is an artefact of a curved energy: a linear energy, with no Hessian of its own, already sees it |
| `MetricDensity.density_variation_does_not_determine_the_perturbation` | the density factor as a source of separation: `δ√(-g)` annihilates a nonzero perturbation whenever the index set has two elements |
| `SymmetricFibre.symmetric_perturbations_do_not_separate_general_tensors` | welding a *non-symmetric* stress on the physical fibre: the antisymmetric part is invisible to every symmetric perturbation |

## 4. Dependency and provenance map

```
Integration.Variation.Pairing            (Mathlib inner-product spaces; no project dependency)
        │
        ├── Integration.Variation.CutoffLimit      (+ Banach–Steinhaus, Riesz, ℓ²)
        ├── Integration.Variation.CommonLanguage
        └── Integration.Variation.Weld  ← CutoffLimit, CommonLanguage

Integration.Variation.SourceCoordinate   (Mathlib calculus only; independent of the others)
Integration.Variation.MetricDensity      (Mathlib matrices + calculus; independent of the others)
Integration.Variation.SymmetricFibre     (Mathlib matrices only; independent of the others)

Integration.AxiomAuditVariation ← all seven
Integration (aggregate) ← all seven + the audit
```

Provenance of the *statements*: items A–E are the frontier statements as set out
in the handoff for the common metric-variation language and the finite→continuum
stress follow-up; item F restates the second-order chain-rule correction that
the merged source-coordinate work made in a different setting.  Provenance of
the *proofs*: all new, all in Lean, none transcribed from Agda.  No Agda module
is claimed to be mirrored, and no Agda proof term is claimed to have been
rechecked.

## 5. Honest frontier — the exact remaining obligations

1. **The Einstein-Hilbert first variation (item A).**  Nothing here derives
   `δ_g S[h] = ⟨G, h⟩` for any action.  This is the single largest open item and
   it is analytic, not architectural.
2. **The perturbation space is abstract.**  `H` is a real inner-product space.
   Physical metric perturbations are symmetric 2-tensor *fields* with density
   factors, index conventions and a Lorentzian signature.  Lane 6
   (`SymmetricFibre`) now handles the symmetry restriction honestly in the
   matrix model — symmetric perturbations separate symmetric tensors and
   nothing more — and lane 5 supplies the `√(-g)` density factor, but the
   *field* character, the index placement and the signature are still not
   modelled anywhere.
3. **The Riesz step needs a Hilbert structure.**  Partly relieved:
   `CutoffLimit.exists_unique_continuum_functional` gives the unique continuum
   *functional* on any Banach perturbation space, so only the representation of
   that functional *by a tensor* still needs completeness and an inner product.
   A continuum stress that is genuinely a distribution — a functional on a
   non-normable test space — is still outside this model.
4. **Density is assumed, never verified.**  Every weld theorem takes "the
   admitted image is dense" (previously: spans) as a hypothesis.
   `Pairing.separates_iff_dense` shows this is the sharp condition and cannot be
   weakened further, but for a physical fibre it is a real nondegeneracy
   statement about the pairing, and it is not discharged here.
5. **Convergence is assumed, never verified.**  The finite→continuum theorems
   take pointwise convergence of the cutoff pairings as input; no estimate is
   proved for any concrete cutoff family.
6. **Infinite aggregation needs summability.**  `sector_aggregate_variation_tsum`
   covers an infinite family, but only under `Summable T`; a merely conditionally
   convergent or renormalised sector sum, and a *limit* of sector sums along a
   filter, are not covered.
7. **The source-coordinate law is second order only.**  Discharged for the
   second variation in both the one-dimensional and the Banach-space setting
   (`second_fderiv_comp`), but nothing is proved about third and higher
   variations, and the substitution is assumed `C²` everywhere — no version with
   only local or Sobolev regularity is given.
8. **The density lane is not the Einstein tensor.**  `MetricDensity` computes
   `δ det g` and `δ√(-g)` for a single invertible matrix.  It says nothing about
   `δ(R√(-g))`: no Christoffel symbols, no Ricci or scalar curvature, no
   Palatini identity, no manifold, no integration and no boundary term.  Closing
   item A needs all of those.
9. **The Agda side is unchanged and unchecked.**  No Agda file was modified, and
   no Agda module was typechecked in this environment; the audit in §1 is a
   source reading.  Wiring these Lean results back into the Agda receipts would
   require an Agda-side transcription that this round did not attempt.

## 6. Claim boundary

Every theorem in `Lean/Integration/Variation/` is a statement about Lean
definitions over real inner-product spaces, Banach spaces, real matrices,
sequences and real functions.  None
of them says that any physical theory has a common action, that general
relativity and quantum field theory share a metric-variation language, that a
continuum stress tensor exists for Yang–Mills or any other field theory, or that
a theory of everything has been obtained.  The word "stress" names an element of
an inner-product space; "cutoff" names a natural-number index; "sector" names an
element of a finite index set.  What is proved is the algebra and analysis of
the weld: which hypotheses force `G = T`, and which do not.
