# Presentation independence, gauge algebra, observational thresholds

**Scope of this report.** It documents the tranche added on top of the gauge /
observer weld described in `TOE_GAUGE_DESCENT_REPORT.md`, and states the
remaining obligations honestly. Everything named below is a Lean declaration in
this repository that compiles under `lake build` (full build, no `sorry`), and
every headline result is listed in `Lean/Integration/AxiomAudit.lean` or
`Lean/Spine/AxiomAudit.lean`, where it is shown to depend only on `propext`,
`Classical.choice` and `Quot.sound` (several depend on fewer, and some on none).

No Yang–Mills and no Navier–Stokes material is imported, referenced or restated
anywhere in this tranche. No physical claim, and no claim about the Riemann
zeta function or its zeros, is made. The Agda tree is read-only here (no Agda
toolchain is available in this environment), so nothing below asserts that any
Agda file has been rechecked; where an Agda module is mentioned it is as the
conceptual source of a pattern that has been *re-proved in Lean*.

---

## 1. The certificate no longer depends on how the carrier is listed

`Lean/Integration/EnumInvariance.lean`.

The welded transverse certificate is built from an enumeration
`enum : Rich ≃ Fin n`. Until now nothing ruled out its numerical value
depending on that choice. It does not.

* `permVec`, `inner_permVec`, `norm_sq_permVec`, `avg_permVec`,
  `meanPart_permVec`, `fluct_permVec` — reindexing a coordinate vector by a
  permutation preserves the inner product, the mean, the mean part and the
  fluctuation.
* `area2_permVec` — hence it preserves the transverse Gram defect.
* `readVec_reindex`, `channelVec_reindex` — the two vectors entering the
  certificate are literally permuted when the enumeration changes, by the
  permutation `reindex e₁ e₂`.
* **`nondegeneracy_reindex`** (and `nondegeneracy_reindex'` for the
  invariant-class constructor) — *for any two enumerations `e₁ e₂` of the same
  carrier, the certificates agree pointwise.*
* `certificate_presentation_independent` — the same statement packaged as the
  claim that the certificate is a function of the structured carrier alone.
* `det_gram_reindex` — the Gram determinant of a finite family is unchanged by
  permuting the family (via `Matrix.det_submatrix_equiv_self`), which is the
  rank-`r` counterpart of `area2_permVec`.

This is the item the design note ranked first, and it is now closed for the
certificate as this corpus defines it. **Caveat, stated precisely:** the theorem
is invariance under change of *enumeration of a fixed finite carrier*. It is not
a statement that two different carriers, or two different class coordinates,
give the same number — they do not, and `Lean/Integration/CertificateFormula.lean`
shows exactly what the number depends on.

## 2. The certificate in closed form

`Lean/Integration/CertificateFormula.lean`.

* `channelVec_eq_indicator(')` — the channel vector is the indicator of the
  class of the state.
* **`nondegeneracy_eq(')`** — with `n` the carrier size and `m` the size of the
  class of `x`, the certificate equals

  ```
  (n + 3) · (m − m²/n) − (1 − m/n)²
  ```

  so it depends on exactly two integers: the carrier size and the class size.
* `nondegeneracy_eq_of_card_eq(')` — the specialisation used by the lanes.

This independently reproduces the previously hand-computed axis values
`107/9` (class size 4) and `104/9` (class size 2) at `n = 6`, and it is what
makes the threshold computations in §5 mechanical rather than case-by-case.

## 3. Gauge composition as genuine subgroup algebra

`Lean/Integration/GaugePreimage.lean`.

Previously `compGauge_redundant_iff` only *characterised* the set of symmetries
that a two-stage reduction makes redundant. That set is now an object.

* `PreimageCarrier A Bq` — the preimage `quot₁⁻¹(K) ⊆ G`, carrying the inherited
  monoid structure.
* `compGaugeQuotient` — the composite gauge datum `H_comp → G ↠ P` built from
  it, with `inclFirst` embedding the first-stage subgroup.
* **`compGaugeQuotient_exact`** — the composite datum is exact: the kernel of
  `G ↠ P` is exactly the preimage subgroup. This is the composition law
  `(G/H)/K ≅ G/quot⁻¹(K)` in the form this library can use.
* `quot_inv`, `preimage_inv_mem`, **`preimage_normal`** — in the group case the
  preimage is closed under inverses and is normal whenever `K` is.
* `compGaugeExact`, `compGaugeExact_redundant_iff`,
  `compGaugeExact_effective_iff` — the composite *reduction* with the honest
  gauge subgroup in place, so `redundant_iff_gauge` survives composition.

## 4. Sufficiency: tower-relative and intrinsic

`Lean/Integration/LeastSufficient.lean`.

The tower notion (`CoarsestSufficient` in `Integration.DescentLevel`) is now
related to the order-theoretic one.

* `Sufficient o c` — `o` determines `c` (constant on the fibres of `o`);
  `Refines o o'` — `o'` factors through `o`.
* **`sufficient_iff_refines`** — `o` is sufficient for `c` exactly when `c`
  factors through `o`.
* **`canonical_least`** — `c` itself, viewed as an observer, is refined by every
  observer sufficient for `c`: the canonical observer is least informative among
  sufficient ones.
* `factorsAt_iff_sufficient`, `coarsest_iff_last_refining` — the bridge to the
  tower vocabulary.
* `CoarsestSufficientBelow`, `exists_coarsestBelow`, `coarsestBelow_unique`,
  **`coarsest_of_coarsestBelow`**, `coarsestBelow_of_coarsest` — the bounded
  notion the design note asked for, distinguishing *last sufficient layer before
  loss* from *coarsest sufficient layer within a finite horizon*. Within a
  horizon `N` a coarsest-sufficient-below level always exists and is unique;
  it upgrades to the unbounded notion exactly when it is not the horizon.
* `Equivalent`, `equivalent_canonical_iff`, **`coarsest_equivalent_canonical`**,
  `coarsest_strictly_finer` — when a tower's coarsest sufficient layer *is* the
  intrinsic least sufficient observer (namely when the invariant also determines
  that layer), and what it is when it is not: strictly more informative than the
  invariant.
* `axis_coarsestBelow`, `su2_coarsestBelow` — the two existing lanes placed in
  the bounded framework (the SU(2) lane factors at every level, so its bounded
  answer is the horizon itself, consistent with `su2_no_coarsest`).

## 5. The SSP observational threshold

`Lean/Integration/SSPThreshold.lean`.

* `ssp_class_card`, **`ssp_cert_constant`**, `ssp_factorsAt_all`,
  **`ssp_no_threshold`** — for the gauge weld's *own* channel every polarity
  class has three cells, so by §2 the certificate is constant on the nine cells
  and factors at every level: this tower has no threshold.
* `sspZeroBuild` / `sspZeroObserver` — the same nine cells with an invariant,
  zero-detecting class coordinate. Then `sspZero_cert_zero = 212/9`,
  `sspZero_cert_nonzero = 215/9`, so the certificate separates states.
* `sspZero_factorsAt_one`, `sspZero_not_factorsAt_two`,
  **`sspZero_coarsest_sufficient`**, `sspZero_threshold_is_one` — the threshold
  is exactly `k = 1`: polarity suffices, the further merge destroys the
  invariant.
* `sspZero_not_refines_layer`, **`sspZero_coarsest_strictly_finer`** — the
  threshold layer is *not* equivalent to the canonical observer: the certificate
  cannot separate the two nonzero polarities, so the layer is strictly more
  informative. This is the negative side of §4.
* **`ssp_threshold_dichotomy`** — both facts together: on one and the same
  9 → 3 → 2 tower, whether a threshold exists is a property of the channel, not
  of the carrier.

## 6. Orbit–stabilizer bounds on the hidden information

`Lean/Integration/OrbitResidual.lean`.

* `residual_injOn_fibre` — exact reopening forces the residual to be injective
  on each fibre of the projection (the general principle behind the earlier
  cardinality bounds).
* `orbitProj`, `residual_orbit_injective` — for an orbit projection the residual
  is injective on each orbit.
* `card_orbit_le_card_residual`, **`index_stabilizer_le_card_residual`**,
  `card_group_le_card_residual` — hence `[G : Stab x] ≤ |Res|`: the hidden
  information is at least the orbit's symmetry index.
* `cosetResidual`, **`cosetResidual_injective`**, `cosetResidual_apply` — more
  than a bound: reading the residual along a coset of the stabilizer gives a
  canonical *injection* `G ⧸ Stab x ↪ Res`, so the residual literally records
  which coset was used.

**Honest limit.** The embedding `G ⧸ Stab x ↪ Res` is proved; a *bijection*
`R_[x] ≅ G ⧸ Stab x` is not — surjectivity would need a minimality hypothesis on
the residual presentation, which is not assumed anywhere here.

## 7. When a certificate pays for a defect

`Lean/Integration/CertificatePays.lean`.

* `Pays C D c` — `c · D i ≤ C i` pointwise.
* **`sum_defect_le_of_budget`** (and the `Finset` version) — a certificate
  budget `∑ C ≤ B` with a payment rate `c > 0` yields the defect budget
  `∑ D ≤ B / c`.
* `sites_le_of_budget`, `pointwise_defect_le_of_budget` — counting and pointwise
  corollaries.
* **`weighted_budget_not_uniform`** — the honest negative: a bounded weighted
  aggregate does *not* bound the local defect uniformly.
* `exists_certificate_floor`, `welded_sites_le_of_budget` — the welded observer
  supplies a strictly positive floor, so the abstract theorem applies to it.

This is the abstract shape of "the certificate controls an expenditure". It is
*not* an analytic or dynamical theorem: no differential inequality, no evolution
equation and no lane-specific quantity appears.

## 8. Hidden-variable elimination: the Schur complement, owned once

`Lean/Spine/SchurComplement.lean` (new in this tranche).

* `coupled a b d x y = a x² + 2x⟪b,y⟫ + d y`, `schur a b d y = d y − ⟪b,y⟫²/a`.
* `coupled_eq_schur_add` — completing the square.
* **`schur_isLeast`**, `schur_eq_iInf` — the Schur complement *is* the minimum
  of the coupled form over the hidden variable, attained at `−⟪b,y⟫/a`.
* **`schur_coercive`** — the quantitative transfer: visible floor `δ`, coupling
  ceiling `η`, effective floor `δ − η`.
* **`schur_norm_sq`** — eliminating the direction `u` from `‖x • u + y‖²`
  returns exactly `area2 u y / ‖u‖²`. The transverse Gram defect of
  `Spine.TransverseGram` *is* a Schur complement.
* `schur_pos_iff_area2_pos` — so effective positivity and transverse
  nondegeneracy are literally the same condition.

**Honest limit.** The hidden block is one-dimensional. The matrix-block form
`S = D − BᵀA⁻¹B` with a vector hidden space is not proved here.

## 9. Consumers: invariant, equivariant, gauge-sensitive

`Lean/Integration/ConsumerGauge.lean` (new in this tranche).

* `Invariant`, `Equivariant`, `Sensitive`, with
  `invariant_iff_not_sensitive`, `invariant_iff_equivariant_trivial`,
  `invariant_of_equivariant_trivial`, `Invariant.comp`,
  `Equivariant.comp_of_target_invariant` (how a covariant quantity is turned
  into an invariant one).
* **`exists_factor_of_invariant`** / `invariant_of_orbit_consumer` — the
  universal property: invariant consumers are exactly the consumers of the orbit
  quotient.
* `gauge_consumer_invariant`, `red_equivariant`, `red_sensitive_of_effective` —
  for any gauge reduction: every consumer of the visible carrier is
  gauge-invariant, the visible carrier is equivariant for the coarse action, and
  effectiveness makes it sensitive to the surviving symmetry.
* **`ssp_consumer_trichotomy`** — the three classes realised on one nine-cell
  state: the transverse certificate is invariant under all of `C₃ × C₂`; the
  visible lane is gauge-invariant, equivariant, and sensitive to the surviving
  `C₂`; the retained wheel-phase residual is sensitive to the gauge subgroup
  itself, which is exactly the information the reduction discards.

## 10. Exact versus certified-approximate intertwiners

`Lean/Integration/ApproximateIntertwiner.lean`.

* `IsIntertwiner Φ R T` — `Φ ∘ R = T ∘ Φ`; `IsApproxIntertwiner … ε` — the
  metric version `d(Φ(Rx), T(Φx)) ≤ ε`.
* `approx_of_exact(_le)`, `exact_of_approx_zero` — the two tiers agree at
  `ε = 0`.
* **`approx_comp`** — additive error under composition when the downstream map
  is nonexpansive; `approx_iterate` — `n · ε` under iteration.
* `certificate_intertwiner`, `certificate_approx` — the welded certificate is an
  exact intertwiner for the symmetry action, so it sits in the strongest tier.

**This is not a Hecke theorem.** No Hecke operator, modular form or
representation-theoretic object appears anywhere in this repository. What exists
is the tiering discipline — exact ⊂ certified approximate ⊂ unverified analogy —
and the arithmetic of the middle tier.

---

## Dependency / provenance map for this tranche

```
Spine.Observer  ─┬─▶ Spine.TransverseGram ──▶ Spine.SchurComplement
                 │        (area2 core)            (elimination = area2)
                 └─▶ Spine.MeanSplit
                          │
Integration.StructuredObserver ──▶ Integration.EquivariantChannel
     │                                     │
     │                                     ├─▶ Integration.EnumInvariance   (§1)
     │                                     └─▶ Integration.CertificateFormula (§2)
     │                                                   │
     ├─▶ Integration.GaugeReduction ──▶ Integration.GaugePreimage (§3)
     │            │
     │            ├─▶ Integration.GaugeObserver ─┬─▶ Integration.GaugeSU2
     │            │                              └─▶ Integration.GaugeSSP
     │            │                                        │
     │            └────────────────────────────────────────┼─▶ Integration.ConsumerGauge (§9)
     │                                                     │
     ├─▶ Integration.ObserverTower ──▶ Integration.DescentLevel
     │                                     ├─▶ Integration.LeastSufficient (§4)
     │                                     └─▶ Integration.SSPThreshold    (§5)
     │
     ├─▶ Integration.ResidualQuotient ──▶ Integration.OrbitResidual (§6)
     ├─▶ Integration.CertificatePays (§7)
     └─▶ Integration.ApproximateIntertwiner (§10)

All of the above are imported by `Lean/Integration.lean` (items 20–28) or
`Lean/Spine.lean`, and audited in the two `AxiomAudit.lean` files.
```

Conceptual provenance (patterns re-proved in Lean, not Agda files rechecked):
the least-sufficient-observer order (§4) follows the shape of
`DASHI/Core/ConsumerDescentMinimalObserverExact.agda`; the fibre-injectivity
lower bound (§6) that of `DASHI/Core/ResidualFibreLowerBoundExact.agda` and
`OrbitStabilizerResidualPresentationExact.agda`; the composition of residuals
that of `RecoverableQuotientCompositionExact.agda`; the additive-error tier
(§10) that of `ApproximateIntertwinerCompositionExact.agda`.

---

## Frontier: exactly what is not proved

1. **Canonical orbit–stabilizer residual.** §6 proves the canonical injection
   `G ⧸ Stab x ↪ Res` and the index bound. The *bijection*
   `R_[x] ≅ G ⧸ Stab x` — equivalently surjectivity of the coset reading under a
   minimality hypothesis on the residual presentation — is open here.
2. **Matrix-block Schur complement.** §8 proves the one-dimensional-hidden-block
   case. `S = D − BᵀA⁻¹B` for a vector hidden space, its minimum
   characterisation, and the `S ≥ (δ − η)I` operator inequality are not proved.
3. **Non-finite gauge instance.** §9's instances are finite carriers
   (nine cells). No `U(1)`/phase gauge instance, and no invariance statement for
   a Hermitian form under a continuous group, exists in this repository.
4. **Certificate-controls-dynamics.** §7 is a budget-arithmetic theorem. There
   is no evolution equation, no differential inequality, and therefore no claim
   that any certificate controls any dynamical quantity.
5. **Hecke square.** `Φ ∘ R_p = T_p ∘ Φ` is not stated for any Hecke operator;
   §10 supplies only the tiering machinery. Bridging out of the finite-chart
   world remains the largest open step.
6. **Global versus tower-relative sufficiency.** §4 now proves both directions
   (`coarsest_equivalent_canonical`, `coarsest_strictly_finer`) and §5 exhibits
   a lane where the coarsest layer is strictly finer than the canonical
   observer. What is still missing is a construction that *inserts* the
   canonical observer into a given tower, i.e. a canonical refinement of a tower
   whose coarsest sufficient layer is always equivalent to the canonical
   observer.
7. **Agda side.** No Agda module has been typechecked in this environment. Every
   claim above is a Lean claim about Lean definitions.

## What this tranche does *not* claim

It does not claim a physical theory of everything, a mass gap, a regularity
result, or anything about the Riemann hypothesis. It does not claim that the
finite carriers used as instances *are* `SU(2)`, `SO(3)`, or any Lie group; they
instantiate the same quotient *pattern* `G → G/H` and nothing more. It does not
claim that shared terminology between modules constitutes a mathematical link:
every link asserted above is a Lean import plus a Lean theorem.
