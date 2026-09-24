import Mathlib
import Integration.Variation.Pairing
import Integration.Variation.CutoffLimit
import Integration.Variation.SectorFilter
import Integration.Variation.Weld

/-!
# Continuum-producer reconciliation — endpoint sector variation and aggregation

`DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact` carries a
producer record whose sector data is *endpoint* data: for each sector a
continuum first variation, together with the assumed identity

```
sectorContinuumVariationIsLiteralStressPairing :
  sectorContinuumFirstVariation group candidate regime perturbation
    ≡ stressMetricPairing (…) perturbation
```

and a two-entry boundary ledger:

* `downstreamCommonActionNeedsIndependentConvergenceRelation ≡ false`;
* `endpointSectorVariationPlusExactAggregationIsSufficient ≡ true`.

Both entries are `Bool`s pinned by `refl`.  This module states them against the
Lean variational model and settles them:

* `endpoint_aggregation_suffices` — endpoint sector receipts plus exact
  aggregation over a dense admitted fibre determine the common stress, with
  **no convergence hypothesis anywhere in the hypothesis list**.  This is the
  `true` entry, and reading the same hypothesis list is what refutes the `false`
  one (`ledger_false_entry_is_refuted`).
* `endpoint_aggregation_suffices_tsum` — the infinite-family version, under
  summability of the sector stresses.
* the summability hypothesis of the infinite version is not decoration:
  `exact_aggregation_needs_the_right_total` exhibits a sector family whose
  partial sums along an exhaustion converge to a nonzero vector while its `∑'`
  is zero, so "exact aggregation" has to name *which* total is meant.

## Reading discipline

Lean statements about Lean definitions.  No Agda module is typechecked, no Agda
proof term is transported, and no claim is made that any physical sector family
satisfies the endpoint receipts, the density hypothesis or the aggregation
identity — those remain the physical frontier.
-/

namespace Integration.Reconciliation.ContinuumProducerBoundary

open scoped InnerProductSpace RealInnerProductSpace
open Filter
open Integration.Variation
open Integration.Variation.Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Endpoint sector variation plus exact aggregation is sufficient.**  If the
common variation is represented by `G` on a dense admitted fibre, each sector's
*continuum* variation is literally a stress pairing, and the common variation is
the finite sum of the sector variations, then the common stress is the sum of
the sector stresses.

There is no convergence hypothesis: the cutoff limit has already been taken in
the endpoint data. -/
theorem endpoint_aggregation_suffices [CompleteSpace H] {ι : Type*} (s : Finset ι)
    (K : Submodule ℝ H) (hdense : Dense (K : Set H))
    (deltaCommon : H → ℝ) (G : H)
    (hGR : ∀ h ∈ K, deltaCommon h = pair G h)
    (deltaSec : ι → H → ℝ) (Tc : ι → H)
    (hsec : ∀ i ∈ s, ∀ h, deltaSec i h = pair (Tc i) h)
    (hagg : ∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSec i h) :
    G = ∑ i ∈ s, Tc i := by
  refine eq_of_pair_eq_on_dense_submodule G (∑ i ∈ s, Tc i) K hdense (fun v hv => ?_)
  rw [← hGR v hv, hagg v hv, pair_sum]
  exact Finset.sum_congr rfl (fun i hi => hsec i hi v)

/-- The infinite-family version: with summable sector stresses and aggregation
read as an unconditional sum, the same conclusion holds. -/
theorem endpoint_aggregation_suffices_tsum [CompleteSpace H] {ι : Type*}
    (K : Submodule ℝ H) (hdense : Dense (K : Set H))
    (deltaCommon : H → ℝ) (G : H)
    (hGR : ∀ h ∈ K, deltaCommon h = pair G h)
    (deltaSec : ι → H → ℝ) (Tc : ι → H) (hsummable : Summable Tc)
    (hsec : ∀ i h, deltaSec i h = pair (Tc i) h)
    (hagg : ∀ h ∈ K, deltaCommon h = ∑' i, deltaSec i h) :
    G = ∑' i, Tc i := by
  refine eq_of_pair_eq_on_dense_submodule G (∑' i, Tc i) K hdense (fun v hv => ?_)
  rw [← hGR v hv, hagg v hv, pair_tsum _ _ hsummable]
  exact tsum_congr (fun i => hsec i v)

/-- The one-entry ledger of the producer boundary record, read as a claim about
the Lean model: *endpoint receipts plus exact aggregation leave the common
stress undetermined, so a separate convergence relation is still needed*. -/
def needsIndependentConvergenceRelation : Prop :=
  ∃ (s : Finset ℕ) (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (deltaCommon : EuclideanSpace ℝ (Fin 2) → ℝ) (G : EuclideanSpace ℝ (Fin 2))
    (deltaSec : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (Tc : ℕ → EuclideanSpace ℝ (Fin 2)),
    Dense (K : Set (EuclideanSpace ℝ (Fin 2))) ∧
      (∀ h ∈ K, deltaCommon h = pair G h) ∧
      (∀ i ∈ s, ∀ h, deltaSec i h = pair (Tc i) h) ∧
      (∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSec i h) ∧
      G ≠ ∑ i ∈ s, Tc i

/-- **The `false`-pinned entry is refuted.**  No independent convergence
relation is needed downstream of endpoint sector data. -/
theorem ledger_false_entry_is_refuted : ¬ needsIndependentConvergenceRelation := by
  rintro ⟨s, K, deltaCommon, G, deltaSec, Tc, hdense, hGR, hsec, hagg, hne⟩
  exact hne (endpoint_aggregation_suffices s K hdense deltaCommon G hGR deltaSec Tc hsec hagg)

/-- **"Exact aggregation" has to name a total.**  A sector family can have
partial sums converging along an exhaustion to a nonzero vector while its
unconditional sum is zero, so the summability hypothesis of
`endpoint_aggregation_suffices_tsum` is load-bearing. -/
theorem exact_aggregation_needs_the_right_total (e : H) (he : e ≠ 0) :
    ∃ T : ℕ → H, ¬ Summable T ∧
      Tendsto (fun N => ∑ i ∈ Finset.range N, T i) atTop (nhds e) ∧
      ∑' i, T i = 0 ∧ (0 : H) ≠ e :=
  SectorFilter.exhaustion_total_is_not_the_unconditional_total e he

/-- **The producer ledger, settled.**  The `true` entry is a theorem, the
`false` entry is refuted, and the infinite-family form comes with the exact
hypothesis (summability) that its finite form does not need. -/
theorem producer_ledger_has_theorem_content [CompleteSpace H] :
    ¬ needsIndependentConvergenceRelation ∧
      (∀ {ι : Type} (s : Finset ι) (K : Submodule ℝ H) (_ : Dense (K : Set H))
        (deltaCommon : H → ℝ) (G : H), (∀ h ∈ K, deltaCommon h = pair G h) →
        ∀ (deltaSec : ι → H → ℝ) (Tc : ι → H),
          (∀ i ∈ s, ∀ h, deltaSec i h = pair (Tc i) h) →
          (∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSec i h) →
          G = ∑ i ∈ s, Tc i) :=
  ⟨ledger_false_entry_is_refuted,
    fun s K hdense deltaCommon G hGR deltaSec Tc hsec hagg =>
      endpoint_aggregation_suffices s K hdense deltaCommon G hGR deltaSec Tc hsec hagg⟩

end Integration.Reconciliation.ContinuumProducerBoundary
