import Mathlib
import Integration.Variation.Pairing

/-!
# QFT/GR frontier, lane 2 — finite cutoff to continuum, and sector aggregation

The handoff records the open follow-up precisely:

```
finite-cutoff stress representation  ⇏  literal continuum stress tensor
```

and states the chain that is actually wanted:

```
δ_g S_k[h] = ⟨T_k, h⟩            for every cutoff k
δ_g S_k[h] → δ_g S_∞[h]
⟨T_k, h⟩   → ⟨T_continuum, h⟩
uniqueness of the scalar limit
------------------------------------------------
δ_g S_∞[h] = ⟨T_continuum, h⟩
```

This file proves that chain, and — more than the chain asks — proves that the
continuum stress tensor does not have to be assumed: if the cutoff pairings
converge pointwise on a complete perturbation space, a *unique* continuum
tensor representing the limit exists.  That is Banach–Steinhaus (the limit
functional is continuous) followed by Riesz representation.

## What is proved

* `scalar_limit_interchange` — the literal interchange step: two sequences that
  agree term by term have the same limit, so `δ_g S_∞[h] = ⟨T_c, h⟩` follows
  from the two convergences;
* `exists_unique_continuum_stress` — **the missing continuum-stress theorem**:
  pointwise convergence of the cutoff pairings yields a unique `T_c : H` with
  `lim_k ⟨T_k, h⟩ = ⟨T_c, h⟩` for every `h`;
* `continuum_stress_of_cutoff_family` — the packaged form: finite-cutoff
  representation plus pointwise convergence of the finite variations gives a
  unique continuum stress representing the continuum variation;
* `sector_aggregate_variation` — sector aggregation: a finite family of
  sectorwise representations sums to a representation by the summed tensor;
* `sector_aggregation_commutes_with_cutoff_limit` — aggregation over finitely
  many sectors commutes with the cutoff limit;
* `exists_unique_continuum_functional` — the Banach-space form: without any
  inner product the limit is still a unique continuous linear functional, so
  only the tensor *representation* needs the Hilbert structure;
* `sector_aggregate_variation_tsum` — aggregation over an infinite summable
  family of sectors.

Three negatives keep the hypotheses load-bearing:

* `pairing_convergence_is_not_tensor_convergence` (and its concrete `ℓ²`
  witness) — every pairing may converge while the tensors do not converge at
  all: convergence of `⟨T_k, h⟩` is *weak*, and no norm statement follows;
* `divergent_cutoff_family_has_no_continuum_pairing` — without the convergence
  hypothesis there is no continuum pairing to represent;
* `one_sector_is_not_the_total` — a single sector's stress is not the total
  stress; the aggregation step is not cosmetic.
-/

namespace Integration.Variation.CutoffLimit

open scoped InnerProductSpace RealInnerProductSpace
open Filter Integration.Variation.Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The interchange step -/

/-- **Uniqueness of the scalar limit.**  If the finite-cutoff variation equals
the finite-cutoff stress pairing at every cutoff, and both converge, the
continuum variation equals the continuum pairing. -/
theorem scalar_limit_interchange (delta pairing : ℕ → ℝ) (dInf tInf : ℝ)
    (hrep : ∀ k, delta k = pairing k)
    (hd : Tendsto delta atTop (nhds dInf))
    (ht : Tendsto pairing atTop (nhds tInf)) : dInf = tInf := by
  have : delta = pairing := funext hrep
  exact tendsto_nhds_unique hd (this ▸ ht)

/-! ### Existence and uniqueness of the continuum stress -/

/-- **The continuum stress tensor exists and is unique.**  If the finite-cutoff
stress pairings converge pointwise to a scalar `dInf h` for every admitted
perturbation `h`, then there is exactly one tensor `T_c` with
`dInf h = ⟨T_c, h⟩`.

The proof is Banach–Steinhaus (the pointwise limit of continuous linear
functionals on a complete space is again continuous) followed by the Riesz
representation theorem. -/
theorem exists_unique_continuum_stress [CompleteSpace H] (T : ℕ → H) (dInf : H → ℝ)
    (hconv : ∀ h, Tendsto (fun k => pair (T k) h) atTop (nhds (dInf h))) :
    ∃! Tc : H, ∀ h, dInf h = pair Tc h := by
  have hg : Tendsto (fun k x => (innerSL ℝ (T k)) x) atTop (nhds dInf) :=
    tendsto_pi_nhds.mpr hconv
  set L : H →L[ℝ] ℝ := continuousLinearMapOfTendsto _ hg with hL
  have hLapp : ∀ x, L x = dInf x := fun _ => rfl
  refine ⟨(InnerProductSpace.toDual ℝ H).symm L, fun h => ?_, ?_⟩
  · simp only [pair_apply]
    rw [InnerProductSpace.toDual_symm_apply, hLapp]
  · intro y hy
    refine ext_inner_right ℝ (fun v => ?_)
    rw [InnerProductSpace.toDual_symm_apply, hLapp]
    exact ((hy v).trans (pair_apply y v)).symm

/-- The packaged finite→continuum theorem.  `deltaK k h` is the first variation
of the action at cutoff `k`, represented at that cutoff by the finite stress
`T k`; `deltaInf` is the continuum variation, obtained as the pointwise limit.
Then a unique continuum stress represents `deltaInf`, and every cutoff identity
passes to the limit. -/
theorem continuum_stress_of_cutoff_family [CompleteSpace H]
    (deltaK : ℕ → H → ℝ) (T : ℕ → H) (deltaInf : H → ℝ)
    (hrep : ∀ k h, deltaK k h = pair (T k) h)
    (hconv : ∀ h, Tendsto (fun k => deltaK k h) atTop (nhds (deltaInf h))) :
    ∃! Tc : H, ∀ h, deltaInf h = pair Tc h := by
  refine exists_unique_continuum_stress T deltaInf (fun h => ?_)
  have : (fun k => pair (T k) h) = fun k => deltaK k h := funext fun k => (hrep k h).symm
  rw [this]
  exact hconv h

/-- The same existence statement without an inner product: on any Banach space
of perturbations, a pointwise limit of continuous cutoff variations is again a
continuous linear functional, uniquely.  Only the *representation* of that
functional by a tensor needs a Hilbert structure. -/
theorem exists_unique_continuum_functional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (deltaK : ℕ → E →L[ℝ] ℝ) (deltaInf : E → ℝ)
    (hconv : ∀ h, Tendsto (fun k => deltaK k h) atTop (nhds (deltaInf h))) :
    ∃! L : E →L[ℝ] ℝ, ∀ h, deltaInf h = L h := by
  have hg : Tendsto (fun k x => (deltaK k) x) atTop (nhds deltaInf) := tendsto_pi_nhds.mpr hconv
  refine ⟨continuousLinearMapOfTendsto _ hg, fun _ => rfl, ?_⟩
  intro L hL
  ext x
  exact (hL x).symm

/-! ### Sector aggregation -/

/-- **Sector aggregation.**  If each sector's variation is represented by that
sector's stress tensor, the total variation is represented by the summed
tensor. -/
theorem sector_aggregate_variation {ι : Type*} (s : Finset ι)
    (deltaSec : ι → H → ℝ) (T : ι → H)
    (hrep : ∀ i ∈ s, ∀ h, deltaSec i h = pair (T i) h) (h : H) :
    ∑ i ∈ s, deltaSec i h = pair (∑ i ∈ s, T i) h := by
  rw [pair_sum]
  exact Finset.sum_congr rfl fun i hi => hrep i hi h

/-- Aggregation over finitely many sectors commutes with the cutoff limit. -/
theorem sector_aggregation_commutes_with_cutoff_limit {ι : Type*} (s : Finset ι)
    (T : ι → ℕ → H) (Tc : ι → H) (h : H)
    (hconv : ∀ i ∈ s, Tendsto (fun k => pair (T i k) h) atTop (nhds (pair (Tc i) h))) :
    Tendsto (fun k => pair (∑ i ∈ s, T i k) h) atTop (nhds (pair (∑ i ∈ s, Tc i) h)) := by
  have hsum : Tendsto (fun k => ∑ i ∈ s, pair (T i k) h) atTop
      (nhds (∑ i ∈ s, pair (Tc i) h)) := tendsto_finset_sum s hconv
  simpa only [pair_sum] using hsum

/-- Sector aggregation over an infinite, summable family of sectors. -/
theorem sector_aggregate_variation_tsum {ι : Type*}
    (deltaSec : ι → H → ℝ) (T : ι → H) (hs : Summable T)
    (hrep : ∀ i h, deltaSec i h = pair (T i) h) (h : H) :
    ∑' i, deltaSec i h = pair (∑' i, T i) h := by
  rw [pair_tsum T h hs]
  exact tsum_congr fun i => hrep i h

/-! ### Negatives: the hypotheses are load-bearing -/

/-- Pairing convergence is strictly weaker than tensor convergence.  For any
orthonormal sequence the pairings all converge to zero, yet the tensors stay at
norm one and converge to nothing. -/
theorem pairing_convergence_is_not_tensor_convergence (e : ℕ → H)
    (he : Orthonormal ℝ e) :
    (∀ h, Tendsto (fun k => pair (e k) h) atTop (nhds 0)) ∧ ¬ Tendsto e atTop (nhds 0) := by
  constructor
  · intro h
    have hs := he.inner_products_summable (𝕜 := ℝ) h
    have h2 : Tendsto (fun k => ‖⟪e k, h⟫_ℝ‖) atTop (nhds 0) := by
      simpa [Real.sqrt_sq_eq_abs] using hs.tendsto_atTop_zero.sqrt
    simpa [pair, tendsto_zero_iff_norm_tendsto_zero] using h2
  · intro hcon
    have hnorm : Tendsto (fun k => ‖e k‖) atTop (nhds 0) := by
      have hn := hcon.norm
      simp only [norm_zero] at hn
      exact hn
    have hone : (fun k : ℕ => ‖e k‖) = fun _ : ℕ => (1 : ℝ) := funext fun k => he.1 k
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := hone ▸ hnorm
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    norm_num at this

/-- A concrete witness of the previous negative in `ℓ²(ℕ, ℝ)`. -/
theorem l2_pairing_convergence_is_not_tensor_convergence :
    ∃ e : ℕ → lp (fun _ : ℕ => ℝ) 2,
      (∀ h, Tendsto (fun k => pair (e k) h) atTop (nhds 0)) ∧ ¬ Tendsto e atTop (nhds 0) := by
  refine ⟨fun k => lp.single 2 k (1 : ℝ), ?_⟩
  refine pairing_convergence_is_not_tensor_convergence _ ?_
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  by_cases h : i = j <;> simp [h, lp.single_apply]

/-- Without a convergence hypothesis there is no continuum pairing at all: the
cutoff family `T k = k • v` has divergent pairings against `v`. -/
theorem divergent_cutoff_family_has_no_continuum_pairing (v : H) (hv : v ≠ 0) :
    ∀ c : ℝ, ¬ Tendsto (fun k : ℕ => pair ((k : ℝ) • v) v) atTop (nhds c) := by
  intro c hc
  have hpos : 0 < ‖v‖ ^ 2 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  have hform : (fun k : ℕ => pair ((k : ℝ) • v) v) = fun k : ℕ => (k : ℝ) * ‖v‖ ^ 2 := by
    funext k
    simp [pair, real_inner_smul_left]
  have hdiv : Tendsto (fun k : ℕ => (k : ℝ) * ‖v‖ ^ 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hpos
  rw [hform] at hc
  exact not_tendsto_nhds_of_tendsto_atTop hdiv c hc

/-- A single sector's stress is not the total stress: aggregation is not a
relabelling. -/
theorem one_sector_is_not_the_total :
    ∃ (T : Fin 2 → EuclideanSpace ℝ (Fin 1)) (h : EuclideanSpace ℝ (Fin 1)),
      pair (T 0) h ≠ pair (∑ i, T i) h := by
  refine ⟨fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_⟩
  simp [pair, two_smul, inner_add_left]

end Integration.Variation.CutoffLimit
