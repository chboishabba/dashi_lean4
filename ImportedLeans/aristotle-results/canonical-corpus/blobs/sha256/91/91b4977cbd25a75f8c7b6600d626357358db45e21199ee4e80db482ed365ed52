import Mathlib
import Integration.Variation.Pairing

/-!
# QFT/GR frontier, lane 3 — one common metric-variation language

The correction recorded in the handoff is that it is **not enough** for GR and
QFT each to have something separately named "metric variation": both must be
induced from a *single common perturbation carrier*

```
        H_common
        /      \
   H_GR          H_QFT
```

with commuting stress-pairing diagrams and one common admitted perturbation
fibre.  This file makes that structure a Lean definition and proves exactly what
it buys — and, in three negatives, exactly what it does not.

## The structure

`CommonMetricVariationLanguage` carries the admitted fibre `admitted ≤ H_common`
and the two induced maps `toGR`, `toQFT`.  `CommonVariation` carries the first
variation `δ_g S_common : H_common →ₗ[ℝ] ℝ` of the *one* common action together
with the two sector receipts

```
δ_g S_common[h] = ⟨G, toGR h⟩            (Einstein side)
δ_g S_common[h] = ⟨T_QFT,total, toQFT h⟩  (QFT side)
```

for every admitted `h`.

## What is proved

* `pairings_agree` — the two stress pairings agree on the common fibre; this is
  the only thing the two receipts give *by themselves*;
* `stress_weld_of_common_carrier` — **the stress weld**: if the two sides are
  read into the *same* space by the *same* map and the image of the admitted
  fibre spans, then `G = T_QFT,total` as tensors;
* `stress_weld_of_dense_carrier` — the same conclusion from the weaker, and
  physically attainable, hypothesis that the admitted image is only dense;
* `stress_weld` — the same statement packaged for a language whose two maps
  coincide;
* `tensor_unique_of_spanning` — the represented tensor is unique, so "the"
  Einstein tensor of a common action is well defined once the fibre spans.

Negatives:

* `mismatched_carrier_maps_do_not_weld` — two *different* induced maps out of a
  common carrier, both with spanning admitted fibre and both with a valid
  receipt, and yet `G ≠ T`: naming both maps "the metric variation" is not
  enough;
* `non_spanning_fibre_does_not_weld` — one common map, valid receipts on both
  sides, and still `G ≠ T`, because the admitted fibre does not span;
* `separate_actions_do_not_weld` — two separately named actions with no common
  carrier constrain nothing at all.
-/

namespace Integration.Variation.CommonLanguage

open scoped InnerProductSpace RealInnerProductSpace
open Integration.Variation.Pairing

variable {Hc HGR HQFT : Type*}
  [NormedAddCommGroup Hc] [InnerProductSpace ℝ Hc]
  [NormedAddCommGroup HGR] [InnerProductSpace ℝ HGR]
  [NormedAddCommGroup HQFT] [InnerProductSpace ℝ HQFT]

/-- One common metric-perturbation language: a common carrier `Hc` with a single
admitted perturbation fibre, and the two maps sending a common perturbation to
the perturbation each sector actually pairs against. -/
structure CommonMetricVariationLanguage (Hc HGR HQFT : Type*)
    [NormedAddCommGroup Hc] [InnerProductSpace ℝ Hc]
    [NormedAddCommGroup HGR] [InnerProductSpace ℝ HGR]
    [NormedAddCommGroup HQFT] [InnerProductSpace ℝ HQFT] where
  /-- The one common admitted perturbation fibre. -/
  admitted : Submodule ℝ Hc
  /-- The perturbation the GR sector pairs against. -/
  toGR : Hc →ₗ[ℝ] HGR
  /-- The perturbation the QFT sector pairs against. -/
  toQFT : Hc →ₗ[ℝ] HQFT

/-- The first variation of *one* common action, with both sector receipts. -/
structure CommonVariation (L : CommonMetricVariationLanguage Hc HGR HQFT) where
  /-- `δ_g S_common`, a functional on the common carrier. -/
  deltaCommon : Hc →ₗ[ℝ] ℝ
  /-- The GR-side tensor (the Einstein tensor of the common action). -/
  einstein : HGR
  /-- The QFT-side total stress tensor, after sector aggregation. -/
  qftTotal : HQFT
  /-- Einstein-side receipt: `δ_g S_common[h] = ⟨G, h⟩`. -/
  grVariation : ∀ h ∈ L.admitted, deltaCommon h = pair einstein (L.toGR h)
  /-- QFT-side receipt: `δ_g S_common[h] = ⟨T_total, h⟩`. -/
  qftVariation : ∀ h ∈ L.admitted, deltaCommon h = pair qftTotal (L.toQFT h)

namespace CommonVariation

variable {L : CommonMetricVariationLanguage Hc HGR HQFT}

/-- What the two receipts give on their own: the two stress pairings agree on
the common admitted fibre. -/
theorem pairings_agree (V : CommonVariation L) (h : Hc) (hh : h ∈ L.admitted) :
    pair V.einstein (L.toGR h) = pair V.qftTotal (L.toQFT h) := by
  rw [← V.grVariation h hh, ← V.qftVariation h hh]

end CommonVariation

/-! ### The stress weld -/

/-- **The stress weld.**  If both sectors pair in the same space along the same
induced map, and the image of the admitted fibre spans that space, then the
Einstein tensor of the common action *is* the total QFT stress tensor. -/
theorem stress_weld_of_common_carrier {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (iota : Hc →ₗ[ℝ] H) (K : Submodule ℝ Hc) (d : Hc →ₗ[ℝ] ℝ) (G T : H)
    (hG : ∀ h ∈ K, d h = pair G (iota h))
    (hT : ∀ h ∈ K, d h = pair T (iota h))
    (hspan : Submodule.span ℝ (iota '' K) = ⊤) : G = T := by
  refine eq_of_pair_eq_on_spanning G T (iota '' K) hspan ?_
  rintro v ⟨h, hh, rfl⟩
  rw [← hG h hh, ← hT h hh]

/-- The stress weld under the weaker, and physically attainable, hypothesis
that the admitted image is only *dense*. -/
theorem stress_weld_of_dense_carrier {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (iota : Hc →ₗ[ℝ] H) (K : Submodule ℝ Hc) (d : Hc →ₗ[ℝ] ℝ) (G T : H)
    (hG : ∀ h ∈ K, d h = pair G (iota h))
    (hT : ∀ h ∈ K, d h = pair T (iota h))
    (hdense : Dense (Submodule.span ℝ (iota '' K) : Set H)) : G = T := by
  refine eq_of_pair_eq_on_dense G T (iota '' K) hdense ?_
  rintro v ⟨h, hh, rfl⟩
  rw [← hG h hh, ← hT h hh]

/-- The weld for a language whose two induced maps coincide. -/
theorem stress_weld {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : CommonMetricVariationLanguage Hc H H) (V : CommonVariation L)
    (hsame : L.toGR = L.toQFT)
    (hspan : Submodule.span ℝ (L.toGR '' L.admitted) = ⊤) :
    V.einstein = V.qftTotal := by
  refine stress_weld_of_common_carrier L.toGR L.admitted V.deltaCommon _ _
    V.grVariation (fun h hh => ?_) hspan
  rw [V.qftVariation h hh, hsame]

/-- Once the admitted fibre spans, the tensor representing a variation is
unique: "the" Einstein tensor of the common action is well defined. -/
theorem tensor_unique_of_spanning {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (iota : Hc →ₗ[ℝ] H) (K : Submodule ℝ Hc) (d : Hc →ₗ[ℝ] ℝ) (G G' : H)
    (hG : ∀ h ∈ K, d h = pair G (iota h))
    (hG' : ∀ h ∈ K, d h = pair G' (iota h))
    (hspan : Submodule.span ℝ (iota '' K) = ⊤) : G = G' :=
  stress_weld_of_common_carrier iota K d G G' hG hG' hspan

/-! ### Negatives -/

/-- **Two differently named "metric variations" do not weld.**  Here there *is*
a common carrier and the admitted fibre is everything, but the GR side reads a
perturbation as `h` while the QFT side reads it as `2h`.  Both receipts hold and
the tensors differ. -/
theorem mismatched_carrier_maps_do_not_weld :
    ∃ (iotaGR iotaQFT : ℝ →ₗ[ℝ] ℝ) (K : Submodule ℝ ℝ) (d : ℝ →ₗ[ℝ] ℝ) (G T : ℝ),
      K = ⊤ ∧
      (∀ h ∈ K, d h = pair G (iotaGR h)) ∧
      (∀ h ∈ K, d h = pair T (iotaQFT h)) ∧
      Submodule.span ℝ (iotaGR '' K) = ⊤ ∧
      G ≠ T := by
  refine ⟨LinearMap.id, (2 : ℝ) • LinearMap.id, ⊤, (2 : ℝ) • LinearMap.id, 2, 1,
    rfl, ?_, ?_, ?_, by norm_num⟩
  · intro h _
    simp [pair, RCLike.inner_apply]
    ring
  · intro h _
    simp [pair, RCLike.inner_apply]
  · simp

/-- **A non-spanning admitted fibre does not weld.**  One common map, both
receipts valid, and yet the tensors differ, because the admitted perturbations
only probe one axis. -/
theorem non_spanning_fibre_does_not_weld :
    ∃ (iota : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) (K : Submodule ℝ ℝ)
      (d : ℝ →ₗ[ℝ] ℝ) (G T : EuclideanSpace ℝ (Fin 2)),
      K = ⊤ ∧
      (∀ h ∈ K, d h = pair G (iota h)) ∧
      (∀ h ∈ K, d h = pair T (iota h)) ∧
      Submodule.span ℝ (iota '' K) ≠ ⊤ ∧
      G ≠ T := by
  classical
  refine ⟨(LinearMap.toSpanSingleton ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))), ⊤, 0,
    EuclideanSpace.single (1 : Fin 2) (1 : ℝ), 0, rfl, ?_, ?_, ?_, ?_⟩
  · intro h _
    simp [pair, LinearMap.toSpanSingleton_apply,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  · intro h _
    simp [pair]
  · intro hspan
    have hmem : EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ∈
        Submodule.span ℝ ((LinearMap.toSpanSingleton ℝ (EuclideanSpace ℝ (Fin 2))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) '' (⊤ : Submodule ℝ ℝ)) := by
      rw [hspan]; trivial
    have hsub : Submodule.span ℝ ((LinearMap.toSpanSingleton ℝ (EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) '' (⊤ : Submodule ℝ ℝ))
        ≤ Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} := by
      refine Submodule.span_le.mpr ?_
      rintro v ⟨h, -, rfl⟩
      exact Submodule.smul_mem _ h (Submodule.mem_span_singleton_self _)
    have := hsub hmem
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hc
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hc
    simp [EuclideanSpace.single_apply] at h0 h1
  · intro hc
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hc
    simp [EuclideanSpace.single_apply] at this

/-- **Separately named actions constrain nothing.**  Two sector variations with
*no* common carrier — each represented on its own space by its own tensor — put
no relation whatsoever between the two tensors, whatever the two spaces are
called. -/
theorem separate_actions_do_not_weld :
    ∃ (dGR dQFT : ℝ →ₗ[ℝ] ℝ) (G T : ℝ),
      (∀ h : ℝ, dGR h = pair G h) ∧
      (∀ h : ℝ, dQFT h = pair T h) ∧
      G ≠ T := by
  refine ⟨LinearMap.id, (2 : ℝ) • LinearMap.id, 1, 2, ?_, ?_, by norm_num⟩
  · intro h; simp [pair, RCLike.inner_apply]
  · intro h; simp [pair, RCLike.inner_apply, mul_comm]

end Integration.Variation.CommonLanguage
