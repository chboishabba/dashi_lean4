import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated convergence for infinite products at the pinned Mathlib version

Mathlib v4.28.0 already contains the two ingredients used by the later 2026
helper:
* summable finite-subset products;
* Tannery dominated convergence for tsums.

This module ports only the missing product-level wrapper needed by the local
eta^24 cusp proof.  No dependency bump is used.
-/

namespace Integration.MoonshinePinnedInfiniteProductDominated

open Filter
open scoped Topology

variable {α R β : Type*}
  [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
  {g : β → R} {bound : β → ℝ}

theorem tendsto_tprod_one_add_of_dominated_convergence
    {𝓕 : Filter α} {f : α → β → R}
    (h_sum : Summable bound)
    (hab : ∀ k, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∏' k, (1 + f n k))
      𝓕 (𝓝 (∏' k, (1 + g k))) := by
  rcases eq_or_neBot 𝓕 with rfl | _
  · simp
  have h_bound_g (k) : ‖g k‖ ≤ bound k :=
    le_of_tendsto ((hab k).norm)
      (h_bound.mono fun n hn ↦ hn k)
  have hsum_g : Summable (‖g ·‖) :=
    h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  rw [show ∏' k, (1 + g k) =
      ∑' s, ∏ i ∈ s, g i from
    tprod_one_add
      (summable_finsetProd_of_summable_norm hsum_g)]
  have ht :
      Tendsto (∑' k, ∏ c ∈ k, f · c) 𝓕
        (𝓝 (∑' k, ∏ c ∈ k, g c)) :=
    tendsto_tsum_of_dominated_convergence
      (summable_finsetProd_of_summable_nonneg
        (fun i ↦ (norm_nonneg (g i)).trans (h_bound_g i))
        h_sum)
      (tendsto_finsetProd · fun i _ ↦ hab i)
      (h_bound.mono fun n hn s ↦
        (Finset.norm_prod_le s (f n)).trans
          (Finset.prod_le_prod₀ (by grind) (by grind)))
  apply ht.congr' (h_bound.mono fun n hn ↦ ?_)
  rw [tprod_one_add]
  exact summable_finsetProd_of_summable_norm <|
    h_sum.of_nonneg_of_le (by grind) hn

structure Boundary where
  tanneryReusedAtPin : Bool
  summableProductExpansionReusedAtPin : Bool
  dominatedInfiniteProductLimitOwned : Bool
  dependencyBumpUsed : Bool

def boundary : Boundary where
  tanneryReusedAtPin := true
  summableProductExpansionReusedAtPin := true
  dominatedInfiniteProductLimitOwned := true
  dependencyBumpUsed := false

end Integration.MoonshinePinnedInfiniteProductDominated
