import Synthesis.RiemannNormalizedProjectiveHorizontalQuadraticVariation
import Synthesis.RiemannNormalizedProjectiveHorizontalTsumReduction

/-!
# Quadratically refined finite horizontal middle carrier

The first horizontal tsum reduction used the linear first-moment sign margin.
The exact cosine symmetry gives a second, quadratic q-variation criterion.

This file removes every source certified by either criterion from the finite
middle carrier.  Removed terms are nonpositive, so the one-sided aggregate
upper bound can only improve.

The resulting finite carrier is the current honest local obstruction for the
horizontal channel.
-/

noncomputable section

open Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.ProjectedZeroTailSummability

def normalizedProjectiveHorizontalSourceQuadraticNear
    (t : ℝ) (sigma : Zeros) : Prop :=
  heightOf sigma ≠ 0
    ∧
  (normalizedGap t sigma)^2 / 2
      * normalizedProjectiveHorizontalSecondMoment t
          (normalizedHorizontalHeight t sigma)
    <
  - normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t sigma) 0

def normalizedProjectiveHorizontalSourceFavourable
    (t : ℝ) (sigma : Zeros) : Prop :=
  normalizedProjectiveHorizontalSourceNear t sigma
    ∨ normalizedProjectiveHorizontalSourceQuadraticNear t sigma

theorem normalizedProjectiveHorizontalSourceTerm_nonpos_of_favourable
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hfav : normalizedProjectiveHorizontalSourceFavourable t sigma) :
    normalizedProjectiveHorizontalSourceTerm t sigma ≤ 0 := by
  rcases hfav with hlin | hquad
  · exact normalizedProjectiveHorizontalSourceTerm_nonpos_of_near ht hlin
  · rcases hquad with ⟨hoff, hmargin⟩
    have hQ :=
      normalizedProjectiveHorizontalQuadratic_actualSource_neg_of_quadratic_near
        ht hoff hmargin
    have hm :
        0 < ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by
      have hmNat :
          (1 : ℕ) ≤ (zetaZeroConfig).mult (sigma : ℂ) :=
        (zetaZeroConfig).one_le_mult (sigma : ℂ) sigma.2
      exact_mod_cast hmNat
    have htpos : 0 < t := by linarith
    have ha2 : 0 < (heightOf sigma)^2 / t^2 := by
      exact div_pos (sq_pos_of_ne_zero hoff) (sq_pos_of_pos htpos)
    unfold normalizedProjectiveHorizontalSourceTerm
    exact (mul_neg_of_pos_of_neg (mul_pos hm ha2) hQ).le

/-- Refine the previous finite middle carrier by deleting every source covered by
the quadratic sign theorem. -/
def normalizedProjectiveHorizontalRefinedMiddleFinset
    (t : ℝ) :
    Finset ((SameOrd t)ᶜ : Set Zeros) :=
  (normalizedProjectiveHorizontalMiddleFinset t).filter fun sigma =>
    ¬ normalizedProjectiveHorizontalSourceFavourable t (sigma : Zeros)

theorem mem_normalizedProjectiveHorizontalRefinedMiddleFinset_iff
    (t : ℝ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinset t
      ↔
    sigma ∈ normalizedProjectiveHorizontalMiddleFinset t
      ∧
    ¬ normalizedProjectiveHorizontalSourceFavourable t (sigma : Zeros) := by
  classical
  simp [normalizedProjectiveHorizontalRefinedMiddleFinset]

theorem normalizedProjectiveHorizontalRefinedMiddle_subset_middle
    (t : ℝ) :
    normalizedProjectiveHorizontalRefinedMiddleFinset t
      ⊆ normalizedProjectiveHorizontalMiddleFinset t := by
  intro sigma hsigma
  exact
    (mem_normalizedProjectiveHorizontalRefinedMiddleFinset_iff t sigma).1
      hsigma |>.1

/-- Deleting quadratically favourable terms can only increase the finite
one-sided upper budget, because every deleted source term is nonpositive. -/
theorem sum_middle_le_sum_refinedMiddle
    {t : ℝ} (ht : 18 ≤ t) :
    (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      ≤
    ∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) := by
  classical
  let F := normalizedProjectiveHorizontalMiddleFinset t
  let G := normalizedProjectiveHorizontalRefinedMiddleFinset t
  have hpoint :
      ∀ sigma ∈ F,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
          ≤
        if sigma ∈ G
        then normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
        else 0 := by
    intro sigma hsigma
    by_cases hG : sigma ∈ G
    · simp [hG]
    · simp [hG]
      have hnotFav :
          ¬ ¬ normalizedProjectiveHorizontalSourceFavourable
              t (sigma : Zeros) := by
        intro hnot
        apply hG
        exact
          (mem_normalizedProjectiveHorizontalRefinedMiddleFinset_iff
            t sigma).2 ⟨hsigma, hnot⟩
      have hfav :
          normalizedProjectiveHorizontalSourceFavourable
            t (sigma : Zeros) := Classical.not_not.mp hnotFav
      exact normalizedProjectiveHorizontalSourceTerm_nonpos_of_favourable
        ht hfav
  have hsum :
      (∑ sigma ∈ F,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤
      ∑ sigma ∈ F,
        (if sigma ∈ G
         then normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
         else 0) := by
    exact Finset.sum_le_sum hpoint
  have hFG : G ⊆ F := by
    dsimp [F, G]
    exact normalizedProjectiveHorizontalRefinedMiddle_subset_middle t
  have hrw :
      (∑ sigma ∈ F,
        (if sigma ∈ G
         then normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
         else 0))
        =
      ∑ sigma ∈ G,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) := by
    exact Finset.sum_ite_irrel
      (s := F) (p := fun sigma => sigma ∈ G)
      (f := fun sigma =>
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      |>.trans (by
        rw [Finset.filter_mem_eq_inter]
        have hfilter : F.filter (fun sigma => sigma ∈ G) = G := by
          ext sigma
          simp [hFG]
        rw [hfilter])
  exact hsum.trans_eq hrw

/--
Refined literal infinite horizontal aggregate reduction.

The same theorem-bearing far coefficient works, but the finite local remainder
contains only sources which evade BOTH the linear and quadratic signed-near
criteria.
-/
theorem exists_offOrdProjectiveHorizontal_le_refinedMiddle_add_farTail
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤
      (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinset t,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        +
      K * ∑' rho : Zeros, tailTerm t rho := by
  obtain ⟨K, hK0, hbase⟩ :=
    exists_offOrdProjectiveHorizontal_le_middle_add_farTail ht
  refine ⟨K, hK0, ?_⟩
  calc
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      ≤
    (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      +
    K * ∑' rho : Zeros, tailTerm t rho := hbase
    _ ≤
    (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      +
    K * ∑' rho : Zeros, tailTerm t rho := by
        exact add_le_add_right
          (sum_middle_le_sum_refinedMiddle ht) _

end Synthesis
