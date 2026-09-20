import Synthesis.RiemannNormalizedProjectiveHorizontalFarSummability
import Zeta23Bridge.OffOrdinateCutoffCarrier

/-!
# Literal horizontal tsum = finite unsigned middle + signed-near + summable far

The horizontal source family now has three exact regions.

1. Local signed-near sources: their contribution is nonpositive.
2. Local sources failing the sign margin: these form a finite literal set because
   they lie in |Im rho - t| < 1.
3. Far sources: their absolute sum is controlled by the theorem-bearing
   quadratic zero tail.

This file proves the infinite aggregate reduction on the actual off-ordinate
carrier.  It is not a finite approximation: the left side is the literal tsum
of the complete horizontal source family.

The only horizontal terms that survive as individually difficult objects are
the finite local "middle" carrier.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.NearFarCarrierSplit
open Zeta23Bridge.OffOrdinateCutoffCarrier
open Zeta23Bridge.ProjectedZeroTailSummability

def normalizedProjectiveHorizontalLocalTerm
    (t : ℝ) (rho : Zeros) : ℝ :=
  if |(rho : ℂ).im - t| < 1
  then normalizedProjectiveHorizontalSourceTerm t rho
  else 0

theorem normalizedProjectiveHorizontalLocalTerm_summable
    (t : ℝ) :
    Summable (normalizedProjectiveHorizontalLocalTerm t) := by
  classical
  apply summable_of_ne_finset_zero (s := nearFinset t 1)
  intro rho hrho
  by_cases hlt : |(rho : ℂ).im - t| < 1
  · exfalso
    apply hrho
    exact (mem_nearFinset_iff t 1 rho).2 (by simpa using hlt)
  · simp [normalizedProjectiveHorizontalLocalTerm, hlt]

theorem normalizedProjectiveHorizontalSourceTerm_eq_local_add_far
    (t : ℝ) (rho : Zeros) :
    normalizedProjectiveHorizontalSourceTerm t rho
      =
    normalizedProjectiveHorizontalLocalTerm t rho
      + normalizedProjectiveHorizontalFarTerm t rho := by
  unfold normalizedProjectiveHorizontalLocalTerm
    normalizedProjectiveHorizontalFarTerm
  by_cases hlocal : |(rho : ℂ).im - t| < 1
  · have hfar : ¬ 1 ≤ |(rho : ℂ).im - t| := not_le.mpr hlocal
    simp [hlocal, hfar]
  · have hfar : 1 ≤ |(rho : ℂ).im - t| := le_of_not_gt hlocal
    simp [hlocal, hfar]

/-- The complete horizontal source family is summable on the full literal zero
carrier. -/
theorem normalizedProjectiveHorizontalSourceTerm_summable_full
    {t : ℝ} (ht : 18 ≤ t) :
    Summable (normalizedProjectiveHorizontalSourceTerm t) := by
  have hlocal :=
    normalizedProjectiveHorizontalLocalTerm_summable t
  obtain ⟨K, hK0, habsFar, hdom, htotal⟩ :=
    exists_canonicalProjectiveHorizontalFarSummableBound ht
  have hfar :
      Summable (normalizedProjectiveHorizontalFarTerm t) :=
    Summable.of_abs habsFar
  have hadd :=
    hlocal.add hfar
  refine hadd.congr ?_
  intro rho
  exact (normalizedProjectiveHorizontalSourceTerm_eq_local_add_far t rho).symm

/-- The complete horizontal source family is summable on the actual
off-ordinate carrier. -/
theorem normalizedProjectiveHorizontalSourceTerm_summable_offOrd
    {t : ℝ} (ht : 18 ≤ t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) :=
  (normalizedProjectiveHorizontalSourceTerm_summable_full ht).subtype _

/-- Finite local off-ordinate sources for which the signed-near criterion is not
available. -/
def normalizedProjectiveHorizontalMiddleFinset
    (t : ℝ) :
    Finset ((SameOrd t)ᶜ : Set Zeros) :=
  (nearOffFinset t 1).filter fun sigma =>
    ¬ normalizedProjectiveHorizontalSourceNear t (sigma : Zeros)

theorem mem_normalizedProjectiveHorizontalMiddleFinset_iff
    (t : ℝ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    sigma ∈ normalizedProjectiveHorizontalMiddleFinset t
      ↔
    |((sigma : Zeros) : ℂ).im - t| < 1
      ∧
    ¬ normalizedProjectiveHorizontalSourceNear t (sigma : Zeros) := by
  classical
  unfold normalizedProjectiveHorizontalMiddleFinset
  rw [Finset.mem_filter, mem_nearOffFinset_iff]
  simp

def normalizedProjectiveHorizontalMiddleTerm
    (t : ℝ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) : ℝ :=
  if sigma ∈ normalizedProjectiveHorizontalMiddleFinset t
  then normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
  else 0

theorem normalizedProjectiveHorizontalMiddleTerm_summable
    (t : ℝ) :
    Summable (normalizedProjectiveHorizontalMiddleTerm t) := by
  classical
  apply summable_of_ne_finset_zero
    (s := normalizedProjectiveHorizontalMiddleFinset t)
  intro sigma hsigma
  simp [normalizedProjectiveHorizontalMiddleTerm, hsigma]

theorem tsum_normalizedProjectiveHorizontalMiddleTerm
    (t : ℝ) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalMiddleTerm t sigma)
      =
    ∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) := by
  classical
  rw [tsum_eq_sum
    (s := normalizedProjectiveHorizontalMiddleFinset t)
    (fun sigma hsigma => by
      simp [normalizedProjectiveHorizontalMiddleTerm, hsigma])]
  simp [normalizedProjectiveHorizontalMiddleTerm]

/-- Pointwise one-sided decomposition on the off-ordinate carrier: signed-near
sources cost zero, local failures are retained exactly in the finite middle
carrier, and far sources are charged only by their absolute value. -/
theorem normalizedProjectiveHorizontalSourceTerm_le_middle_add_farAbs
    {t : ℝ} (ht : 18 ≤ t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
      ≤
    normalizedProjectiveHorizontalMiddleTerm t sigma
      +
    |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)| := by
  classical
  by_cases hlocal : |((sigma : Zeros) : ℂ).im - t| < 1
  · have hfar : ¬ 1 ≤ |((sigma : Zeros) : ℂ).im - t| :=
      not_le.mpr hlocal
    have hfarZero :
        normalizedProjectiveHorizontalFarTerm t (sigma : Zeros) = 0 := by
      simp [normalizedProjectiveHorizontalFarTerm, hfar]
    by_cases hnear :
        normalizedProjectiveHorizontalSourceNear t (sigma : Zeros)
    · have hnonpos :=
        normalizedProjectiveHorizontalSourceTerm_nonpos_of_near
          ht hnear
      have hnotMiddle :
          sigma ∉ normalizedProjectiveHorizontalMiddleFinset t := by
        intro hm
        have hm' :=
          (mem_normalizedProjectiveHorizontalMiddleFinset_iff t sigma).1 hm
        exact hm'.2 hnear
      simp [normalizedProjectiveHorizontalMiddleTerm,
        hnotMiddle, hfarZero]
      exact hnonpos
    · have hmiddle :
          sigma ∈ normalizedProjectiveHorizontalMiddleFinset t :=
        (mem_normalizedProjectiveHorizontalMiddleFinset_iff t sigma).2
          ⟨hlocal, hnear⟩
      simp [normalizedProjectiveHorizontalMiddleTerm,
        hmiddle, hfarZero]
  · have hfar : 1 ≤ |((sigma : Zeros) : ℂ).im - t| :=
      le_of_not_gt hlocal
    have hnotMiddle :
        sigma ∉ normalizedProjectiveHorizontalMiddleFinset t := by
      intro hm
      have hm' :=
        (mem_normalizedProjectiveHorizontalMiddleFinset_iff t sigma).1 hm
      exact hlocal hm'.1
    have hfarEq :
        normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)
          =
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) := by
      simp [normalizedProjectiveHorizontalFarTerm, hfar]
    simp [normalizedProjectiveHorizontalMiddleTerm,
      hnotMiddle, hfarEq, le_abs_self]

/--
Literal infinite horizontal aggregate reduction.

There exists a nonnegative canonical far coefficient K such that

  sum'_off horizontalSource
    <= finiteMiddleSum + K * sum'_all tailTerm.

The near signed region is absent from the positive budget altogether.
-/
theorem exists_offOrdProjectiveHorizontal_le_middle_add_farTail
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤
      (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        +
      K * ∑' rho : Zeros, tailTerm t rho := by
  obtain ⟨K, hK0, habsFarFull, hdom, hfarTotal⟩ :=
    exists_canonicalProjectiveHorizontalFarSummableBound ht
  have hleft :=
    normalizedProjectiveHorizontalSourceTerm_summable_offOrd ht
  have hmiddle :=
    normalizedProjectiveHorizontalMiddleTerm_summable t
  have hfarOff :
      Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)| :=
    habsFarFull.subtype _
  have hrhs :
      Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        normalizedProjectiveHorizontalMiddleTerm t sigma
          + |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)| :=
    hmiddle.add hfarOff
  have hpoint : ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
        ≤
      normalizedProjectiveHorizontalMiddleTerm t sigma
        + |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)| :=
    normalizedProjectiveHorizontalSourceTerm_le_middle_add_farAbs ht
  have hsum :=
    hleft.tsum_le_tsum hpoint hrhs
  have hsplit :
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalMiddleTerm t sigma
          + |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)|)
        =
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalMiddleTerm t sigma)
        +
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)|) := by
    exact hmiddle.tsum_add hfarOff
  rw [hsplit, tsum_normalizedProjectiveHorizontalMiddleTerm] at hsum
  have hsubFar :
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)|)
        ≤
      ∑' rho : Zeros,
        |normalizedProjectiveHorizontalFarTerm t rho| := by
    exact Summable.tsum_subtype_le
      _ _
      (fun rho => abs_nonneg _)
      habsFarFull
  refine ⟨K, hK0, ?_⟩
  calc
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      ≤
    (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      +
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      |normalizedProjectiveHorizontalFarTerm t (sigma : Zeros)|) := hsum
    _ ≤
    (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      +
    (∑' rho : Zeros,
      |normalizedProjectiveHorizontalFarTerm t rho|) := by
        exact add_le_add_left hsubFar _
    _ ≤
    (∑ sigma ∈ normalizedProjectiveHorizontalMiddleFinset t,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
      +
    K * ∑' rho : Zeros, tailTerm t rho := by
        exact add_le_add_left hfarTotal _

end Synthesis
