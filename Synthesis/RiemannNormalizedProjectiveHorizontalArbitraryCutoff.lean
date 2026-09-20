import Synthesis.RiemannNormalizedProjectiveHorizontalRefinedMiddle
import Zeta23Bridge.FarShellCutoffTailBound

/-!
# Arbitrary-cutoff horizontal reduction with vanishing far remainder

The cutoff |Im rho - t| = 1 was only a convenient first split.  The literal
zero-tail machinery already provides, for every J >= 1,

  tailTermFrom(t,J,rho)

and an explicit theorem-bearing bound

  sum' tailTermFrom <= farShellBound A |t| J,

with farShellBound tending to zero as J tends to infinity.

Using the same signed-favourable predicate as the refined local theorem, define
the difficult finite carrier at cutoff J to contain only off-ordinate zeros with

  |Im rho - t| < J

which evade both the linear and quadratic sign criteria.

Then the complete literal off-ordinate horizontal tsum is bounded above by that
finite signed carrier plus K_t times the far-shell bound.  The latter can be
made arbitrarily small without taking absolute values on any favourable near
source.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.OffOrdinateCutoffCarrier
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.FarShellCutoffTailBound

def normalizedProjectiveHorizontalRefinedMiddleFinsetAt
    (t : ℝ) (J : ℕ) :
    Finset ((SameOrd t)ᶜ : Set Zeros) :=
  (nearOffFinset t J).filter fun sigma =>
    ¬ normalizedProjectiveHorizontalSourceFavourable t (sigma : Zeros)

theorem mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt_iff
    (t : ℝ) (J : ℕ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J
      ↔
    |((sigma : Zeros) : ℂ).im - t| < (J : ℝ)
      ∧
    ¬ normalizedProjectiveHorizontalSourceFavourable t (sigma : Zeros) := by
  classical
  unfold normalizedProjectiveHorizontalRefinedMiddleFinsetAt
  rw [Finset.mem_filter, mem_nearOffFinset_iff]
  simp

def normalizedProjectiveHorizontalRefinedMiddleTermAt
    (t : ℝ) (J : ℕ)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) : ℝ :=
  if sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J
  then normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
  else 0

theorem normalizedProjectiveHorizontalRefinedMiddleTermAt_summable
    (t : ℝ) (J : ℕ) :
    Summable (normalizedProjectiveHorizontalRefinedMiddleTermAt t J) := by
  classical
  apply summable_of_ne_finset_zero
    (s := normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J)
  intro sigma hsigma
  simp [normalizedProjectiveHorizontalRefinedMiddleTermAt, hsigma]

theorem tsum_normalizedProjectiveHorizontalRefinedMiddleTermAt
    (t : ℝ) (J : ℕ) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma)
      =
    ∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros) := by
  classical
  rw [tsum_eq_sum
    (s := normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J)
    (fun sigma hsigma => by
      simp [normalizedProjectiveHorizontalRefinedMiddleTermAt, hsigma])]
  simp [normalizedProjectiveHorizontalRefinedMiddleTermAt]

/-- Outside the cutoff J>=1, the actual horizontal source inherits the same K
majorant against tailTermFrom. -/
theorem normalizedProjectiveHorizontalSource_abs_le_K_tailTermFrom
    {t K : ℝ} {J : ℕ}
    (hJ : 1 ≤ J)
    (hdom :
      ∀ rho : Zeros,
        |normalizedProjectiveHorizontalFarTerm t rho|
          ≤ K * tailTerm t rho)
    (rho : Zeros)
    (hfar : (J : ℝ) ≤ |(rho : ℂ).im - t|) :
    |normalizedProjectiveHorizontalSourceTerm t rho|
      ≤ K * tailTermFrom t J rho := by
  have hfar1 : 1 ≤ |(rho : ℂ).im - t| := by
    exact_mod_cast hJ at hJ
    linarith
  have hfarEq :
      normalizedProjectiveHorizontalFarTerm t rho
        = normalizedProjectiveHorizontalSourceTerm t rho := by
    simp [normalizedProjectiveHorizontalFarTerm, hfar1]
  have htail :
      tailTerm t rho = tailTermFrom t J rho := by
    unfold tailTerm tailTermFrom
    rw [if_pos hfar1, if_pos hfar]
  simpa [hfarEq, htail] using hdom rho

/-- Pointwise one-sided arbitrary-cutoff reduction. -/
theorem normalizedProjectiveHorizontalSourceTerm_le_middleAt_add_far
    {t K : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hdom :
      ∀ rho : Zeros,
        |normalizedProjectiveHorizontalFarTerm t rho|
          ≤ K * tailTerm t rho)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
      ≤
    normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma
      + K * tailTermFrom t J (sigma : Zeros) := by
  classical
  by_cases hinside :
      |((sigma : Zeros) : ℂ).im - t| < (J : ℝ)
  · have htail0 :
        tailTermFrom t J (sigma : Zeros) = 0 := by
      unfold tailTermFrom
      rw [if_neg]
      exact not_le.mpr hinside
    by_cases hfav :
        normalizedProjectiveHorizontalSourceFavourable
          t (sigma : Zeros)
    · have hnotMiddle :
          sigma ∉ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J := by
        intro hm
        have hm' :=
          (mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt_iff
            t J sigma).1 hm
        exact hm'.2 hfav
      have hnonpos :=
        normalizedProjectiveHorizontalSourceTerm_nonpos_of_favourable
          ht hfav
      simp [normalizedProjectiveHorizontalRefinedMiddleTermAt,
        hnotMiddle, htail0, hnonpos]
    · have hmiddle :
          sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J :=
        (mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt_iff
          t J sigma).2 ⟨hinside, hfav⟩
      simp [normalizedProjectiveHorizontalRefinedMiddleTermAt,
        hmiddle, htail0]
  · have hfar :
      (J : ℝ) ≤ |((sigma : Zeros) : ℂ).im - t| :=
      le_of_not_gt hinside
    have hnotMiddle :
        sigma ∉ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J := by
      intro hm
      have hm' :=
        (mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt_iff
          t J sigma).1 hm
      exact hinside hm'.1
    have habs :=
      normalizedProjectiveHorizontalSource_abs_le_K_tailTermFrom
        hJ hdom (sigma : Zeros) hfar
    have hself :
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
          ≤
        |normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)| :=
      le_abs_self _
    simp [normalizedProjectiveHorizontalRefinedMiddleTermAt, hnotMiddle]
    exact hself.trans habs

/--
Arbitrary-cutoff literal horizontal tsum theorem.

The difficult part is finite for every J; the theorem-bearing remainder tends
to zero with J.
-/
theorem exists_offOrdProjectiveHorizontal_cutoff_reduction
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      (∀ J : ℕ, 1 ≤ J →
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
          ≤
        (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
          normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
          +
        K * farShellBound A |t| J)
      ∧
      Tendsto
        (fun J : ℕ => K * farShellBound A |t| J)
        atTop (nhds 0) := by
  obtain ⟨K, hK0, habsFar, hdom, hfarTotal⟩ :=
    exists_canonicalProjectiveHorizontalFarSummableBound ht
  obtain ⟨A, hA1, hloc⟩ :=
    Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A, K, hA1, hK0, ?_, ?_⟩
  · intro J hJ
    have hleft :=
      normalizedProjectiveHorizontalSourceTerm_summable_offOrd ht
    have hmiddle :=
      normalizedProjectiveHorizontalRefinedMiddleTermAt_summable t J
    have htailFull :=
      summable_tailTermFrom hJ t
    have htailOff :
        Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
          K * tailTermFrom t J (sigma : Zeros) :=
      ((htailFull.mul_left K).subtype _)
    have hrhs :
        Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
          normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma
            + K * tailTermFrom t J (sigma : Zeros) :=
      hmiddle.add htailOff
    have hpoint : ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)
          ≤
        normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma
          + K * tailTermFrom t J (sigma : Zeros) :=
      normalizedProjectiveHorizontalSourceTerm_le_middleAt_add_far
        ht hJ hdom
    have hsum :=
      hleft.tsum_le_tsum hpoint hrhs
    have hsplit :
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma
            + K * tailTermFrom t J (sigma : Zeros))
          =
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveHorizontalRefinedMiddleTermAt t J sigma)
          +
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          K * tailTermFrom t J (sigma : Zeros)) := by
      exact hmiddle.tsum_add htailOff
    rw [hsplit,
      tsum_normalizedProjectiveHorizontalRefinedMiddleTermAt] at hsum
    have htailSubtype :
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          K * tailTermFrom t J (sigma : Zeros))
          ≤
        K * ∑' rho : Zeros, tailTermFrom t J rho := by
      rw [tsum_mul_left]
      have hsub :
          (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
            tailTermFrom t J (sigma : Zeros))
            ≤
          ∑' rho : Zeros, tailTermFrom t J rho := by
        exact Summable.tsum_subtype_le _ _
          (fun rho => tailTermFrom_nonneg t J rho)
          htailFull
      exact mul_le_mul_of_nonneg_left hsub hK0
    have htailBound :
        ∑' rho : Zeros, tailTermFrom t J rho
          ≤ farShellBound A |t| J :=
      tsum_tailTermFrom_le hA1 hloc t J hJ
    calc
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤
      (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        +
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        K * tailTermFrom t J (sigma : Zeros)) := hsum
      _ ≤
      (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        +
      K * ∑' rho : Zeros, tailTermFrom t J rho := by
        exact add_le_add_left htailSubtype _
      _ ≤
      (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        +
      K * farShellBound A |t| J := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left htailBound hK0) _
  · have hlim := farShellBound_tendsto_zero A |t|
    exact hlim.const_mul K

end Synthesis
