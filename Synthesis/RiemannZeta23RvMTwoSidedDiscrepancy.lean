import Synthesis.RiemannZeta23RvMIntervalDiscrepancyBound
import Zeta23.ZetaReflect

/-!
# Two-sided literal RvM discrepancy

The normalized q-carrier around a large positive sample height still sees zeros
of both signs of the ordinate.  Therefore the cumulative RvM producer must not
silently become a positive-ordinate theorem.

Zeta has exact conjugation symmetry:
  rho is a nontrivial zero -> conj rho is a nontrivial zero,
with the same analytic multiplicity.  At good endpoints this identifies the
half-open windows exactly,

  N(-T2,-T1) = N(T1,T2).

The archimedean density mu is even, so its interval integral has the same
symmetry.  Consequently the arbitrary positive-height discrepancy theorem
already proved by Zeta23 transports verbatim to the negative-height window.

This closes the sign-of-ordinate transport needed before normalized q-grid
attachment.
-/

noncomputable section

open Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

theorem zeta_nontrivial_conj
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    IsNontrivialZero (conj rho) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj hrho.not_trivial.2, hrho.1]
    simp
  · simpa using hrho.2.1
  · simpa using hrho.2.2

theorem zeroMult_conj_of_nontrivial
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    zeroMult (conj rho) = zeroMult rho := by
  unfold zeroMult
  exact congrArg ENat.toNat
    (analyticOrderAt_zeta_conj hrho.not_trivial.2)

private theorem conj_injective :
    Function.Injective (fun z : ℂ => conj z) := by
  intro z w h
  have h' := congrArg (fun u : ℂ => conj u) h
  simpa using h'

theorem conj_image_zerosIn_eq
    {T1 T2 : ℝ}
    (hg1 : GoodHeight T1) (hg2 : GoodHeight T2) :
    (fun z : ℂ => conj z) '' zerosIn T1 T2
      =
    zerosIn (-T2) (-T1) := by
  ext z
  constructor
  · rintro ⟨rho, ⟨hz, hlo, hhi⟩, rfl⟩
    have hstrict : rho.im < T2 :=
      lt_of_le_of_ne hhi (hg2 rho hz)
    refine ⟨zeta_nontrivial_conj hz, ?_, ?_⟩
    · simp only [Complex.conj_im]
      linarith
    · simp only [Complex.conj_im]
      linarith
  · intro hzwin
    rcases hzwin with ⟨hz, hlo, hhi⟩
    let rho : ℂ := conj z
    have hrho : IsNontrivialZero rho := by
      dsimp [rho]
      exact zeta_nontrivial_conj hz
    have hne : z.im ≠ -T1 := by
      intro heq
      apply hg1 rho hrho
      dsimp [rho]
      simp [heq]
    have hstrict : z.im < -T1 :=
      lt_of_le_of_ne hhi hne
    refine ⟨rho, ?_, ?_⟩
    · refine ⟨hrho, ?_, ?_⟩
      · dsimp [rho]
        simp only [Complex.conj_im]
        linarith
      · dsimp [rho]
        simp only [Complex.conj_im]
        linarith
    · dsimp [rho]
      simp

theorem Ncount_neg_window_eq
    {T1 T2 : ℝ}
    (hg1 : GoodHeight T1) (hg2 : GoodHeight T2) :
    Ncount (-T2) (-T1) = Ncount T1 T2 := by
  have hset := conj_image_zerosIn_eq
    (T1 := T1) (T2 := T2) hg1 hg2
  unfold Ncount
  rw [← hset]
  calc
    (∑ᶠ sigma ∈
        (fun z : ℂ => conj z) '' zerosIn T1 T2,
        zeroMult sigma)
      =
    ∑ᶠ rho ∈ zerosIn T1 T2,
      zeroMult (conj rho) := by
        exact finsum_mem_image conj_injective.injOn
    _ =
    ∑ᶠ rho ∈ zerosIn T1 T2,
      zeroMult rho := by
        apply finsum_mem_congr rfl
        intro rho hrho
        exact zeroMult_conj_of_nontrivial hrho.1

theorem intervalIntegral_mu_neg_window_eq
    (T1 T2 : ℝ) :
    (∫ t in (-T2)..(-T1), mu t)
      =
    ∫ t in T1..T2, mu t := by
  rw [← intervalIntegral.integral_comp_neg
    (f := mu) (a := T1) (b := T2)]
  apply intervalIntegral.integral_congr
  intro t ht
  exact mu_even t

/--
The same quantitative cumulative RvM discrepancy on the reflected negative
ordinate window.  Constants are literally inherited from the positive theorem.
-/
theorem literal_zeta_negative_interval_discrepancy_quantitative :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ T1 T2 : ℝ,
        max T0 3 <= T1 ->
        T1 < T2 ->
        GoodHeight T1 ->
        GoodHeight T2 ->
        |(Ncount (-T2) (-T1) : ℝ)
          - (∫ t in (-T2)..(-T1), mu t)|
          <=
        (C * Real.log T1 + Real.pi + C * Real.log T2) / Real.pi := by
  obtain ⟨C, T0, hC, hpos⟩ :=
    literal_zeta_interval_discrepancy_quantitative
  refine ⟨C, T0, hC, ?_⟩
  intro T1 T2 hT h12 hg1 hg2
  rw [Ncount_neg_window_eq hg1 hg2,
      intervalIntegral_mu_neg_window_eq]
  exact hpos T1 T2 hT h12 hg1 hg2

end Synthesis
