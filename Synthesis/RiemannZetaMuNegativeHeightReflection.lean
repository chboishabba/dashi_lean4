import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy
import Synthesis.RiemannRvMMuIntegrationByParts
import Zeta23.Statement.SeamClosed
import Zeta23.ZetaReflect
import Zeta23.GammaFacts.Complete

/-!
# Negative-height reflection for the literal Zeta23 N-mu discrepancy

The Zeta23 counting window is (A,B].  Complex conjugation sends it to
[-B,-A), so the naive identity N(A,B)=N(-B,-A) is endpoint-wrong.

This module keeps the correction exactly.  Let M(T) be the total zero
multiplicity at ordinate T.  Then

  N(A,B) = N(-B,-A) + M(B) - M(A)

as a real-valued identity.

The smooth density is exactly even, hence

  integral_A^B mu = integral_{-B}^{-A} mu.

These two facts are the representation adapter needed to transport the far
negative part of a centred Abel window to a positive one.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped BigOperators Interval Real ComplexConjugate

namespace Synthesis

open Zeta23

def zetaZeroOrdinateMultiplicity (T : ℝ) : ℕ :=
  ∑ᶠ rho ∈ {rho : ℂ | IsNontrivialZero rho ∧ rho.im = T},
    zeroMult rho

theorem zetaZeroOrdinateSet_finite (T : ℝ) :
    ({rho : ℂ | IsNontrivialZero rho ∧ rho.im = T}).Finite := by
  apply (zerosIn_finite (T-1) T).subset
  intro rho h
  exact ⟨h.1, by linarith, h.2.le⟩

theorem isNontrivialZero_conj
    {rho : ℂ} (h : IsNontrivialZero rho) :
    IsNontrivialZero (conj rho) := by
  constructor
  · rw [Zeta23.riemannZeta_conj h.not_trivial.2, h.1, map_zero]
  constructor
  · simpa using h.2.1
  · simpa using h.2.2

theorem zeroMult_conj
    {rho : ℂ} (h : IsNontrivialZero rho) :
    zeroMult (conj rho) = zeroMult rho := by
  unfold zeroMult
  exact congrArg ENat.toNat
    (Zeta23.analyticOrderAt_zeta_conj h.not_trivial.2)

private theorem conj_maps_zerosIn_to_reflectedHalfOpen
    {A B : ℝ}
    {rho : ℂ}
    (h : rho ∈ zerosIn A B) :
    IsNontrivialZero (conj rho)
      ∧ -B <= (conj rho).im
      ∧ (conj rho).im < -A := by
  refine ⟨isNontrivialZero_conj h.1, ?_, ?_⟩
  · simpa using neg_le_neg h.2.2
  · simpa using neg_lt_neg h.2.1

private theorem conj_maps_reflectedHalfOpen_to_zerosIn
    {A B : ℝ}
    {rho : ℂ}
    (h :
      IsNontrivialZero rho
        ∧ -B <= rho.im
        ∧ rho.im < -A) :
    conj rho ∈ zerosIn A B := by
  refine ⟨isNontrivialZero_conj h.1, ?_, ?_⟩
  · simpa using neg_lt_neg h.2.2
  · simpa using neg_le_neg h.2.1

def reflectedHalfOpenZeros (A B : ℝ) : Set ℂ :=
  {rho : ℂ |
    IsNontrivialZero rho
      ∧ -B <= rho.im
      ∧ rho.im < -A}

theorem reflectedHalfOpenZeros_finite
    (A B : ℝ) :
    (reflectedHalfOpenZeros A B).Finite := by
  have hfin := zerosIn_finite A B
  let e : ℂ ≃ ℂ := {
    toFun := conj
    invFun := conj
    left_inv := Complex.conj_conj
    right_inv := Complex.conj_conj
  }
  have himage :
      e '' zerosIn A B = reflectedHalfOpenZeros A B := by
    ext rho
    constructor
    · rintro ⟨sigma,hsigma,rfl⟩
      exact conj_maps_zerosIn_to_reflectedHalfOpen hsigma
    · intro hrho
      refine ⟨conj rho, ?_, by simp [e]⟩
      exact conj_maps_reflectedHalfOpen_to_zerosIn hrho
  rw [← himage]
  exact hfin.image e

theorem zetaCount_eq_reflectedHalfOpen
    {A B : ℝ} :
    (Ncount A B : ℝ)
      =
    ∑ᶠ rho ∈ reflectedHalfOpenZeros A B,
      (zeroMult rho : ℝ) := by
  classical
  have hsrc := zerosIn_finite A B
  have htgt := reflectedHalfOpenZeros_finite A B
  rw [Ncount,
      finsum_mem_eq_finite_toFinset_sum _ hsrc,
      finsum_mem_eq_finite_toFinset_sum _ htgt]
  let F := hsrc.toFinset
  let G := htgt.toFinset
  let f : ℂ -> ℂ := conj
  have hmap :
      F.image f = G := by
    ext rho
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨sigma,hsigma,rfl⟩
      exact conj_maps_zerosIn_to_reflectedHalfOpen hsigma
    · intro hrho
      refine ⟨conj rho, ?_, by simp [f]⟩
      exact conj_maps_reflectedHalfOpen_to_zerosIn hrho
  calc
    (∑ rho ∈ F, (zeroMult rho : ℝ))
      =
    ∑ rho ∈ F, (zeroMult (f rho) : ℝ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hz : IsNontrivialZero rho :=
        (Set.Finite.mem_toFinset.mp hrho).1
      rw [zeroMult_conj hz]
    _ =
    ∑ rho ∈ F.image f, (zeroMult rho : ℝ) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Complex.conj_injective hab
    _ = ∑ rho ∈ G, (zeroMult rho : ℝ) := by rw [hmap]

theorem reflectedHalfOpen_split_standard
    {A B : ℝ}
    (hAB : A <= B) :
    (∑ᶠ rho ∈ reflectedHalfOpenZeros A B,
      (zeroMult rho : ℝ))
      =
    (Ncount (-B) (-A) : ℝ)
      + zetaZeroOrdinateMultiplicity (-B)
      - zetaZeroOrdinateMultiplicity (-A) := by
  let interior : Set ℂ := zerosIn (-B) (-A)
  let left : Set ℂ :=
    {rho : ℂ | IsNontrivialZero rho ∧ rho.im = -B}
  let right : Set ℂ :=
    {rho : ℂ | IsNontrivialZero rho ∧ rho.im = -A}
  let reflected : Set ℂ := reflectedHalfOpenZeros A B

  have hI : interior.Finite := zerosIn_finite (-B) (-A)
  have hL : left.Finite := zetaZeroOrdinateSet_finite (-B)
  have hR : right.Finite := zetaZeroOrdinateSet_finite (-A)
  have hS : reflected.Finite := reflectedHalfOpenZeros_finite A B

  have hSR : Disjoint reflected right := by
    rw [Set.disjoint_left]
    intro rho hs hr
    have hslt : rho.im < -A := hs.2.2
    have hre : rho.im = -A := hr.2
    linarith

  have hIL : Disjoint interior left := by
    rw [Set.disjoint_left]
    intro rho hi hl
    have hilt : -B < rho.im := hi.2.1
    have hle : rho.im = -B := hl.2
    linarith

  have hunion :
      reflected ∪ right = interior ∪ left := by
    ext rho
    constructor
    · intro h
      rcases h with hs | hr
      · by_cases hy : rho.im = -B
        · exact Or.inr ⟨hs.1, hy⟩
        · exact Or.inl
            ⟨hs.1,
              lt_of_le_of_ne hs.2.1 (Ne.symm hy),
              (le_of_lt hs.2.2)⟩
      · by_cases hEq : A = B
        · subst B
          exact Or.inr ⟨hr.1, by simpa using hr.2⟩
        · have hBA : -B < -A := by
            exact neg_lt_neg (lt_of_le_of_ne hAB hEq)
          exact Or.inl ⟨hr.1, by simpa [hr.2] using hBA, hr.2.le⟩
    · intro h
      rcases h with hi | hl
      · by_cases hy : rho.im = -A
        · exact Or.inr ⟨hi.1, hy⟩
        · exact Or.inl
            ⟨hi.1,
              hi.2.1.le,
              lt_of_le_of_ne hi.2.2 hy⟩
      · by_cases hEq : A = B
        · subst B
          exact Or.inr ⟨hl.1, by simpa using hl.2⟩
        · have hBA : -B < -A := by
            exact neg_lt_neg (lt_of_le_of_ne hAB hEq)
          exact Or.inl ⟨hl.1, hl.2.ge, by simpa [hl.2] using hBA⟩

  have hleftUnion :
      (∑ᶠ rho ∈ reflected ∪ right, (zeroMult rho : ℝ))
        =
      (∑ᶠ rho ∈ reflected, (zeroMult rho : ℝ))
        +
      (∑ᶠ rho ∈ right, (zeroMult rho : ℝ)) :=
    finsum_mem_union hSR hS hR

  have hrightUnion :
      (∑ᶠ rho ∈ interior ∪ left, (zeroMult rho : ℝ))
        =
      (∑ᶠ rho ∈ interior, (zeroMult rho : ℝ))
        +
      (∑ᶠ rho ∈ left, (zeroMult rho : ℝ)) :=
    finsum_mem_union hIL hI hL

  have hbalance :
      (∑ᶠ rho ∈ reflected, (zeroMult rho : ℝ))
        +
      (∑ᶠ rho ∈ right, (zeroMult rho : ℝ))
      =
      (∑ᶠ rho ∈ interior, (zeroMult rho : ℝ))
        +
      (∑ᶠ rho ∈ left, (zeroMult rho : ℝ)) := by
    rw [← hleftUnion, hunion, hrightUnion]

  change
    (∑ᶠ rho ∈ reflected, (zeroMult rho : ℝ))
      =
    (∑ᶠ rho ∈ interior, (zeroMult rho : ℝ))
      + (∑ᶠ rho ∈ left, (zeroMult rho : ℝ))
      - (∑ᶠ rho ∈ right, (zeroMult rho : ℝ))
  linarith


theorem zetaZeroOrdinateMultiplicity_neg (T : ℝ) :
    zetaZeroOrdinateMultiplicity (-T)
      = zetaZeroOrdinateMultiplicity T := by
  classical
  let S : Set ℂ :=
    {rho : ℂ | IsNontrivialZero rho ∧ rho.im = T}
  let Sn : Set ℂ :=
    {rho : ℂ | IsNontrivialZero rho ∧ rho.im = -T}
  have hS := zetaZeroOrdinateSet_finite T
  have hSn := zetaZeroOrdinateSet_finite (-T)
  unfold zetaZeroOrdinateMultiplicity
  rw [finsum_mem_eq_finite_toFinset_sum _ hSn,
      finsum_mem_eq_finite_toFinset_sum _ hS]
  let F := hS.toFinset
  let G := hSn.toFinset
  let f : ℂ -> ℂ := conj
  have hmap : F.image f = G := by
    ext rho
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨sigma,hsigma,rfl⟩
      exact ⟨isNontrivialZero_conj hsigma.1, by simpa [hsigma.2]⟩
    · intro hrho
      refine ⟨conj rho, ?_, by simp [f]⟩
      exact ⟨isNontrivialZero_conj hrho.1, by simpa [hrho.2]⟩
  calc
    (∑ rho ∈ G, zeroMult rho)
      = ∑ rho ∈ F.image f, zeroMult rho := by rw [hmap]
    _ = ∑ rho ∈ F, zeroMult (f rho) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Complex.conj_injective hab
    _ = ∑ rho ∈ F, zeroMult rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact zeroMult_conj (Set.Finite.mem_toFinset.mp hrho).1

/--
Endpoint-correct conjugation reflection for the literal (A,B] zero count.
-/
theorem zetaNcount_reflection_endpoint_correct
    {A B : ℝ}
    (hAB : A <= B) :
    (Ncount A B : ℝ)
      =
    (Ncount (-B) (-A) : ℝ)
      + (zetaZeroOrdinateMultiplicity B : ℝ)
      - (zetaZeroOrdinateMultiplicity A : ℝ) := by
  rw [zetaCount_eq_reflectedHalfOpen,
      reflectedHalfOpen_split_standard hAB,
      zetaZeroOrdinateMultiplicity_neg,
      zetaZeroOrdinateMultiplicity_neg]

/--
Evenness of mu transported to interval integrals.
-/
theorem zetaMuIntegral_reflection
    (A B : ℝ) :
    (∫ x in A..B, Zeta23.mu x)
      =
    ∫ x in (-B)..(-A), Zeta23.mu x := by
  calc
    (∫ x in A..B, Zeta23.mu x)
      =
    ∫ x in A..B, Zeta23.mu (-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Zeta23.mu_even]
    _ = ∫ x in (-B)..(-A), Zeta23.mu x := by
      exact intervalIntegral.integral_comp_neg

/--
Endpoint-correct reflection of the literal N-mu discrepancy.
-/
theorem zetaMuWindowDiscrepancy_reflection_endpoint_correct
    {A B : ℝ}
    (hAB : A <= B) :
    zetaMuWindowDiscrepancy A B
      =
    zetaMuWindowDiscrepancy (-B) (-A)
      + (zetaZeroOrdinateMultiplicity B : ℝ)
      - (zetaZeroOrdinateMultiplicity A : ℝ) := by
  unfold zetaMuWindowDiscrepancy
  rw [zetaNcount_reflection_endpoint_correct hAB,
      zetaMuIntegral_reflection]
  ring


/--
Multiplicity concentrated at one ordinate is bounded by the enclosing unit
window.  This is the endpoint correction estimate used by the reflected
negative-height discrepancy.
-/
theorem zetaZeroOrdinateMultiplicity_le_unitWindow
    (T : ℝ) :
    zetaZeroOrdinateMultiplicity T
      <= Ncount (T-1) T := by
  have hsub :
      {rho : ℂ | IsNontrivialZero rho ∧ rho.im = T}
        ⊆ zetaZeroConfig.window (T-1) T := by
    intro rho h
    exact ⟨h.1, by linarith [h.2], h.2.le⟩
  have hmono :=
    zetaZeroConfig.finsum_mult_mono
      (T-1) T hsub subset_rfl
  simpa [zetaZeroOrdinateMultiplicity,
    zetaZeroConfig_N, ZeroConfig.N] using hmono

/--
Endpoint multiplicity has the same two-sided logarithmic local-count envelope
as the enclosing unit window.
-/
theorem exists_zetaZeroOrdinateMultiplicity_log_bound :
    ∃ A0 : ℝ, 1 <= A0 ∧
      ∀ T : ℝ,
        (zetaZeroOrdinateMultiplicity T : ℝ)
          <= A0 * Real.log (|T-1| + 3) := by
  obtain ⟨A0,hA01,hlocal⟩ :=
    Zeta23.RvM.zeta_local_zero_count
  refine ⟨A0,hA01,?_⟩
  intro T
  have hm := zetaZeroOrdinateMultiplicity_le_unitWindow T
  have hw := hlocal (T-1)
  have hcast :
      (zetaZeroOrdinateMultiplicity T : ℝ)
        <= (Ncount (T-1) T : ℝ) := by
    exact_mod_cast hm
  exact hcast.trans (by simpa [sub_add_cancel] using hw)

/--
The growing negative segment (A,-t] is transported to the positive window
(t,-A], up to the two endpoint multiplicity corrections forced by the literal
(A,B] convention.
-/
theorem zetaMuWindowDiscrepancy_negativeSegment_reflected
    {A t : ℝ}
    (hAt : A <= -t) :
    zetaMuWindowDiscrepancy A (-t)
      =
    zetaMuWindowDiscrepancy t (-A)
      + (zetaZeroOrdinateMultiplicity t : ℝ)
      - (zetaZeroOrdinateMultiplicity A : ℝ) := by
  have h :=
    zetaMuWindowDiscrepancy_reflection_endpoint_correct hAt
  simpa using h

/--
Uniform logarithmic envelope for the reflected far-negative segment.

For t in the positive RvM regime and A<-t, the only growing term is the
positive-window discrepancy D(t,-A) plus the endpoint multiplicity at A.
-/
theorem exists_zetaMuWindowDiscrepancy_negativeSegment_bound :
    ∃ C T0 A0 : ℝ, 0 <= C ∧ 1 <= A0 ∧
      ∀ t A : ℝ,
        max T0 4 <= t ->
        A < -t ->
        |zetaMuWindowDiscrepancy A (-t)|
          <=
        C * (Real.log (t+3) + Real.log (-A+4))
          + A0 * Real.log (|t-1|+3)
          + A0 * Real.log (|A-1|+3) := by
  obtain ⟨C,T0,hC,hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  obtain ⟨A0,hA01,hM⟩ :=
    exists_zetaZeroOrdinateMultiplicity_log_bound
  refine ⟨C,T0,A0,hC,hA01,?_⟩
  intro t A ht hAt
  have htA : t < -A := by linarith
  have href :=
    zetaMuWindowDiscrepancy_negativeSegment_reflected hAt.le
  rw [href]
  have hpos :
      |zetaMuWindowDiscrepancy t (-A)|
        <= C * (Real.log (t+3) + Real.log (-A+4)) :=
    hD t (-A) ht htA
  have hMt := hM t
  have hMA := hM A
  have hMt0 : 0 <= (zetaZeroOrdinateMultiplicity t : ℝ) := by positivity
  have hMA0 : 0 <= (zetaZeroOrdinateMultiplicity A : ℝ) := by positivity
  calc
    |zetaMuWindowDiscrepancy t (-A)
        + (zetaZeroOrdinateMultiplicity t : ℝ)
        - (zetaZeroOrdinateMultiplicity A : ℝ)|
      <=
    |zetaMuWindowDiscrepancy t (-A)|
      + (zetaZeroOrdinateMultiplicity t : ℝ)
      + (zetaZeroOrdinateMultiplicity A : ℝ) := by
        have h1 := abs_sub
          (zetaMuWindowDiscrepancy t (-A)
            + (zetaZeroOrdinateMultiplicity t : ℝ))
          (zetaZeroOrdinateMultiplicity A : ℝ)
        have h2 := abs_add
          (zetaMuWindowDiscrepancy t (-A))
          (zetaZeroOrdinateMultiplicity t : ℝ)
        rw [abs_of_nonneg hMt0, abs_of_nonneg hMA0] at h1 h2
        linarith
    _ <=
    C * (Real.log (t+3) + Real.log (-A+4))
      + A0 * Real.log (|t-1|+3)
      + A0 * Real.log (|A-1|+3) := by
        linarith

end Synthesis
