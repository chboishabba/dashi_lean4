import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.MvPowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.NumberTheory.Padics.PadicIntegers
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesMaximalIdeal
import Integration.OggSSPP2WittPowerSeriesCompleteness

/-!
# Mixed-adic coefficient control for the p=2 Witt power-series base

Let
  A = W(F₂),
  m = maximalIdeal A,
  R = A[[X]],
  J = C(m) + (X).

The previous owner proves J is the actual maximal ideal of R.

This module proves the first coefficient-control estimates needed for J-adic
completeness:

* membership in C(m)^n forces every coefficient into m^n;
* membership in (X)^(k+1) forces the k-th coefficient to vanish;
* hence membership in J^(n+k+1) forces the k-th coefficient into m^n.

The last step uses Mathlib's
  Ideal.sup_pow_add_le_pow_sup_pow.
-/

namespace Integration.OggSSPP2WittPowerSeriesMixedAdicControl

open Integration.OggSSPP2WittPowerSeriesBase
open Integration.OggSSPP2WittPowerSeriesMaximalIdeal

noncomputable local instance : IsLocalRing P2WittRing :=
  p2WittIsLocalRing

noncomputable theorem coefficientMaximalIdeal_fg :
    coefficientMaximalIdeal.FG := by
  have hz :
      (IsLocalRing.maximalIdeal ℤ_[2]).FG := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span (Set.finite_singleton (2 : ℤ_[2]))
  have hm :=
    hz.map p2WittEquivPadicInt.symm.toRingHom
  simpa [coefficientMaximalIdeal,
    IsLocalRing.map_ringEquiv_maximalIdeal] using hm

theorem coeff_mem_of_mem_coefficientMaxPower
    {f : P2WittPowerSeriesBase} {n k : Nat}
    (hf : f ∈ coefficientMaximalIdealInPowerSeries ^ n) :
    PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ n := by
  have hf' :
      f ∈ (coefficientMaximalIdeal ^ n).map PowerSeries.C := by
    simpa [coefficientMaximalIdealInPowerSeries, Ideal.map_pow] using hf
  exact
    MvPowerSeries.coeff_mem_of_mem_map_C hf'
      (Finsupp.single () k)

theorem coeff_eq_zero_of_mem_XPower
    {f : P2WittPowerSeriesBase} {n k : Nat}
    (hk : k < n)
    (hf : f ∈ (Ideal.span ({PowerSeries.X} :
      Set P2WittPowerSeriesBase)) ^ n) :
    PowerSeries.coeff k f = 0 := by
  have hspan :
      f ∈ Ideal.span ({PowerSeries.X ^ n} :
        Set P2WittPowerSeriesBase) := by
    simpa [Ideal.span_singleton_pow] using hf
  have hdvd : PowerSeries.X ^ n ∣ f := by
    simpa [Ideal.mem_span_singleton] using hspan
  exact (PowerSeries.X_pow_dvd_iff.mp hdvd k hk)

theorem coeff_mem_of_mem_mixedPower
    {f : P2WittPowerSeriesBase} (n k : Nat)
    (hf : f ∈ deformationTwoPartIdeal ^ (n + (k + 1))) :
    PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ n := by
  have hle :
      deformationTwoPartIdeal ^ (n + (k + 1)) ≤
        coefficientMaximalIdealInPowerSeries ^ n ⊔
          (Ideal.span ({PowerSeries.X} :
            Set P2WittPowerSeriesBase)) ^ (k + 1) := by
    exact Ideal.sup_pow_add_le_pow_sup_pow
  have hsup := hle hf
  rcases Submodule.mem_sup.mp hsup with ⟨a, ha, b, hb, hab⟩
  have haCoeff :
      PowerSeries.coeff k a ∈ coefficientMaximalIdeal ^ n :=
    coeff_mem_of_mem_coefficientMaxPower ha
  have hbCoeff :
      PowerSeries.coeff k b = 0 :=
    coeff_eq_zero_of_mem_XPower (Nat.lt_succ_self k) hb
  have hcoeff :
      PowerSeries.coeff k f =
        PowerSeries.coeff k a + PowerSeries.coeff k b := by
    rw [← hab]
    simp
  rw [hcoeff, hbCoeff, add_zero]
  exact haCoeff

theorem coeff_mem_of_mem_actualMaximalPower
    {f : P2WittPowerSeriesBase} (n k : Nat)
    (hf :
      f ∈ (IsLocalRing.maximalIdeal P2WittPowerSeriesBase) ^
        (n + (k + 1))) :
    PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ n := by
  apply coeff_mem_of_mem_mixedPower n k
  rwa [deformationTwoPartIdeal_eq_maximalIdeal]

def finitePrefix (n : Nat) (f : P2WittPowerSeriesBase) :
    P2WittPowerSeriesBase :=
  ∑ k ∈ Finset.range n,
    PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k

theorem coeff_finitePrefix_of_lt
    {f : P2WittPowerSeriesBase} {n k : Nat}
    (hk : k < n) :
    PowerSeries.coeff k (finitePrefix n f) =
      PowerSeries.coeff k f := by
  simp only [finitePrefix, map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp [hk]
  · intro b hb hbk
    simp [hbk.symm]
  · simp [hk]

theorem tail_divisible_by_X_pow
    (n : Nat) (f : P2WittPowerSeriesBase) :
    PowerSeries.X ^ n ∣ f - finitePrefix n f := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_finitePrefix_of_lt hk, sub_self]

theorem tail_mem_XIdealPower
    (n : Nat) (f : P2WittPowerSeriesBase) :
    f - finitePrefix n f ∈
      (Ideal.span ({PowerSeries.X} :
        Set P2WittPowerSeriesBase)) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact tail_divisible_by_X_pow n f

theorem constantCoefficientPower_mem_mixedPower
    {a : P2WittRing} {n : Nat}
    (ha : a ∈ coefficientMaximalIdeal ^ n) :
    PowerSeries.C a ∈ deformationTwoPartIdeal ^ n := by
  have hmap :
      PowerSeries.C a ∈
        coefficientMaximalIdealInPowerSeries ^ n := by
    have :
        PowerSeries.C a ∈
          (coefficientMaximalIdeal ^ n).map PowerSeries.C :=
      Ideal.mem_map_of_mem PowerSeries.C ha
    simpa [coefficientMaximalIdealInPowerSeries, Ideal.map_pow] using this
  exact
    Ideal.pow_right_mono
      (le_sup_left :
        coefficientMaximalIdealInPowerSeries ≤ deformationTwoPartIdeal)
      n hmap

theorem XPower_mem_mixedPower (n : Nat) :
    PowerSeries.X ^ n ∈ deformationTwoPartIdeal ^ n := by
  exact Ideal.pow_mem_pow X_mem_twoPart n

theorem prefixMonomial_mem_mixedPower
    {f : P2WittPowerSeriesBase} {n k : Nat}
    (hk : k < n)
    (hcoeff :
      PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ (n - k)) :
    PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k ∈
      deformationTwoPartIdeal ^ n := by
  have hc :
      PowerSeries.C (PowerSeries.coeff k f) ∈
        deformationTwoPartIdeal ^ (n - k) :=
    constantCoefficientPower_mem_mixedPower hcoeff
  have hx :
      PowerSeries.X ^ k ∈ deformationTwoPartIdeal ^ k :=
    XPower_mem_mixedPower k
  have hmul :
      PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k ∈
        deformationTwoPartIdeal ^ (n - k) *
          deformationTwoPartIdeal ^ k :=
    Ideal.mul_mem_mul hc hx
  rw [← pow_add, Nat.sub_add_cancel hk.le] at hmul
  exact hmul

theorem finitePrefix_mem_mixedPower
    {f : P2WittPowerSeriesBase} {n : Nat}
    (hcoeff :
      ∀ k, k < n →
        PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ (n - k)) :
    finitePrefix n f ∈ deformationTwoPartIdeal ^ n := by
  apply Ideal.sum_mem
  intro k hk
  exact prefixMonomial_mem_mixedPower
    (Finset.mem_range.mp hk) (hcoeff k (Finset.mem_range.mp hk))

theorem mixedPower_mem_of_lowCoefficientControl
    {f : P2WittPowerSeriesBase} {n : Nat}
    (hcoeff :
      ∀ k, k < n →
        PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ (n - k)) :
    f ∈ deformationTwoPartIdeal ^ n := by
  have hprefix := finitePrefix_mem_mixedPower hcoeff
  have htail :
      f - finitePrefix n f ∈ deformationTwoPartIdeal ^ n := by
    have hx := tail_mem_XIdealPower n f
    exact Ideal.pow_right_mono
      (le_sup_right :
        (Ideal.span ({PowerSeries.X} :
          Set P2WittPowerSeriesBase)) ≤ deformationTwoPartIdeal)
      n hx
  have hadd :=
    (deformationTwoPartIdeal ^ n).add_mem htail hprefix
  simpa [sub_add_cancel] using hadd

theorem actualMaximalPower_mem_of_lowCoefficientControl
    {f : P2WittPowerSeriesBase} {n : Nat}
    (hcoeff :
      ∀ k, k < n →
        PowerSeries.coeff k f ∈ coefficientMaximalIdeal ^ (n - k)) :
    f ∈ (IsLocalRing.maximalIdeal P2WittPowerSeriesBase) ^ n := by
  rw [← deformationTwoPartIdeal_eq_maximalIdeal]
  exact mixedPower_mem_of_lowCoefficientControl hcoeff

noncomputable local instance :
    IsAdicComplete coefficientMaximalIdeal P2WittRing :=
  Integration.OggSSPP2WittPowerSeriesCompleteness.p2WittMaximalIdealAdicallyComplete

noncomputable def powerSeriesMaximalIdealHausdorff :
    IsHausdorff
      (IsLocalRing.maximalIdeal P2WittPowerSeriesBase)
      P2WittPowerSeriesBase where
  haus' f hf := by
    apply PowerSeries.ext
    intro k
    apply IsHausdorff.haus'
      (I := coefficientMaximalIdeal)
      (PowerSeries.coeff k f)
    intro n
    have hdeep :=
      hf (n + (k + 1))
    have hfmem :
        f ∈ (IsLocalRing.maximalIdeal P2WittPowerSeriesBase) ^
          (n + (k + 1)) := by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hdeep
    have hcoeff :=
      coeff_mem_of_mem_actualMaximalPower n k hfmem
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hcoeff

structure Boundary where
  coefficientMaximalIdealFiniteGenerated : Bool
  coefficientIdealPowerControlsAllCoefficients : Bool
  xPowerKillsLowerCoefficients : Bool
  mixedPowerControlsFixedCoefficient : Bool
  actualMaximalIdealPowerControlsFixedCoefficient : Bool
  mixedAdicHausdorffProved : Bool
  mixedAdicPrecompleteProved : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  coefficientMaximalIdealFiniteGenerated := true
  coefficientIdealPowerControlsAllCoefficients := true
  xPowerKillsLowerCoefficients := true
  mixedPowerControlsFixedCoefficient := true
  actualMaximalIdealPowerControlsFixedCoefficient := true
  mixedAdicHausdorffProved := true
  mixedAdicPrecompleteProved := false

end Integration.OggSSPP2WittPowerSeriesMixedAdicControl
