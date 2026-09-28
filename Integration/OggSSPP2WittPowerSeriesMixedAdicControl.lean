import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.MvPowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesMaximalIdeal

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
  mixedAdicHausdorffProved := false
  mixedAdicPrecompleteProved := false

end Integration.OggSSPP2WittPowerSeriesMixedAdicControl
