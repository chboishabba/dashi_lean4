import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

/-!
# The literal y² = x³ - x model is minimal with good reduction at every odd p

The global model has discriminant 64.  For every prime p != 2, 64 is a unit
in Z_p, hence its multiplicative DVR valuation is exactly 1.

Because mathlib's `valuation_Δ_aux` for every integral model is definitionally
bounded above by 1, this immediately makes the displayed integral equation
minimal: its discriminant valuation already attains the maximum possible
value.  The same valuation equality then gives good reduction.

This removes the chosen-minimal-model ambiguity from the odd-prime local
L-factor comparison.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

def cmPadicWeierstrass
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve ℚ_[p] :=
  cmWeierstrass.baseChange ℚ_[p]

theorem cmPadicWeierstrass_discriminant
    (p : ℕ) [Fact p.Prime] :
    (cmPadicWeierstrass p).Δ = 64 := by
  simp [cmPadicWeierstrass, cmWeierstrass_discriminant]

instance cmPadicWeierstrass_isIntegral
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsIntegral ℤ_[p]
      (cmPadicWeierstrass p) := by
  refine WeierstrassCurve.isIntegral_of_exists_lift
    (R := ℤ_[p]) (K := ℚ_[p]) ?_ ?_ ?_ ?_ ?_
  · exact ⟨0, by simp [cmPadicWeierstrass, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmPadicWeierstrass, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmPadicWeierstrass, cmWeierstrass]⟩
  · exact ⟨-1, by simp [cmPadicWeierstrass, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmPadicWeierstrass, cmWeierstrass]⟩

theorem oddPrime_coprime_sixtyFour
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) :
    p.Coprime 64 := by
  apply hp.out.coprime_iff_not_dvd.mpr
  intro hdiv
  have hp_dvd_two : p ∣ 2 := by
    have hpow : p ∣ 2 ^ 6 := by
      norm_num at hdiv ⊢
      exact hdiv
    exact hp.out.dvd_of_dvd_pow hpow
  have hp_eq_two : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp1 | hp2'
    · exact (hp.out.ne_one hp1).elim
    · exact hp2'
  exact hp2 hp_eq_two

theorem sixtyFour_isUnit_padicInt
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    IsUnit (64 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff,
    PadicInt.norm_natCast_eq_one_iff]
  exact oddPrime_coprime_sixtyFour hp2

theorem cmPadicWeierstrass_discriminant_valuation_eq_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    valuation ℚ_[p] (maximalIdeal ℤ_[p])
      (cmPadicWeierstrass p).Δ = 1 := by
  rw [cmPadicWeierstrass_discriminant]
  change valuation ℚ_[p] (maximalIdeal ℤ_[p])
    (algebraMap ℤ_[p] ℚ_[p] (64 : ℤ_[p])) = 1
  rw [valuation_eq_one_iff_notMem]
  simpa [IsDiscreteValuationRing.maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    using sixtyFour_isUnit_padicInt hp2

instance cmPadicWeierstrass_isMinimal
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.IsMinimal ℤ_[p]
      (cmPadicWeierstrass p) where
  val_Δ_maximal := by
    constructor
    · simpa using
        (inferInstance :
          WeierstrassCurve.IsIntegral ℤ_[p]
            (cmPadicWeierstrass p))
    · intro C hC hle
      have hcurCoe :
          ((WeierstrassCurve.valuation_Δ_aux ℤ_[p]
            ((1 : WeierstrassCurve.VariableChange ℚ_[p]) •
              cmPadicWeierstrass p) :
            {v : ℤᵐ⁰ // v ≤ 1}) : ℤᵐ⁰) = 1 := by
        simp only [one_smul]
        rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
        exact cmPadicWeierstrass_discriminant_valuation_eq_one hp2
      have hcur :
          WeierstrassCurve.valuation_Δ_aux ℤ_[p]
            ((1 : WeierstrassCurve.VariableChange ℚ_[p]) •
              cmPadicWeierstrass p)
            =
          (⟨1, le_rfl⟩ : {v : ℤᵐ⁰ // v ≤ 1}) := by
        apply Subtype.ext
        exact hcurCoe
      rw [hcur]
      exact
        (WeierstrassCurve.valuation_Δ_aux ℤ_[p]
          (C • cmPadicWeierstrass p)).property

instance cmPadicWeierstrass_hasGoodReduction
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.HasGoodReduction ℤ_[p]
      (cmPadicWeierstrass p) where
  toIsMinimal := cmPadicWeierstrass_isMinimal hp2
  goodReduction :=
    cmPadicWeierstrass_discriminant_valuation_eq_one hp2

end Synthesis.Millennium.BSD
