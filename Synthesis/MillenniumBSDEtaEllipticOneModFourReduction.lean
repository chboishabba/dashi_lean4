import Synthesis.MillenniumBSDCMEta32TaylorSupport
import Synthesis.MillenniumBSDCMGlobalLacunarityModFour
import Mathlib.Tactic

/-!
# Reduce eta/elliptic coefficient equality to the 1 mod 4 subsequence

Both literal coefficient families are already known to vanish away from
`n ≡ 1 (mod 4)`.  This file packages the exact remaining same-object seam:
equality on that residue class is equivalent to equality of the full positive
coefficient sequences.
-/

namespace Synthesis.Millennium.BSD

noncomputable def cmEllipticCoefficientComplex (n : ℕ) : ℂ :=
  (cmAllNCoefficient n : ℂ)

def EtaEllipticOneModFourAgreement : Prop :=
  ∀ n : ℕ, n % 4 = 1 →
    cmEta32TaylorCoeff n = cmEllipticCoefficientComplex n

def EtaEllipticPositiveCoefficientAgreement : Prop :=
  ∀ n : ℕ, 0 < n →
    cmEta32TaylorCoeff n = cmEllipticCoefficientComplex n

theorem etaEllipticPositiveAgreement_of_oneModFour
    (h : EtaEllipticOneModFourAgreement) :
    EtaEllipticPositiveCoefficientAgreement := by
  intro n hn
  by_cases hmod : n % 4 = 1
  · exact h n hmod
  · have heta : cmEta32TaylorCoeff n = 0 :=
      cmEta32TaylorCoeff_eq_zero_of_mod_four_ne_one hmod
    have hell : cmAllNCoefficient n = 0 :=
      cmAllNCoefficient_eq_zero_unless_one_mod_four hn hmod
    rw [heta]
    simp [cmEllipticCoefficientComplex, hell]

theorem etaEllipticOneModFourAgreement_of_positive
    (h : EtaEllipticPositiveCoefficientAgreement) :
    EtaEllipticOneModFourAgreement := by
  intro n hmod
  have hn : 0 < n := by omega
  exact h n hn

theorem etaElliptic_positive_iff_oneModFour :
    EtaEllipticPositiveCoefficientAgreement ↔
      EtaEllipticOneModFourAgreement := by
  constructor
  · exact etaEllipticOneModFourAgreement_of_positive
  · exact etaEllipticPositiveAgreement_of_oneModFour

/-- Equivalent parameterization of the live seam by coefficients `4m+1`. -/
def EtaEllipticFourMPlusOneAgreement : Prop :=
  ∀ m : ℕ,
    cmEta32TaylorCoeff (4 * m + 1) =
      cmEllipticCoefficientComplex (4 * m + 1)

theorem oneModFourAgreement_of_fourMPlusOne
    (h : EtaEllipticFourMPlusOneAgreement) :
    EtaEllipticOneModFourAgreement := by
  intro n hmod
  have hn : n = 4 * (n / 4) + 1 := by omega
  subst n
  exact h (n / 4)

theorem fourMPlusOneAgreement_of_oneModFour
    (h : EtaEllipticOneModFourAgreement) :
    EtaEllipticFourMPlusOneAgreement := by
  intro m
  apply h
  omega

theorem etaElliptic_positive_iff_fourMPlusOne :
    EtaEllipticPositiveCoefficientAgreement ↔
      EtaEllipticFourMPlusOneAgreement := by
  rw [etaElliptic_positive_iff_oneModFour]
  constructor
  · exact fourMPlusOneAgreement_of_oneModFour
  · exact oneModFourAgreement_of_fourMPlusOne

end Synthesis.Millennium.BSD
