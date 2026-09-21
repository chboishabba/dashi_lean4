import Synthesis.MillenniumBSDEtaCoefficientFiveWeld
import Synthesis.MillenniumBSDEtaEllipticOneModFourReduction
import Mathlib.Tactic

/-!
# All coefficient checks through the level-32 weight-2 Sturm bound

The live eta/elliptic coefficient seam is supported only on n ≡ 1 mod 4.
Below the classical Sturm bound 8, the only positive surviving indices are
1 and 5.  Both have already been proved equal literally.

This file packages exactly the finite calculation a specialized
Gamma_0(32), weight-2 Sturm theorem would consume.  No general modular-form
infrastructure is introduced.
-/

namespace Synthesis.Millennium.BSD

theorem etaElliptic_agree_one_to_eight
    (n : ℕ) (hn1 : 1 ≤ n) (hn8 : n ≤ 8) :
    cmEta32TaylorCoeff n = cmEllipticCoefficientComplex n := by
  interval_cases n <;>
    first
    | exact etaElliptic_agree_at_one
    | exact etaElliptic_agree_at_five
    | {
        have hmod : n % 4 ≠ 1 := by omega
        rw [cmEta32TaylorCoeff_eq_zero_of_mod_four_ne_one hmod,
          cmAllNCoefficient_eq_zero_unless_one_mod_four (by omega) hmod]
        simp [cmEllipticCoefficientComplex]
      }

/--
The exact external theorem still needed on the analytic same-object route.
For the two specific weight-2 level-32 cusp forms, equality through q^8
implies equality of all positive Fourier coefficients.
-/
def Level32Weight2SturmPrinciple : Prop :=
  (∀ n : ℕ, 1 ≤ n → n ≤ 8 →
      cmEta32TaylorCoeff n = cmEllipticCoefficientComplex n) →
    EtaEllipticPositiveCoefficientAgreement

theorem etaElliptic_positiveAgreement_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple) :
    EtaEllipticPositiveCoefficientAgreement := by
  exact sturm etaElliptic_agree_one_to_eight

theorem etaElliptic_fourMPlusOneAgreement_of_level32Sturm
    (sturm : Level32Weight2SturmPrinciple) :
    EtaEllipticFourMPlusOneAgreement := by
  exact etaElliptic_positive_iff_fourMPlusOne.mp
    (etaElliptic_positiveAgreement_of_level32Sturm sturm)

end Synthesis.Millennium.BSD
