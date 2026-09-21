import Synthesis.MillenniumBSDEtaCoefficientFiveWeld
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Specialized Jacobi route for the eta32 / elliptic same-object seam

We avoid building general level-32 Sturm theory.  The classical Jacobi
factorization needed for this one eta product is

  eta(8z)^3
    = sum_{r>=0} (-1)^r (2r+1) q^((2r+1)^2),

and

  eta(4z)^2 / eta(8z)
    = 1 + 2 sum_{s>=1} (-1)^s q^(4s^2).

At the formal-product level it is enough to prove exactly the two identities
`cmJacobiOddProductIdentity` and `cmJacobiEvenProductIdentity` below.  Their
product is definitionally the already-welded eta32 formal series.  Therefore
they give an explicit finite coefficient formula for the *actual canonical*
Taylor coefficients, with no Gamma_0(32) dimension/Sturm infrastructure.
-/

namespace Synthesis.Millennium.BSD

open PowerSeries

/-- Coefficients of the odd-square Jacobi theta derivative factor. -/
noncomputable def cmJacobiOddCoeff (N : ℕ) : ℂ :=
  ∑ r in Finset.range (N + 1),
    if (2 * r + 1) ^ 2 = N then
      ((-1 : ℂ) ^ r) * (2 * r + 1)
    else 0

/-- Coefficients of the even-square theta factor. -/
noncomputable def cmJacobiEvenCoeff (N : ℕ) : ℂ :=
  (if N = 0 then 1 else 0) +
    ∑ s in Finset.range (N + 1),
      if 0 < s ∧ 4 * s ^ 2 = N then
        2 * ((-1 : ℂ) ^ s)
      else 0

noncomputable def cmJacobiOddSeries : PowerSeries ℂ :=
  PowerSeries.mk cmJacobiOddCoeff

noncomputable def cmJacobiEvenSeries : PowerSeries ℂ :=
  PowerSeries.mk cmJacobiEvenCoeff

@[simp] theorem cmJacobiOddSeries_coeff (N : ℕ) :
    cmJacobiOddSeries.coeff N = cmJacobiOddCoeff N := by
  simp [cmJacobiOddSeries]

@[simp] theorem cmJacobiEvenSeries_coeff (N : ℕ) :
    cmJacobiEvenSeries.coeff N = cmJacobiEvenCoeff N := by
  simp [cmJacobiEvenSeries]

/-- The first specialized Jacobi product identity still to discharge. -/
def cmJacobiOddProductIdentity : Prop :=
  cmJacobiOddSeries =
    X * (cmEtaEulerFormal.subst (X ^ 8)) ^ 3

/--
The second specialized Jacobi identity, written without division so no formal
inverse API is needed.
-/
def cmJacobiEvenProductIdentity : Prop :=
  cmJacobiEvenSeries * (cmEtaEulerFormal.subst (X ^ 8)) =
    (cmEtaEulerFormal.subst (X ^ 4)) ^ 2

/--
The two Jacobi identities multiply to exactly the eta32 formal product already
welded to `cmEta32QProduct`.
-/
theorem cmEta32FormalSeries_eq_jacobiProduct
    (hOdd : cmJacobiOddProductIdentity)
    (hEven : cmJacobiEvenProductIdentity) :
    cmEta32FormalSeries = cmJacobiOddSeries * cmJacobiEvenSeries := by
  unfold cmJacobiOddProductIdentity at hOdd
  unfold cmJacobiEvenProductIdentity at hEven
  rw [hOdd]
  unfold cmEta32FormalSeries
  calc
    X * (cmEtaEulerFormal.subst (X ^ 4)) ^ 2 *
          (cmEtaEulerFormal.subst (X ^ 8)) ^ 2
        = X *
            (cmJacobiEvenSeries *
              (cmEtaEulerFormal.subst (X ^ 8))) *
            (cmEtaEulerFormal.subst (X ^ 8)) ^ 2 := by
              rw [hEven]
    _ =
        (X * (cmEtaEulerFormal.subst (X ^ 8)) ^ 3) *
          cmJacobiEvenSeries := by ring

/-- The theta product coefficient is an explicit finite antidiagonal sum. -/
theorem cmJacobiProduct_coeff (N : ℕ) :
    (cmJacobiOddSeries * cmJacobiEvenSeries).coeff N =
      ∑ ij in Finset.Nat.antidiagonal N,
        cmJacobiOddCoeff ij.1 * cmJacobiEvenCoeff ij.2 := by
  simp [PowerSeries.coeff_mul]

/--
Prize-facing analytic reduction: the two specialized Jacobi identities give
the actual eta Taylor coefficient as a finite odd-square/even-square
representation convolution.
-/
theorem cmEta32TaylorCoeff_eq_jacobiRepresentationSum
    (hOdd : cmJacobiOddProductIdentity)
    (hEven : cmJacobiEvenProductIdentity)
    (N : ℕ) :
    cmEta32TaylorCoeff N =
      ∑ ij in Finset.Nat.antidiagonal N,
        cmJacobiOddCoeff ij.1 * cmJacobiEvenCoeff ij.2 := by
  rw [← cmEta32_formal_coeff_eq_TaylorCoeff N,
    cmEta32FormalSeries_eq_jacobiProduct hOdd hEven,
    cmJacobiProduct_coeff]

/--
After the two Jacobi identities, the eta/elliptic seam is purely the finite
arithmetic statement that this representation sum equals the already-defined
elliptic coefficient.
-/
def JacobiRepresentationMatchesElliptic : Prop :=
  ∀ N : ℕ, 0 < N →
    (∑ ij in Finset.Nat.antidiagonal N,
      cmJacobiOddCoeff ij.1 * cmJacobiEvenCoeff ij.2)
      = cmEllipticCoefficientComplex N

theorem etaEllipticPositiveAgreement_of_jacobi
    (hOdd : cmJacobiOddProductIdentity)
    (hEven : cmJacobiEvenProductIdentity)
    (hArithmetic : JacobiRepresentationMatchesElliptic) :
    EtaEllipticPositiveCoefficientAgreement := by
  intro N hN
  rw [cmEta32TaylorCoeff_eq_jacobiRepresentationSum hOdd hEven N]
  exact hArithmetic N hN

end Synthesis.Millennium.BSD
