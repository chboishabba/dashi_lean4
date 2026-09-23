import Synthesis.MillenniumBSDCMSplitJacobiPrimaryCube
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Split-prime sign: separate Gaussian uniqueness from elementary primary parity

After the paid Jacobi cube congruence, the Jacobi sum has coordinates `a,b`
with

  a²+b²=p,  a odd,  b even,  a+b ≡ -1 (mod 4).

For a supplied prime representation

  p=(2r+1)²+(2s)²,

the only genuinely Gaussian/UFD statement still needed is that the odd/even
coordinates agree in *absolute value* with `2r+1,2s`.

Once that is known, the primary congruence determines the sign of `a`
elementarily:

  a = -(-1)^(r+s) (2r+1).

This file proves that second step and exposes absolute-coordinate uniqueness as
the sole residual owner.
-/

namespace Synthesis.Millennium.BSD

/-- Exact Gaussian/UFD residual: uniqueness of the absolute odd/even
coordinates of a prime sum-of-two-squares representation. -/
def SplitPrimeAbsoluteCoordinateUniqueness : Prop :=
  ∀ (p r s : ℕ), p.Prime →
    p = (2 * r + 1) ^ 2 + 4 * s ^ 2 →
    ∀ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) →
      Odd a →
      Even b →
      (a = 2 * (r : ℤ) + 1 ∨ a = -(2 * (r : ℤ) + 1)) ∧
      (b = 2 * (s : ℤ) ∨ b = -(2 * (s : ℤ)))

private theorem primary_congruence_selects_real_sign
    {r s : ℕ} {a b : ℤ}
    (ha : a = 2 * (r : ℤ) + 1 ∨ a = -(2 * (r : ℤ) + 1))
    (hb : b = 2 * (s : ℤ) ∨ b = -(2 * (s : ℤ)))
    (hprimary : Int.ModEq 4 (a + b) (-1)) :
    a = -((-1 : ℤ) ^ (r + s)) * (2 * (r : ℤ) + 1) := by
  rcases Nat.even_or_odd (r + s) with hev | hod
  · have hp : ((-1 : ℤ) ^ (r + s)) = 1 := hev.neg_one_pow
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exfalso
        rcases (Int.modEq_iff_add_fac.mp hprimary) with ⟨t, ht⟩
        rcases hev with ⟨k, hk⟩
        omega
      · exfalso
        rcases (Int.modEq_iff_add_fac.mp hprimary) with ⟨t, ht⟩
        rcases hev with ⟨k, hk⟩
        omega
    · simpa [hp] using ha
  · have hp : ((-1 : ℤ) ^ (r + s)) = -1 := hod.neg_one_pow
    rcases ha with ha | ha
    · simpa [hp] using ha
    · rcases hb with hb | hb
      · exfalso
        rcases (Int.modEq_iff_add_fac.mp hprimary) with ⟨t, ht⟩
        rcases hod with ⟨k, hk⟩
        omega
      · exfalso
        rcases (Int.modEq_iff_add_fac.mp hprimary) with ⟨t, ht⟩
        rcases hod with ⟨k, hk⟩
        omega

/-- Absolute-coordinate uniqueness plus the already-paid primary mod-4
condition gives the complete split-prime sign compiler. -/
theorem splitPrimeRepresentationSignCompiler_of_absoluteUniqueness
    (huniq : SplitPrimeAbsoluteCoordinateUniqueness) :
    SplitPrimeRepresentationSignCompiler := by
  intro p r s hp hrep a b hnorm haodd hbeven hprimary
  rcases huniq p r s hp hrep a b hnorm haodd hbeven with ⟨ha,hb⟩
  have hsign :=
    primary_congruence_selects_real_sign ha hb hprimary
  rw [hsign]
  push_cast
  ring

/-- Prize-facing split trace now needs only the absolute-coordinate uniqueness
lemma; the Jacobi cube congruence itself is already paid. -/
theorem split_frobenius_signed_of_absoluteUniqueness
    (huniq : SplitPrimeAbsoluteCoordinateUniqueness)
    {p r s : ℕ} (hp : p.Prime)
    (hrep : p = (2 * r + 1) ^ 2 + 4 * s ^ 2)
    (hmod : p % 4 = 1) :
    frobeniusCoefficient p =
      2 * ((-1 : ℤ) ^ (r + s)) * (2 * r + 1) := by
  exact split_frobenius_signed_of_primary_and_representation
    splitJacobiPrimaryCubeCongruence_paid
    (splitPrimeRepresentationSignCompiler_of_absoluteUniqueness huniq)
    hp hrep hmod

/-- Machine-readable residual after the specialized Jacobi cube proof. -/
structure SplitPrimeSignBoundaryStatus where
  jacobiCubeCongruencePaid : Bool
  gaussianNormAndParityPaid : Bool
  primarySignSelectionPaid : Bool
  absoluteCoordinateUniquenessPaid : Bool
  deriving DecidableEq, Repr

def splitPrimeSignBoundaryStatus : SplitPrimeSignBoundaryStatus :=
  ⟨true, true, true, false⟩

end Synthesis.Millennium.BSD
