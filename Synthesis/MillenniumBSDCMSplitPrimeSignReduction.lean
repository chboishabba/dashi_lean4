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

private theorem even_prime_multiple_eq_zero_of_sq_le
    {p : ℕ} (hp : p.Prime) (hpOddNat : Odd p) {x : ℤ}
    (hxEven : Even x)
    (hdvd : (p : ℤ) ∣ x)
    (hbound : x ^ 2 ≤ (p : ℤ) ^ 2) :
    x = 0 := by
  rcases hdvd with ⟨k, rfl⟩
  have hpOdd : Odd (p : ℤ) := hpOddNat.natCast
  have hkEven : Even k := by
    rw [Int.even_mul] at hxEven
    exact hxEven.resolve_left hpOdd.not_even
  rw [even_iff_exists_two_mul] at hkEven
  rcases hkEven with ⟨m, rfl⟩
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  by_contra hne
  have hmne : m ≠ 0 := by
    intro hm
    subst m
    simp at hne
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · have hmle : m ≤ -1 := by omega
    nlinarith
  · have hmge : 1 ≤ m := by omega
    nlinarith

/-- The absolute odd/even coordinates of a prime sum-of-two-squares
representation are unique.  This proof is elementary: the two norm equations
make the product

  (aB-Ab)(aB+Ab)

a multiple of p.  Primality puts p into one factor; Lagrange's identity bounds
that factor by p in absolute value; parity makes the factor even while p is
odd, so it must vanish.  Squaring then identifies both coordinates. -/
theorem splitPrimeAbsoluteCoordinateUniqueness_paid :
    SplitPrimeAbsoluteCoordinateUniqueness := by
  intro p r s hp hrep a b hnorm haodd hbeven
  let A : ℕ := 2 * r + 1
  let B : ℕ := 2 * s
  have hrepAB : p = A ^ 2 + B ^ 2 := by
    dsimp [A, B]
    nlinarith [hrep]
  have hrepZ : (p : ℤ) = (A : ℤ) ^ 2 + (B : ℤ) ^ 2 := by
    exact_mod_cast hrepAB
  have hpOddNat : Odd p := by
    rw [hrepAB]
    have hAoddNat : Odd A := by
      dsimp [A]
      exact odd_two_mul_add_one r
    have hBevenNat : Even B := by
      dsimp [B]
      exact even_two_mul s
    exact hAoddNat.pow.add_even (hBevenNat.pow_of_ne_zero (by norm_num))
  have hAodd : Odd (A : ℤ) := by
    refine ⟨(r : ℤ), ?_⟩
    dsimp [A]
    push_cast
    ring
  have hBeven : Even (B : ℤ) := by
    refine ⟨(s : ℤ), ?_⟩
    dsimp [B]
    push_cast
    ring
  let xm : ℤ := a * (B : ℤ) - (A : ℤ) * b
  let xp : ℤ := a * (B : ℤ) + (A : ℤ) * b
  have hxmEven : Even xm := by
    dsimp [xm]
    exact (hBeven.mul_left a).sub (hbeven.mul_left (A : ℤ))
  have hxpEven : Even xp := by
    dsimp [xp]
    exact (hBeven.mul_left a).add (hbeven.mul_left (A : ℤ))
  have hprod :
      xm * xp = (p : ℤ) * ((B : ℤ) ^ 2 - b ^ 2) := by
    dsimp [xm, xp]
    calc
      (a * (B : ℤ) - (A : ℤ) * b) *
            (a * (B : ℤ) + (A : ℤ) * b)
          = (B : ℤ) ^ 2 * a ^ 2 - (A : ℤ) ^ 2 * b ^ 2 := by ring
      _ = (B : ℤ) ^ 2 * (a ^ 2 + b ^ 2) -
            b ^ 2 * ((A : ℤ) ^ 2 + (B : ℤ) ^ 2) := by ring
      _ = (B : ℤ) ^ 2 * (p : ℤ) - b ^ 2 * (p : ℤ) := by
            rw [hnorm, ← hrepZ]
      _ = (p : ℤ) * ((B : ℤ) ^ 2 - b ^ 2) := by ring
  have hdvdProd : (p : ℤ) ∣ xm * xp :=
    ⟨(B : ℤ) ^ 2 - b ^ 2, hprod⟩
  have hpInt : Prime (p : ℤ) := (Nat.prime_iff_prime_int).mp hp
  have hdvd : (p : ℤ) ∣ xm ∨ (p : ℤ) ∣ xp :=
    hpInt.dvd_mul.mp hdvdProd
  have hminusIdentity :
      xm ^ 2 + (a * (A : ℤ) + b * (B : ℤ)) ^ 2 = (p : ℤ) ^ 2 := by
    dsimp [xm]
    calc
      (a * (B : ℤ) - (A : ℤ) * b) ^ 2 +
            (a * (A : ℤ) + b * (B : ℤ)) ^ 2
          = (a ^ 2 + b ^ 2) *
              ((A : ℤ) ^ 2 + (B : ℤ) ^ 2) := by ring
      _ = (p : ℤ) * (p : ℤ) := by rw [hnorm, ← hrepZ]
      _ = (p : ℤ) ^ 2 := by ring
  have hplusIdentity :
      xp ^ 2 + (a * (A : ℤ) - b * (B : ℤ)) ^ 2 = (p : ℤ) ^ 2 := by
    dsimp [xp]
    calc
      (a * (B : ℤ) + (A : ℤ) * b) ^ 2 +
            (a * (A : ℤ) - b * (B : ℤ)) ^ 2
          = (a ^ 2 + b ^ 2) *
              ((A : ℤ) ^ 2 + (B : ℤ) ^ 2) := by ring
      _ = (p : ℤ) * (p : ℤ) := by rw [hnorm, ← hrepZ]
      _ = (p : ℤ) ^ 2 := by ring
  have hxmBound : xm ^ 2 ≤ (p : ℤ) ^ 2 := by
    nlinarith [sq_nonneg (a * (A : ℤ) + b * (B : ℤ))]
  have hxpBound : xp ^ 2 ≤ (p : ℤ) ^ 2 := by
    nlinarith [sq_nonneg (a * (A : ℤ) - b * (B : ℤ))]
  have hfactor : xm = 0 ∨ xp = 0 := by
    rcases hdvd with hm | hp'
    · exact Or.inl
        (even_prime_multiple_eq_zero_of_sq_le hp hpOddNat hxmEven hm hxmBound)
    · exact Or.inr
        (even_prime_multiple_eq_zero_of_sq_le hp hpOddNat hxpEven hp' hxpBound)
  have hcrossSq :
      a ^ 2 * (B : ℤ) ^ 2 = (A : ℤ) ^ 2 * b ^ 2 := by
    rcases hfactor with hm | hp'
    · have hlin : a * (B : ℤ) = (A : ℤ) * b := sub_eq_zero.mp (by simpa [xm] using hm)
      have hs := congrArg (fun z : ℤ => z ^ 2) hlin
      simpa only [mul_pow] using hs
    · have hlin : a * (B : ℤ) = -((A : ℤ) * b) := add_eq_zero_iff_eq_neg.mp
        (by simpa [xp] using hp')
      have hs := congrArg (fun z : ℤ => z ^ 2) hlin
      simpa only [mul_pow, neg_sq] using hs
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hBsq : (B : ℤ) ^ 2 = b ^ 2 := by
    apply Int.eq_of_mul_eq_mul_left hpne
    calc
      (p : ℤ) * (B : ℤ) ^ 2
          = (a ^ 2 + b ^ 2) * (B : ℤ) ^ 2 := by rw [hnorm]
      _ = a ^ 2 * (B : ℤ) ^ 2 + b ^ 2 * (B : ℤ) ^ 2 := by ring
      _ = (A : ℤ) ^ 2 * b ^ 2 + b ^ 2 * (B : ℤ) ^ 2 := by rw [hcrossSq]
      _ = ((A : ℤ) ^ 2 + (B : ℤ) ^ 2) * b ^ 2 := by ring
      _ = (p : ℤ) * b ^ 2 := by rw [← hrepZ]
  have hAsq : a ^ 2 = (A : ℤ) ^ 2 := by
    nlinarith [hnorm, hrepZ, hBsq]
  have ha :
      a = (A : ℤ) ∨ a = -(A : ℤ) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hAsq
  have hb :
      b = (B : ℤ) ∨ b = -(B : ℤ) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hBsq.symm
  simpa [A, B] using And.intro ha hb

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
  ⟨true, true, true, true⟩

end Synthesis.Millennium.BSD
