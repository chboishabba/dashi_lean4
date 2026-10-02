import Mathlib

namespace CondensedMatter

/-!
Concrete 2x2 complex Majorana operator kernel.

DASHI DERIVATION:
* gamma1 = sigma_x and gamma2 = sigma_y are self-adjoint;
* gamma_i^2 = 1;
* gamma1 gamma2 + gamma2 gamma1 = 0;
* f = (gamma1 + i gamma2)/2 is the exact one-fermion ladder operator;
* n = f† f is a projector, n^2 = n.

This is a mathematical operator realization.  It is not a claim that a
specific YbSb2 surface mode has been experimentally isolated or manipulated.
-/

structure CMatrix2 where
  a11 : ℂ
  a12 : ℂ
  a21 : ℂ
  a22 : ℂ
  deriving Repr

namespace CMatrix2

@[ext]
theorem ext {A B : CMatrix2}
    (h11 : A.a11 = B.a11)
    (h12 : A.a12 = B.a12)
    (h21 : A.a21 = B.a21)
    (h22 : A.a22 = B.a22) :
    A = B := by
  cases A
  cases B
  simp_all

def zero : CMatrix2 := ⟨0, 0, 0, 0⟩
def one : CMatrix2 := ⟨1, 0, 0, 1⟩

def add (A B : CMatrix2) : CMatrix2 :=
  ⟨A.a11 + B.a11, A.a12 + B.a12,
   A.a21 + B.a21, A.a22 + B.a22⟩

def neg (A : CMatrix2) : CMatrix2 :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

def mul (A B : CMatrix2) : CMatrix2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

def smul (z : ℂ) (A : CMatrix2) : CMatrix2 :=
  ⟨z * A.a11, z * A.a12, z * A.a21, z * A.a22⟩

def dagger (A : CMatrix2) : CMatrix2 :=
  ⟨starRingEnd ℂ A.a11, starRingEnd ℂ A.a21,
   starRingEnd ℂ A.a12, starRingEnd ℂ A.a22⟩

end CMatrix2

open CMatrix2

def gamma1 : CMatrix2 := ⟨0, 1, 1, 0⟩

def gamma2 : CMatrix2 := ⟨0, -Complex.I, Complex.I, 0⟩

theorem gamma1_selfAdjoint :
    dagger gamma1 = gamma1 := by
  apply CMatrix2.ext <;> simp [dagger, gamma1]

theorem gamma2_selfAdjoint :
    dagger gamma2 = gamma2 := by
  apply CMatrix2.ext <;> simp [dagger, gamma2]

theorem gamma1_square :
    mul gamma1 gamma1 = one := by
  apply CMatrix2.ext <;> simp [mul, gamma1, one]

theorem gamma2_square :
    mul gamma2 gamma2 = one := by
  apply CMatrix2.ext <;> simp [mul, gamma2, one, Complex.I_mul_I]

theorem gamma12_anticommute :
    add (mul gamma1 gamma2) (mul gamma2 gamma1) = zero := by
  apply CMatrix2.ext <;>
    simp [add, mul, gamma1, gamma2, zero, Complex.I_mul_I]

/-- f = (gamma1 + i gamma2)/2. -/
def fermionF : CMatrix2 :=
  smul ((2 : ℂ)⁻¹) (add gamma1 (smul Complex.I gamma2))

def fermionFDagger : CMatrix2 :=
  dagger fermionF

def fermionNumber : CMatrix2 :=
  mul fermionFDagger fermionF

def ladderTarget : CMatrix2 :=
  ⟨0, 1, 0, 0⟩

def ladderDaggerTarget : CMatrix2 :=
  ⟨0, 0, 1, 0⟩

def occupiedProjector : CMatrix2 :=
  ⟨0, 0, 0, 1⟩

theorem fermionF_exact :
    fermionF = ladderTarget := by
  apply CMatrix2.ext <;>
    simp [fermionF, ladderTarget, smul, add, gamma1, gamma2,
      Complex.I_mul_I]
  <;> norm_num

theorem fermionFDagger_exact :
    fermionFDagger = ladderDaggerTarget := by
  rw [fermionFDagger, fermionF_exact]
  apply CMatrix2.ext <;>
    simp [dagger, ladderTarget, ladderDaggerTarget]

theorem fermionNumber_exact :
    fermionNumber = occupiedProjector := by
  rw [fermionNumber, fermionFDagger_exact, fermionF_exact]
  apply CMatrix2.ext <;>
    simp [mul, ladderTarget, ladderDaggerTarget, occupiedProjector]

theorem fermionNumber_projector :
    mul fermionNumber fermionNumber = fermionNumber := by
  rw [fermionNumber_exact]
  apply CMatrix2.ext <;>
    simp [mul, occupiedProjector]

/-- Canonical CAR identity {f,f†}=1 in the concrete kernel. -/
theorem fermion_CAR :
    add (mul fermionF fermionFDagger)
        (mul fermionFDagger fermionF)
      = one := by
  rw [fermionF_exact, fermionFDagger_exact]
  apply CMatrix2.ext <;>
    simp [add, mul, ladderTarget, ladderDaggerTarget, one]

end CondensedMatter


/-!
Closed-form exchange operator numerator.

For A = gamma1 gamma2, A^2 = -1.  Hence the normalized exchange
U12 = (1 + A)/sqrt(2) has inverse/adjoint proportional to (1 - A).
We prove the normalization-free identities exactly; these are sufficient to
recover the conjugation action after dividing by 2.
-/

def gamma12 : CMatrix2 :=
  mul gamma1 gamma2

def braidPlus : CMatrix2 :=
  add one gamma12

def braidMinus : CMatrix2 :=
  add one (neg gamma12)

def twoIdentity : CMatrix2 :=
  smul 2 one

def twoGamma1 : CMatrix2 :=
  smul 2 gamma1

def twoGamma2 : CMatrix2 :=
  smul 2 gamma2

def minusTwoGamma1 : CMatrix2 :=
  neg twoGamma1

theorem gamma12_square_minus_one :
    mul gamma12 gamma12 = neg one := by
  apply CMatrix2.ext <;>
    simp [gamma12, mul, gamma1, gamma2, neg, one, Complex.I_mul_I]

theorem braid_normalization_exact :
    mul braidMinus braidPlus = twoIdentity := by
  apply CMatrix2.ext <;>
    simp [braidMinus, braidPlus, gamma12, add, neg, mul, smul,
      one, twoIdentity, gamma1, gamma2, Complex.I_mul_I]
  <;> norm_num

/--
Unnormalized form of U† gamma1 U = gamma2.
The left side equals 2 gamma2 before the 1/sqrt(2) factors are divided out.
-/
theorem braid_conjugates_gamma1_to_gamma2 :
    mul (mul braidMinus gamma1) braidPlus = twoGamma2 := by
  apply CMatrix2.ext <;>
    simp [braidMinus, braidPlus, gamma12, add, neg, mul, smul,
      one, twoGamma2, gamma1, gamma2, Complex.I_mul_I]
  <;> norm_num

/--
Unnormalized form of U† gamma2 U = -gamma1.
-/
theorem braid_conjugates_gamma2_to_minus_gamma1 :
    mul (mul braidMinus gamma2) braidPlus = minusTwoGamma1 := by
  apply CMatrix2.ext <;>
    simp [braidMinus, braidPlus, gamma12, add, neg, mul, smul,
      one, minusTwoGamma1, twoGamma1, gamma1, gamma2, Complex.I_mul_I]
  <;> norm_num
