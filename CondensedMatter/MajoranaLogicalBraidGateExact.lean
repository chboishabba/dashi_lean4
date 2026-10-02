import Mathlib
import CondensedMatter.MajoranaOperatorKernelExact
import CondensedMatter.MajoranaParityQubitExact

namespace CondensedMatter

/-!
Exact logical braid matrices on the four-Majorana even-parity qubit.

In the logical basis |0_L>=|00>, |1_L>=|11>, use the unnormalized matrices

  B1~ = [[1+i, 0], [0, 1-i]]
  B2~ = [[1, i], [i, 1]]
  B3~ = B1~

Each is sqrt(2) times the corresponding unitary Ising/Majorana braid gate.
Keeping the common normalization out makes the kernel proof purely Gaussian-
integer algebra.  We prove:
* B_i† B_i = 2 I;
* B1 B2 B1 = B2 B1 B2;
* B2 B3 B2 = B3 B2 B3;
* B1 B3 = B3 B1;
* B1 B2 != B2 B1.

This closes the mathematical code-space braid-gate seam.  It does not assert
that YbSb2 physically realizes these gates.
-/

open CMatrix2

def logicalB1 : CMatrix2 :=
  ⟨1 + Complex.I, 0, 0, 1 - Complex.I⟩

def logicalB2 : CMatrix2 :=
  ⟨1, Complex.I, Complex.I, 1⟩

def logicalB3 : CMatrix2 :=
  logicalB1

theorem logicalB1_norm :
    mul (dagger logicalB1) logicalB1 = twoIdentity := by
  apply CMatrix2.ext <;>
    simp [logicalB1, dagger, mul, twoIdentity, smul, one,
      Complex.I_mul_I]
  <;> ring

theorem logicalB2_norm :
    mul (dagger logicalB2) logicalB2 = twoIdentity := by
  apply CMatrix2.ext <;>
    simp [logicalB2, dagger, mul, twoIdentity, smul, one,
      Complex.I_mul_I]
  <;> ring

theorem logicalB3_norm :
    mul (dagger logicalB3) logicalB3 = twoIdentity := by
  simpa [logicalB3] using logicalB1_norm

theorem logical_yangBaxter12 :
    mul (mul logicalB1 logicalB2) logicalB1
      =
    mul (mul logicalB2 logicalB1) logicalB2 := by
  apply CMatrix2.ext <;>
    simp [logicalB1, logicalB2, mul, Complex.I_mul_I]
  <;> ring

theorem logical_yangBaxter23 :
    mul (mul logicalB2 logicalB3) logicalB2
      =
    mul (mul logicalB3 logicalB2) logicalB3 := by
  simpa [logicalB3] using logical_yangBaxter12.symm

theorem logical_farCommutation13 :
    mul logicalB1 logicalB3 = mul logicalB3 logicalB1 := by
  rfl

theorem logical_adjacent_noncommuting :
    mul logicalB1 logicalB2 ≠ mul logicalB2 logicalB1 := by
  intro h
  have h12 := congrArg CMatrix2.a12 h
  simp [logicalB1, logicalB2, mul, Complex.I_mul_I] at h12

/--
The logical code space is the full two-component amplitude carrier over the
already-proved even-parity basis.  Hence every 2x2 logical braid matrix acts
internally on that code space.
-/
structure LogicalAmplitude where
  ampZero : ℂ
  ampOne : ℂ
  deriving Repr

def applyLogicalMatrix (M : CMatrix2) (v : LogicalAmplitude) :
    LogicalAmplitude :=
  ⟨M.a11 * v.ampZero + M.a12 * v.ampOne,
   M.a21 * v.ampZero + M.a22 * v.ampOne⟩

def applyLogicalB1 : LogicalAmplitude → LogicalAmplitude :=
  applyLogicalMatrix logicalB1

def applyLogicalB2 : LogicalAmplitude → LogicalAmplitude :=
  applyLogicalMatrix logicalB2

def applyLogicalB3 : LogicalAmplitude → LogicalAmplitude :=
  applyLogicalMatrix logicalB3

/-- Mathematical gate package consumed by the YbSb2 promotion bridge. -/
structure ExactMajoranaLogicalBraidGates where
  B1 : CMatrix2
  B2 : CMatrix2
  B3 : CMatrix2
  yb12 : mul (mul B1 B2) B1 = mul (mul B2 B1) B2
  yb23 : mul (mul B2 B3) B2 = mul (mul B3 B2) B3
  far13 : mul B1 B3 = mul B3 B1
  adjacentNoncommuting : mul B1 B2 ≠ mul B2 B1
  norm1 : mul (dagger B1) B1 = twoIdentity
  norm2 : mul (dagger B2) B2 = twoIdentity
  norm3 : mul (dagger B3) B3 = twoIdentity

def canonicalExactMajoranaLogicalBraidGates :
    ExactMajoranaLogicalBraidGates where
  B1 := logicalB1
  B2 := logicalB2
  B3 := logicalB3
  yb12 := logical_yangBaxter12
  yb23 := logical_yangBaxter23
  far13 := logical_farCommutation13
  adjacentNoncommuting := logical_adjacent_noncommuting
  norm1 := logicalB1_norm
  norm2 := logicalB2_norm
  norm3 := logicalB3_norm

end CondensedMatter
