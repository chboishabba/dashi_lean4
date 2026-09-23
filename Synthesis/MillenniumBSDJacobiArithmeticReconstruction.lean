import Synthesis.MillenniumBSDJacobiEta32Reduction
import Synthesis.MillenniumBSDGlobalCoefficientReconstruction
import Synthesis.MillenniumBSDCMSplitPrimeSignReduction
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# CM Jacobi coefficient local-to-global reconstruction

The q-series seam should not ask for arbitrary coefficient equality as an
opaque theorem.  The Jacobi convolution is itself a global arithmetic
coefficient system.  Equality with the elliptic L-function follows once that
system has the same compatible local data:

* coprime multiplicativity;
* the same odd-prime coefficient;
* the same good-prime second-order recurrence;
* the same additive p=2 prime-power coefficients.

Unique factorization then reconstructs every global coefficient.

This file pays the reconstruction compiler.  The remaining CM-theta
mathematics is precisely to prove those local/compatibility properties for the
explicit Jacobi convolution.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction PowerSeries

/-- The finite Jacobi convolution already produced by the two q-product
factors, packaged as a named coefficient function. -/
noncomputable def cmJacobiArithmeticCoefficient (N : ℕ) : ℂ :=
  ∑ ij in Finset.Nat.antidiagonal N,
    cmJacobiOddCoeff ij.1 * cmJacobiEvenCoeff ij.2

@[simp] theorem cmJacobiArithmeticCoefficient_zero :
    cmJacobiArithmeticCoefficient 0 = 0 := by
  simp [cmJacobiArithmeticCoefficient, cmJacobiOddCoeff, cmJacobiEvenCoeff]

theorem cmJacobiArithmeticCoefficient_eq_productCoeff (N : ℕ) :
    cmJacobiArithmeticCoefficient N =
      (cmJacobiOddSeries * cmJacobiEvenSeries).coeff N := by
  rw [cmJacobiProduct_coeff]
  rfl

/-- The Jacobi theta coefficient sequence as an arithmetic function. -/
noncomputable def cmJacobiArithmeticFunction : ArithmeticFunction ℂ where
  toFun := cmJacobiArithmeticCoefficient
  map_zero' := cmJacobiArithmeticCoefficient_zero

@[simp] theorem cmJacobiArithmeticFunction_apply (N : ℕ) :
    cmJacobiArithmeticFunction N = cmJacobiArithmeticCoefficient N := rfl

/-- The already-constructed elliptic coefficients, viewed on the same complex
arithmetic-function carrier. -/
noncomputable def cmEllipticComplexArithmeticFunction : ArithmeticFunction ℂ where
  toFun := cmEllipticCoefficientComplex
  map_zero' := by
    simp [cmEllipticCoefficientComplex, cmAllNCoefficient_zero]

@[simp] theorem cmEllipticComplexArithmeticFunction_apply (N : ℕ) :
    cmEllipticComplexArithmeticFunction N = cmEllipticCoefficientComplex N := rfl

theorem cmEllipticComplexArithmeticFunction_isMultiplicative :
    cmEllipticComplexArithmeticFunction.IsMultiplicative := by
  constructor
  · simp [cmEllipticComplexArithmeticFunction, cmEllipticCoefficientComplex,
      cmAllNCoefficient_one]
  · intro m n hmn
    simp only [cmEllipticComplexArithmeticFunction_apply,
      cmEllipticCoefficientComplex]
    rw [cmAllNCoefficient_coprime_mul hmn]
    push_cast
    rfl

/-- J3a: the CM/Jacobi coefficient system glues coprime local pieces
multiplicatively. -/
def JacobiArithmeticMultiplicativity : Prop :=
  cmJacobiArithmeticFunction.IsMultiplicative

/-- J3b: at each odd prime, the first Jacobi local coefficient is the actual
elliptic Frobenius coefficient.  The split-prime sign theorem and inert-prime
vanishing are the already-paid data expected to discharge this producer. -/
def JacobiOddPrimeAgreement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 →
    cmJacobiArithmeticFunction p =
      ((@frobeniusCoefficient p ⟨hp⟩ : ℤ) : ℂ)

/-- J3c: the Jacobi prime-power coefficients obey the same degree-two Euler
recurrence as the elliptic coefficients at every odd prime. -/
def JacobiOddPrimePowerRecurrence : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → ∀ k : ℕ,
    cmJacobiArithmeticFunction (p ^ (k + 2)) =
      ((@frobeniusCoefficient p ⟨hp⟩ : ℤ) : ℂ) *
          cmJacobiArithmeticFunction (p ^ (k + 1))
        - (p : ℂ) * cmJacobiArithmeticFunction (p ^ k)

theorem cmJacobiOddCoeff_eq_zero_of_even
    {N : ℕ} (hN : Even N) :
    cmJacobiOddCoeff N = 0 := by
  unfold cmJacobiOddCoeff
  apply Finset.sum_eq_zero
  intro r hr
  split_ifs with hsq
  · have hodd : Odd ((2 * r + 1) ^ 2) :=
      (odd_two_mul_add_one r).pow
    have : Odd N := by simpa [hsq] using hodd
    exact (this.not_even hN).elim
  · rfl

theorem cmJacobiEvenCoeff_eq_zero_of_odd
    {N : ℕ} (hN : Odd N) :
    cmJacobiEvenCoeff N = 0 := by
  unfold cmJacobiEvenCoeff
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    simpa using hN
  rw [if_neg hN0, zero_add]
  apply Finset.sum_eq_zero
  intro s hs
  split_ifs with hterm
  · rcases hterm with ⟨hspos, hsq⟩
    have heven : Even (4 * s ^ 2) := by
      exact ⟨2 * s ^ 2, by ring⟩
    have : Even N := by simpa [hsq] using heven
    exact (hN.not_even this).elim
  · rfl

theorem cmJacobiArithmeticCoefficient_eq_zero_of_even
    {N : ℕ} (hN : Even N) :
    cmJacobiArithmeticCoefficient N = 0 := by
  unfold cmJacobiArithmeticCoefficient
  apply Finset.sum_eq_zero
  intro ij hij
  rcases ij with ⟨i,j⟩
  have hijsum : i + j = N := by
    simpa using Finset.mem_antidiagonal.mp hij
  rcases Nat.even_or_odd i with hi | hi
  · rw [cmJacobiOddCoeff_eq_zero_of_even hi, zero_mul]
  · have hj : Odd j := by
      rcases hN with ⟨n, hn⟩
      rcases hi with ⟨a, ha⟩
      refine ⟨n - a - 1, ?_⟩
      omega
    rw [cmJacobiEvenCoeff_eq_zero_of_odd hj, mul_zero]

@[simp] theorem cmJacobiArithmeticFunction_one :
    cmJacobiArithmeticFunction 1 = 1 := by
  simp [cmJacobiArithmeticFunction, cmJacobiArithmeticCoefficient,
    cmJacobiOddCoeff, cmJacobiEvenCoeff]

/-- J3d: the Jacobi system has the already-known additive local behavior at
the bad prime 2. -/
def JacobiTwoPowerAgreement : Prop :=
  ∀ k : ℕ,
    cmJacobiArithmeticFunction (2 ^ k) =
      if k = 0 then 1 else 0

theorem jacobiTwoPowerAgreement_paid :
    JacobiTwoPowerAgreement := by
  intro k
  rcases k with _ | k
  · simp
  · rw [if_neg (Nat.succ_ne_zero k)]
    have heven : Even (2 ^ (k + 1)) := by
      exact even_two.pow_of_ne_zero (by omega)
    exact cmJacobiArithmeticCoefficient_eq_zero_of_even heven

/-- The four local/compatibility owners of the CM theta arithmetic seam. -/
structure JacobiLocalReconstructionData : Prop where
  multiplicative : JacobiArithmeticMultiplicativity
  oddPrime : JacobiOddPrimeAgreement
  oddPrimePowerRecurrence : JacobiOddPrimePowerRecurrence
  twoPower : JacobiTwoPowerAgreement

/-- Local equality at every prime power follows from prime agreement plus the
shared recurrence; p=2 is dispatched separately. -/
theorem cmJacobi_primePower_eq_elliptic
    (h : JacobiLocalReconstructionData)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cmJacobiArithmeticFunction (p ^ k) =
      cmEllipticComplexArithmeticFunction (p ^ k) := by
  by_cases hp2 : p = 2
  · subst p
    rw [cmEllipticComplexArithmeticFunction_apply,
      cmEllipticCoefficientComplex, cmAllNCoefficient_twoPower]
    exact h.twoPower k
  · letI : Fact p.Prime := ⟨hp⟩
    rw [cmEllipticComplexArithmeticFunction_apply,
      cmEllipticCoefficientComplex, cmAllNCoefficient_odd_primePower hp2]
    induction k using Nat.twoStepInduction with
    | zero =>
        simpa using h.multiplicative.1
    | one =>
        simpa [explicitPrimePowerCoefficient_one] using h.oddPrime p hp hp2
    | more n h0 h1 =>
        rw [explicitPrimePowerCoefficient_recurrence]
        rw [h.oddPrimePowerRecurrence p hp hp2 n, h1, h0]
        push_cast
        rfl

/-- Unique factorization is the local-to-global reconstruction compiler:
matching every prime-power local piece of two multiplicative arithmetic
functions forces equality at every positive integer. -/
theorem cmJacobiArithmeticFunction_eq_elliptic_of_localData
    (h : JacobiLocalReconstructionData)
    {N : ℕ} (hN : 0 < N) :
    cmJacobiArithmeticFunction N =
      cmEllipticComplexArithmeticFunction N := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  rw [h.multiplicative.multiplicative_factorization
      cmJacobiArithmeticFunction hN0]
  rw [cmEllipticComplexArithmeticFunction_isMultiplicative.multiplicative_factorization
      cmEllipticComplexArithmeticFunction hN0]
  apply Finsupp.prod_congr
  intro p hpSupport
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
    (Nat.mem_primeFactors.mpr
      ⟨hN0, Nat.dvd_of_factorization_pos
        (Finsupp.mem_support_iff.mp hpSupport)⟩)
  exact cmJacobi_primePower_eq_elliptic h hpPrime (N.factorization p)

/-- The former arbitrary-N arithmetic producer is therefore compiled from the
local CM data alone. -/
theorem jacobiRepresentationMatchesElliptic_of_localData
    (h : JacobiLocalReconstructionData) :
    JacobiRepresentationMatchesElliptic := by
  intro N hN
  change cmJacobiArithmeticCoefficient N = cmEllipticCoefficientComplex N
  simpa using cmJacobiArithmeticFunction_eq_elliptic_of_localData h hN

/-- Machine-readable statement of the recut analytic arithmetic boundary. -/
structure JacobiArithmeticBoundaryStatus where
  localToGlobalCompilerPaid : Bool
  ellipticPrimeDataPaid : Bool
  ellipticPrimePowerRecurrencePaid : Bool
  jacobiMultiplicativityPaid : Bool
  jacobiOddPrimeAgreementPaid : Bool
  jacobiPrimePowerRecurrencePaid : Bool
  jacobiTwoPowerAgreementPaid : Bool
  deriving DecidableEq, Repr

def jacobiArithmeticBoundaryStatus : JacobiArithmeticBoundaryStatus :=
  ⟨true, true, true, false, false, false, true⟩

end Synthesis.Millennium.BSD
