import Synthesis.MillenniumBSDJacobiEta32Reduction
import Synthesis.MillenniumBSDGlobalCoefficientReconstruction
import Synthesis.MillenniumBSDCMSplitPrimeCanonicalWitness
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

/-- The only nontrivial prime-value owner after paying inert-prime support. -/
def JacobiSplitPrimeAgreement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1),
    cmJacobiArithmeticFunction p =
      ((@frobeniusCoefficient p ⟨hp⟩ : ℤ) : ℂ)

theorem jacobi_inertPrimeAgreement_paid
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    cmJacobiArithmeticFunction p =
      ((@frobeniusCoefficient p ⟨hp⟩ : ℤ) : ℂ) := by
  have hj : cmJacobiArithmeticFunction p = 0 := by
    exact cmJacobiArithmeticCoefficient_eq_zero_of_mod_four_ne_one (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  have he : frobeniusCoefficient p = 0 :=
    inert_frobeniusCoefficient_eq_zero hmod
  rw [hj, he]
  norm_num

theorem jacobiOddPrimeAgreement_of_split
    (hsplit : JacobiSplitPrimeAgreement) :
    JacobiOddPrimeAgreement := by
  intro p hp hp2
  rcases (Nat.odd_mod_four_iff.mp
      (hp.eq_two_or_odd.resolve_left hp2)) with h1 | h3
  · exact hsplit p hp h1
  · exact jacobi_inertPrimeAgreement_paid hp h3

theorem cmJacobiOddCoeff_ne_zero_exists_square
    {N : ℕ} (h : cmJacobiOddCoeff N ≠ 0) :
    ∃ r : ℕ, (2 * r + 1) ^ 2 = N := by
  by_contra hnone
  push_neg at hnone
  apply h
  unfold cmJacobiOddCoeff
  apply Finset.sum_eq_zero
  intro r hr
  simp [hnone r]

theorem cmJacobiEvenCoeff_ne_zero_exists_square
    {N : ℕ} (hN0 : N ≠ 0) (h : cmJacobiEvenCoeff N ≠ 0) :
    ∃ s : ℕ, 0 < s ∧ 4 * s ^ 2 = N := by
  by_contra hnone
  push_neg at hnone
  apply h
  unfold cmJacobiEvenCoeff
  rw [if_neg hN0, zero_add]
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hs0 : 0 < s
  · have hsq : 4 * s ^ 2 ≠ N := hnone s hs0
    simp [hs0, hsq]
  · simp [hs0]

theorem cmJacobiOddCoeff_canonicalSquare (r : ℕ) :
    cmJacobiOddCoeff ((2 * r + 1) ^ 2) =
      ((-1 : ℂ) ^ r) * (2 * r + 1) := by
  unfold cmJacobiOddCoeff
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' hr' hne
    have hsq : (2 * r' + 1) ^ 2 ≠ (2 * r + 1) ^ 2 := by
      intro h
      have hbase : 2 * r' + 1 = 2 * r + 1 :=
        Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h
      exact hne (by omega)
    simp [hsq]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_range]
    nlinarith [sq_nonneg (2 * r + 1 : ℤ)]

theorem cmJacobiEvenCoeff_canonicalSquare
    {s : ℕ} (hs : 0 < s) :
    cmJacobiEvenCoeff (4 * s ^ 2) =
      2 * ((-1 : ℂ) ^ s) := by
  unfold cmJacobiEvenCoeff
  have hN0 : 4 * s ^ 2 ≠ 0 := by positivity
  rw [if_neg hN0, zero_add, Finset.sum_eq_single s]
  · simp [hs]
  · intro s' hs' hne
    have hsq : 4 * s' ^ 2 ≠ 4 * s ^ 2 := by
      intro h
      have h' : s' ^ 2 = s ^ 2 := by omega
      have : s' = s :=
        Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h'
      exact hne this
    simp [hsq]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_range]
    nlinarith

theorem splitPrimeCanonicalCompanion_pos
    {p r s : ℕ} (hp : p.Prime)
    (hrep : p = (2 * r + 1) ^ 2 + 4 * s ^ 2) :
    0 < s := by
  by_contra hs
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
  apply hp.not_isSquare
  refine ⟨2 * r + 1, ?_⟩
  simpa [hs0, pow_two] using hrep

/-- At a split prime the finite Jacobi convolution has exactly one surviving
odd-square/even-square representation, namely the canonical one. -/
theorem cmJacobiArithmeticCoefficient_splitPrime
    {p r s : ℕ} (hp : p.Prime)
    (hrep : p = (2 * r + 1) ^ 2 + 4 * s ^ 2) :
    cmJacobiArithmeticCoefficient p =
      (2 : ℂ) * ((-1 : ℂ) ^ (r + s)) * (2 * r + 1) := by
  let I : ℕ := (2 * r + 1) ^ 2
  let J : ℕ := 4 * s ^ 2
  have hs : 0 < s := splitPrimeCanonicalCompanion_pos hp hrep
  have hmem : (I, J) ∈ Finset.Nat.antidiagonal p := by
    rw [Finset.mem_antidiagonal]
    simpa [I, J] using hrep.symm
  unfold cmJacobiArithmeticCoefficient
  rw [Finset.sum_eq_single_of_mem (I, J) hmem]
  · rw [cmJacobiOddCoeff_canonicalSquare r,
      cmJacobiEvenCoeff_canonicalSquare hs]
    dsimp [I, J]
    rw [pow_add]
    ring
  · rintro ⟨i,j⟩ hij hne
    simp only [Prod.fst, Prod.snd]
    by_cases hi0 : cmJacobiOddCoeff i = 0
    · simp [hi0]
    by_cases hj0 : cmJacobiEvenCoeff j = 0
    · simp [hj0]
    obtain ⟨r', hr'⟩ := cmJacobiOddCoeff_ne_zero_exists_square hi0
    have hjne : j ≠ 0 := by
      intro hj
      subst j
      have hip : i = p := by
        simpa using Finset.mem_antidiagonal.mp hij
      apply hp.not_isSquare
      refine ⟨2 * r' + 1, ?_⟩
      simpa [hip, pow_two] using hr'.symm
    obtain ⟨s', hs'pos, hs'⟩ :=
      cmJacobiEvenCoeff_ne_zero_exists_square hjne hj0
    have hsum : i + j = p := Finset.mem_antidiagonal.mp hij
    have hrep' : p = (2 * r' + 1) ^ 2 + 4 * s' ^ 2 := by
      omega
    have hrs := splitPrimeCanonicalCoordinates_unique hp hrep hrep'
    rcases hrs with ⟨rfl, rfl⟩
    apply hne
    ext <;> simp [I, J, hr', hs']

/-- The split-prime Jacobi coefficient is already the signed elliptic trace. -/
theorem jacobi_splitPrimeAgreement_paid :
    JacobiSplitPrimeAgreement := by
  intro p hp hmod
  obtain ⟨w⟩ := splitPrimeCanonicalWitness_of_mod_four_eq_one hp hmod
  rw [cmJacobiArithmeticFunction_apply,
    cmJacobiArithmeticCoefficient_splitPrime hp w.normExact]
  letI : Fact p.Prime := ⟨hp⟩
  rw [split_frobenius_signed hp w.normExact hmod]
  push_cast
  ring

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
    have hoddN : Odd N := by simpa [hsq] using hodd
    rcases hN with ⟨a, ha⟩
    rcases hoddN with ⟨b, hb⟩
    omega
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
    have hevenN : Even N := by simpa [hsq] using heven
    rcases hevenN with ⟨a, ha⟩
    rcases hN with ⟨b, hb⟩
    omega
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

theorem cmJacobiOddCoeff_eq_zero_of_mod_four_ne_one
    {N : ℕ} (hN : N % 4 ≠ 1) :
    cmJacobiOddCoeff N = 0 := by
  unfold cmJacobiOddCoeff
  apply Finset.sum_eq_zero
  intro r hr
  split_ifs with hsq
  · have hsquare : (2 * r + 1) ^ 2 % 4 = 1 := by
      have hid : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
      rw [hid]
      omega
    exact (hN (by simpa [hsq] using hsquare)).elim
  · rfl

theorem cmJacobiEvenCoeff_eq_zero_of_mod_four_ne_zero
    {N : ℕ} (hN : N % 4 ≠ 0) :
    cmJacobiEvenCoeff N = 0 := by
  unfold cmJacobiEvenCoeff
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    exact hN (by norm_num)
  rw [if_neg hN0, zero_add]
  apply Finset.sum_eq_zero
  intro s hs
  split_ifs with hterm
  · rcases hterm with ⟨hspos, hsq⟩
    apply (hN ?_).elim
    rw [← hsq]
    omega
  · rfl

/-- The full Jacobi convolution is supported on the CM residue class
N ≡ 1 (mod 4). -/
theorem cmJacobiArithmeticCoefficient_eq_zero_of_mod_four_ne_one
    {N : ℕ} (hN : N % 4 ≠ 1) :
    cmJacobiArithmeticCoefficient N = 0 := by
  unfold cmJacobiArithmeticCoefficient
  apply Finset.sum_eq_zero
  intro ij hij
  rcases ij with ⟨i,j⟩
  have hijsum : i + j = N := by
    simpa using Finset.mem_antidiagonal.mp hij
  by_cases hi : i % 4 = 1
  · by_cases hj : j % 4 = 0
    · exfalso
      apply hN
      rw [← hijsum, Nat.add_mod, hi, hj]
      norm_num
    · rw [cmJacobiEvenCoeff_eq_zero_of_mod_four_ne_zero hj, mul_zero]
  · rw [cmJacobiOddCoeff_eq_zero_of_mod_four_ne_one hi, zero_mul]

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
      refine ⟨2 ^ k, ?_⟩
      simp [pow_succ, two_mul]
    exact cmJacobiArithmeticCoefficient_eq_zero_of_even heven

/-- Internal four-field record consumed by the generic reconstruction compiler. -/
structure JacobiLocalReconstructionData : Prop where
  multiplicative : JacobiArithmeticMultiplicativity
  oddPrime : JacobiOddPrimeAgreement
  oddPrimePowerRecurrence : JacobiOddPrimePowerRecurrence
  twoPower : JacobiTwoPowerAgreement

/-- Prize-facing J3 input after paying the bad-prime-two support internally.
Only the genuinely CM-theta local mathematics remains. -/
structure JacobiCMReconstructionData : Prop where
  multiplicative : JacobiArithmeticMultiplicativity
  splitPrime : JacobiSplitPrimeAgreement
  oddPrimePowerRecurrence : JacobiOddPrimePowerRecurrence

theorem JacobiCMReconstructionData.oddPrime
    (h : JacobiCMReconstructionData) :
    JacobiOddPrimeAgreement :=
  jacobiOddPrimeAgreement_of_split h.splitPrime

theorem JacobiCMReconstructionData.toLocalData
    (h : JacobiCMReconstructionData) :
    JacobiLocalReconstructionData where
  multiplicative := h.multiplicative
  oddPrime := h.oddPrime
  oddPrimePowerRecurrence := h.oddPrimePowerRecurrence
  twoPower := jacobiTwoPowerAgreement_paid

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

/-- Final J3 compiler from the three substantive CM-theta producers. -/
theorem jacobiRepresentationMatchesElliptic_of_cmData
    (h : JacobiCMReconstructionData) :
    JacobiRepresentationMatchesElliptic :=
  jacobiRepresentationMatchesElliptic_of_localData h.toLocalData

/-- Machine-readable statement of the recut analytic arithmetic boundary. -/
structure JacobiArithmeticBoundaryStatus where
  localToGlobalCompilerPaid : Bool
  ellipticPrimeDataPaid : Bool
  ellipticPrimePowerRecurrencePaid : Bool
  jacobiMultiplicativityPaid : Bool
  jacobiInertPrimeAgreementPaid : Bool
  jacobiSplitPrimeAgreementPaid : Bool
  jacobiPrimePowerRecurrencePaid : Bool
  jacobiTwoPowerAgreementPaid : Bool
  deriving DecidableEq, Repr

def jacobiArithmeticBoundaryStatus : JacobiArithmeticBoundaryStatus :=
  ⟨true, true, true, false, true, true, false, true⟩

end Synthesis.Millennium.BSD
