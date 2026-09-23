import Synthesis.MillenniumBSDJacobiEta32Reduction
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic

/-!
# Formal Jacobi triple-product boundary

The eta32 proof currently exposes two classical q-product identities. Their
natural common owner is Jacobi's triple product, not two unrelated axioms.

We state the triple product in the faithful coefficient ring C[z,z⁻¹][[q]],
implemented as PowerSeries (LaurentPolynomial ℂ). To avoid imposing an
artificial topology on Laurent polynomials, the infinite product is stated
coefficientwise in the same eventual-finite-product style used by mathlib's
formal pentagonal theorem.

With indexing n = 0,1,2,... the factor is

  (1-q^(n+1)) (1+z q^n) (1+z⁻¹ q^(n+1)),

and the bilateral series is

  Σ_{k∈Z} z^k q^(k(k-1)/2), represented coefficientwise by pairing
  k=r+1 with k=-r.

The remaining J0 mathematics is to prove this formal identity. The eta32
cube identity is obtained by the standard z-derivative at z=-1; the square
theta identity is obtained by the specialization q↦q², z↦-q. Those
specialization compilers are deliberately kept distinct from the J0 theorem:
the latter is the reusable library result.
-/

namespace Synthesis.Millennium.BSD

open Filter PowerSeries
open scoped LaurentPolynomial PowerSeries.WithPiTopology

abbrev JacobiLaurentCoeff := LaurentPolynomial ℂ
abbrev JacobiBivariateFormal := PowerSeries JacobiLaurentCoeff

/-- Natural triangular exponent r(r+1)/2. -/
def jacobiTriangularNat (r : ℕ) : ℕ :=
  r * (r + 1) / 2

theorem two_mul_jacobiTriangularNat (r : ℕ) :
    2 * jacobiTriangularNat r = r * (r + 1) := by
  unfold jacobiTriangularNat
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)

theorem eight_mul_jacobiTriangularNat_add_one (r : ℕ) :
    8 * jacobiTriangularNat r + 1 = (2 * r + 1) ^ 2 := by
  have h := two_mul_jacobiTriangularNat r
  nlinarith

theorem jacobiTriangularNat_injective :
    Function.Injective jacobiTriangularNat := by
  intro r s hrs
  have hr := eight_mul_jacobiTriangularNat_add_one r
  have hs := eight_mul_jacobiTriangularNat_add_one s
  rw [hrs] at hr
  nlinarith

theorem jacobiTriangularNat_ge (r : ℕ) :
    r ≤ jacobiTriangularNat r := by
  rcases r with _ | r
  · simp [jacobiTriangularNat]
  · have h := two_mul_jacobiTriangularNat (r + 1)
    nlinarith

/-- Finite coefficient formula for the bilateral Jacobi series, already
paired under the canonical integer decomposition k=r+1 or k=-r.  Thus the
coefficient at q^(r(r+1)/2) contains z^(r+1)+z^(-r). -/
noncomputable def jacobiTripleCoefficient (N : ℕ) : JacobiLaurentCoeff :=
  ∑ r ∈ Finset.range (N + 1),
    if jacobiTriangularNat r = N then
      LaurentPolynomial.T ((r + 1 : ℕ) : ℤ) +
        LaurentPolynomial.T (-(r : ℤ))
    else 0

/-- The one-variable Jacobi cube series before the level-32
substitution q↦X^8 and leading X factor. -/
noncomputable def jacobiCubeBaseCoeff (N : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (N + 1),
    if jacobiTriangularNat r = N then
      ((-1 : ℂ) ^ r) * (2 * r + 1)
    else 0

noncomputable def jacobiCubeBaseSeries : PowerSeries ℂ :=
  PowerSeries.mk jacobiCubeBaseCoeff

@[simp] theorem jacobiCubeBaseSeries_coeff (N : ℕ) :
    jacobiCubeBaseSeries.coeff N = jacobiCubeBaseCoeff N := by
  simp [jacobiCubeBaseSeries]

theorem jacobiCubeBaseCoeff_triangular (r : ℕ) :
    jacobiCubeBaseCoeff (jacobiTriangularNat r) =
      ((-1 : ℂ) ^ r) * (2 * r + 1) := by
  unfold jacobiCubeBaseCoeff
  rw [Finset.sum_eq_single r]
  · simp
  · intro s hs hsr
    have hne : jacobiTriangularNat s ≠ jacobiTriangularNat r :=
      fun h => hsr (jacobiTriangularNat_injective h)
    simp [hne]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (jacobiTriangularNat_ge r)

theorem jacobiCubeBaseCoeff_eq_zero_of_not_triangular
    {N : ℕ} (hN : ¬ ∃ r : ℕ, jacobiTriangularNat r = N) :
    jacobiCubeBaseCoeff N = 0 := by
  unfold jacobiCubeBaseCoeff
  apply Finset.sum_eq_zero
  intro r hr
  simp [hN]

theorem cmJacobiOddCoeff_oddSquare_fromTriangular (r : ℕ) :
    cmJacobiOddCoeff ((2 * r + 1) ^ 2) =
      ((-1 : ℂ) ^ r) * (2 * r + 1) := by
  unfold cmJacobiOddCoeff
  rw [Finset.sum_eq_single r]
  · simp
  · intro s hs hsr
    have hsq : (2 * s + 1) ^ 2 ≠ (2 * r + 1) ^ 2 := by
      intro h
      apply hsr
      nlinarith
    simp [hsq]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_range]
    nlinarith

theorem oddSquare_eq_eight_mul_add_one_iff
    (r m : ℕ) :
    (2 * r + 1) ^ 2 = 8 * m + 1 ↔
      jacobiTriangularNat r = m := by
  have htri := eight_mul_jacobiTriangularNat_add_one r
  constructor <;> intro h <;> nlinarith

/-- The level-32 odd-square coefficient at 8m+1 is exactly the base Jacobi
cube coefficient at m. -/
theorem cmJacobiOddCoeff_eight_mul_add_one (m : ℕ) :
    cmJacobiOddCoeff (8 * m + 1) = jacobiCubeBaseCoeff m := by
  by_cases htri : ∃ r : ℕ, jacobiTriangularNat r = m
  · rcases htri with ⟨r, hr⟩
    have hsq : (2 * r + 1) ^ 2 = 8 * m + 1 :=
      (oddSquare_eq_eight_mul_add_one_iff r m).2 hr
    rw [← hsq, cmJacobiOddCoeff_oddSquare_fromTriangular,
      ← hr, jacobiCubeBaseCoeff_triangular]
  · rw [jacobiCubeBaseCoeff_eq_zero_of_not_triangular htri]
    unfold cmJacobiOddCoeff
    apply Finset.sum_eq_zero
    intro r hrange
    split_ifs with hsq
    · exfalso
      apply htri
      refine ⟨r, ?_⟩
      exact (oddSquare_eq_eight_mul_add_one_iff r m).1 hsq
    · rfl

theorem cmJacobiOddCoeff_succ_eq_zero_of_not_eight_dvd
    {N : ℕ} (h8 : ¬ 8 ∣ N) :
    cmJacobiOddCoeff (N + 1) = 0 := by
  unfold cmJacobiOddCoeff
  apply Finset.sum_eq_zero
  intro r hrange
  split_ifs with hsq
  · exfalso
    apply h8
    refine ⟨jacobiTriangularNat r, ?_⟩
    have htri := eight_mul_jacobiTriangularNat_add_one r
    omega
  · rfl


/-- The bilateral side as a formal q-series with Laurent-polynomial
coefficients in z. -/
noncomputable def jacobiTripleSeries : JacobiBivariateFormal :=
  PowerSeries.mk jacobiTripleCoefficient

@[simp] theorem jacobiTripleSeries_coeff (N : ℕ) :
    jacobiTripleSeries.coeff N = jacobiTripleCoefficient N := by
  simp [jacobiTripleSeries]

/-- The n-th finite Jacobi product factor, with n indexed from zero. -/
noncomputable def jacobiTripleFactor (n : ℕ) : JacobiBivariateFormal :=
  (1 - X ^ (n + 1)) *
    (1 + C (LaurentPolynomial.T (1 : ℤ)) * X ^ n) *
    (1 + C (LaurentPolynomial.T (-1 : ℤ)) * X ^ (n + 1))

/-- Euler derivation z*d/dz on Laurent polynomials.  Unlike the ordinary
derivative it preserves the Laurent exponent, which makes the Leibniz proof
on monomials especially simple. -/
noncomputable def jacobiLaurentEuler
    (p : JacobiLaurentCoeff) : JacobiLaurentCoeff :=
  p.sum fun k a =>
    LaurentPolynomial.C ((k : ℂ) * a) * LaurentPolynomial.T k

@[simp] theorem jacobiLaurentEuler_C_mul_T
    (a : ℂ) (k : ℤ) :
    jacobiLaurentEuler
        (LaurentPolynomial.C a * LaurentPolynomial.T k) =
      LaurentPolynomial.C ((k : ℂ) * a) * LaurentPolynomial.T k := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp [jacobiLaurentEuler]

@[simp] theorem jacobiLaurentEuler_zero :
    jacobiLaurentEuler (0 : JacobiLaurentCoeff) = 0 := by
  simp [jacobiLaurentEuler]

theorem jacobiLaurentEuler_add
    (p q : JacobiLaurentCoeff) :
    jacobiLaurentEuler (p + q) =
      jacobiLaurentEuler p + jacobiLaurentEuler q := by
  simp [jacobiLaurentEuler, Finsupp.sum_add_index, add_mul]

/-- Leibniz rule for the Laurent Euler derivation. -/
theorem jacobiLaurentEuler_mul
    (p q : JacobiLaurentCoeff) :
    jacobiLaurentEuler (p * q) =
      jacobiLaurentEuler p * q + p * jacobiLaurentEuler q := by
  induction p using LaurentPolynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
      simp only [add_mul, jacobiLaurentEuler_add, hp₁, hp₂]
      ring
  | C_mul_T m a =>
      induction q using LaurentPolynomial.induction_on' with
      | add q₁ q₂ hq₁ hq₂ =>
          simp only [mul_add, jacobiLaurentEuler_add, hq₁, hq₂]
          ring
      | C_mul_T n b =>
          simp only [← LaurentPolynomial.single_eq_C_mul_T]
          ext j
          simp [jacobiLaurentEuler, AddMonoidAlgebra.single_mul_single]
          split_ifs <;> push_cast <;> ring

/-- Formal derivative in the Laurent variable z. -/
noncomputable def jacobiLaurentDerivative
    (p : JacobiLaurentCoeff) : JacobiLaurentCoeff :=
  p.sum fun k a =>
    LaurentPolynomial.C ((k : ℂ) * a) *
      LaurentPolynomial.T (k - 1)

@[simp] theorem jacobiLaurentDerivative_T (k : ℤ) :
    jacobiLaurentDerivative (LaurentPolynomial.T k : JacobiLaurentCoeff) =
      LaurentPolynomial.C (k : ℂ) * LaurentPolynomial.T (k - 1) := by
  simp [jacobiLaurentDerivative, LaurentPolynomial.T]

/-- The unit -1 used for Laurent evaluation. -/
noncomputable def jacobiNegOneUnit : ℂˣ :=
  Units.mk0 (-1 : ℂ) (by norm_num)

/-- Evaluate the Euler derivation at z=-1. -/
noncomputable def jacobiLaurentEulerAtNegOne
    (p : JacobiLaurentCoeff) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) jacobiNegOneUnit
    (jacobiLaurentEuler p)

/-- Laurent evaluation at z=-1 as a ring homomorphism. -/
noncomputable def jacobiEvalNegOneHom : JacobiLaurentCoeff →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) jacobiNegOneUnit

/-- Coefficientwise evaluation z=-1 on the bivariate q-series. -/
noncomputable def jacobiEvalZAtNegOne
    (F : JacobiBivariateFormal) : PowerSeries ℂ :=
  PowerSeries.map jacobiEvalNegOneHom F

@[simp] theorem jacobiEvalZAtNegOne_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiEvalZAtNegOne F).coeff N =
      jacobiEvalNegOneHom (F.coeff N) := by
  simp [jacobiEvalZAtNegOne]

theorem jacobiLaurentEulerAtNegOne_add
    (p q : JacobiLaurentCoeff) :
    jacobiLaurentEulerAtNegOne (p + q) =
      jacobiLaurentEulerAtNegOne p + jacobiLaurentEulerAtNegOne q := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_add,
    jacobiEvalNegOneHom]

theorem jacobiLaurentEulerAtNegOne_mul
    (p q : JacobiLaurentCoeff) :
    jacobiLaurentEulerAtNegOne (p * q) =
      jacobiLaurentEulerAtNegOne p * jacobiEvalNegOneHom q +
        jacobiEvalNegOneHom p * jacobiLaurentEulerAtNegOne q := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_mul,
    jacobiEvalNegOneHom, mul_add, add_mul]

theorem jacobiLaurentEulerAtNegOne_sum
    {ι : Type*} (s : Finset ι) (f : ι → JacobiLaurentCoeff) :
    jacobiLaurentEulerAtNegOne (∑ i ∈ s, f i) =
      ∑ i ∈ s, jacobiLaurentEulerAtNegOne (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_zero]
  | insert a s ha ih =>
      simp [ha, jacobiLaurentEulerAtNegOne_add, ih]

theorem jacobiLaurentEulerAtNegOne_T_nat (n : ℕ) :
    jacobiLaurentEulerAtNegOne
        (LaurentPolynomial.T (n : ℤ) : JacobiLaurentCoeff) =
      (n : ℂ) * ((-1 : ℂ) ^ n) := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_T,
    jacobiNegOneUnit, LaurentPolynomial.eval₂_T_n]

theorem jacobiLaurentEulerAtNegOne_T_neg_nat (n : ℕ) :
    jacobiLaurentEulerAtNegOne
        (LaurentPolynomial.T (-(n : ℤ)) : JacobiLaurentCoeff) =
      -(n : ℂ) * ((-1 : ℂ) ^ n) := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_T,
    jacobiNegOneUnit, LaurentPolynomial.eval₂_T_neg_n]
  ring

/-- The canonical pair k=r+1 and k=-r on the bilateral side produces
exactly the signed odd coefficient of Jacobi's cube identity. -/
theorem jacobiLaurentEulerAtNegOne_pairedTerm (r : ℕ) :
    jacobiLaurentEulerAtNegOne
      (LaurentPolynomial.T ((r + 1 : ℕ) : ℤ) +
        LaurentPolynomial.T (-(r : ℤ))) =
      -(((-1 : ℂ) ^ r) * (2 * r + 1)) := by
  rw [jacobiLaurentEulerAtNegOne_add,
    jacobiLaurentEulerAtNegOne_T_nat,
    jacobiLaurentEulerAtNegOne_T_neg_nat]
  rw [pow_succ]
  push_cast
  ring


/-- Coefficientwise Euler derivation/evaluation on the bivariate q-series. -/
noncomputable def jacobiEulerZAtNegOne
    (F : JacobiBivariateFormal) : PowerSeries ℂ :=
  PowerSeries.mk fun N => jacobiLaurentEulerAtNegOne (F.coeff N)

@[simp] theorem jacobiEulerZAtNegOne_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiEulerZAtNegOne F).coeff N =
      jacobiLaurentEulerAtNegOne (F.coeff N) := by
  simp [jacobiEulerZAtNegOne]

/-- The existing level-32 odd-square series is literally the base Jacobi
cube series after q↦X^8 and multiplication by the leading X. -/
theorem cmJacobiOddSeries_eq_X_subst_jacobiCubeBase :
    cmJacobiOddSeries =
      X * jacobiCubeBaseSeries.subst (X ^ 8) := by
  ext N
  rcases N with _ | N
  · simp [cmJacobiOddSeries_coeff, cmJacobiOddCoeff]
  · rw [cmJacobiOddSeries_coeff]
    rw [show (X : PowerSeries ℂ) = X ^ 1 by simp,
      PowerSeries.coeff_X_pow_mul']
    simp only [Nat.one_le_iff_ne_zero, Nat.succ_ne_zero, if_true,
      Nat.succ_sub_one]
    rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
      (by norm_num : (8 : ℕ) ≠ 0)]
    by_cases h8 : 8 ∣ N
    · rcases h8 with ⟨m, rfl⟩
      simp [cmJacobiOddCoeff_eight_mul_add_one,
        jacobiCubeBaseSeries_coeff]
    · rw [if_neg h8]
      exact cmJacobiOddCoeff_succ_eq_zero_of_not_eight_dvd h8

/-- Bilateral-series half of the cube specialization. -/
theorem jacobiEulerZAtNegOne_tripleSeries :
    jacobiEulerZAtNegOne jacobiTripleSeries =
      -jacobiCubeBaseSeries := by
  ext N
  rw [jacobiEulerZAtNegOne_coeff, jacobiTripleSeries_coeff,
    PowerSeries.coeff_neg, jacobiCubeBaseSeries_coeff]
  unfold jacobiTripleCoefficient jacobiCubeBaseCoeff
  rw [jacobiLaurentEulerAtNegOne_sum]
  rw [Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with htri
  · rw [jacobiLaurentEulerAtNegOne_pairedTerm]
  · simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_zero]


theorem jacobiEulerZAtNegOne_add
    (F G : JacobiBivariateFormal) :
    jacobiEulerZAtNegOne (F + G) =
      jacobiEulerZAtNegOne F + jacobiEulerZAtNegOne G := by
  ext N
  simp [jacobiEulerZAtNegOne, jacobiLaurentEulerAtNegOne_add]

theorem jacobiEulerZAtNegOne_neg
    (F : JacobiBivariateFormal) :
    jacobiEulerZAtNegOne (-F) = -jacobiEulerZAtNegOne F := by
  have h := jacobiEulerZAtNegOne_add F (-F)
  rw [add_neg_cancel, jacobiEulerZAtNegOne_add] at h
  have hz : jacobiEulerZAtNegOne (0 : JacobiBivariateFormal) = 0 := by
    ext N
    simp [jacobiEulerZAtNegOne, jacobiLaurentEulerAtNegOne,
      jacobiLaurentEuler_zero]
  rw [hz] at h
  exact eq_neg_of_add_eq_zero_left h

theorem jacobiEulerZAtNegOne_sub
    (F G : JacobiBivariateFormal) :
    jacobiEulerZAtNegOne (F - G) =
      jacobiEulerZAtNegOne F - jacobiEulerZAtNegOne G := by
  rw [sub_eq_add_neg, jacobiEulerZAtNegOne_add,
    jacobiEulerZAtNegOne_neg, sub_eq_add_neg]

@[simp] theorem jacobiLaurentEulerAtNegOne_T_one :
    jacobiLaurentEulerAtNegOne (LaurentPolynomial.T (1 : ℤ)) = -1 := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_T,
    jacobiNegOneUnit]

@[simp] theorem jacobiLaurentEulerAtNegOne_T_neg_one :
    jacobiLaurentEulerAtNegOne (LaurentPolynomial.T (-1 : ℤ)) = 1 := by
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_T,
    jacobiNegOneUnit]

theorem jacobiEulerZAtNegOne_C_T_mul_X_pow
    (k : ℤ) (n : ℕ) :
    jacobiEulerZAtNegOne
        (C (LaurentPolynomial.T k) * X ^ n : JacobiBivariateFormal) =
      C (jacobiLaurentEulerAtNegOne (LaurentPolynomial.T k)) * X ^ n := by
  ext N
  simp [jacobiEulerZAtNegOne, PowerSeries.coeff_C_mul_X_pow]

@[simp] theorem jacobiEulerZAtNegOne_one :
    jacobiEulerZAtNegOne (1 : JacobiBivariateFormal) = 0 := by
  ext N
  simp [jacobiEulerZAtNegOne, jacobiLaurentEulerAtNegOne,
    jacobiLaurentEuler]

@[simp] theorem jacobiEulerZAtNegOne_X_pow (n : ℕ) :
    jacobiEulerZAtNegOne (X ^ n : JacobiBivariateFormal) = 0 := by
  rw [show (X ^ n : JacobiBivariateFormal) =
      C (LaurentPolynomial.T (0 : ℤ)) * X ^ n by simp]
  rw [jacobiEulerZAtNegOne_C_T_mul_X_pow]
  simp [jacobiLaurentEulerAtNegOne, jacobiLaurentEuler_T]

@[simp] theorem jacobiEulerZAtNegOne_T_one_mul_X_pow (n : ℕ) :
    jacobiEulerZAtNegOne
        (C (LaurentPolynomial.T (1 : ℤ)) * X ^ n :
          JacobiBivariateFormal) =
      -(X ^ n : PowerSeries ℂ) := by
  rw [jacobiEulerZAtNegOne_C_T_mul_X_pow]
  simp

@[simp] theorem jacobiEulerZAtNegOne_T_neg_one_mul_X_pow (n : ℕ) :
    jacobiEulerZAtNegOne
        (C (LaurentPolynomial.T (-1 : ℤ)) * X ^ n :
          JacobiBivariateFormal) =
      (X ^ n : PowerSeries ℂ) := by
  rw [jacobiEulerZAtNegOne_C_T_mul_X_pow]
  simp

/-- The coefficientwise Euler-at-minus-one operator is a derivation relative
to the coefficient evaluation homomorphism. -/
theorem jacobiEulerZAtNegOne_mul
    (F G : JacobiBivariateFormal) :
    jacobiEulerZAtNegOne (F * G) =
      jacobiEulerZAtNegOne F * jacobiEvalZAtNegOne G +
        jacobiEvalZAtNegOne F * jacobiEulerZAtNegOne G := by
  ext N
  rw [jacobiEulerZAtNegOne_coeff, PowerSeries.coeff_mul]
  rw [jacobiLaurentEulerAtNegOne_sum]
  simp only [jacobiLaurentEulerAtNegOne_mul]
  rw [PowerSeries.coeff_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simp only [jacobiEulerZAtNegOne_coeff, jacobiEvalZAtNegOne_coeff]
  rw [Finset.sum_add_distrib]

/-- Differentiate a Laurent polynomial and evaluate at z=-1. -/
noncomputable def jacobiLaurentDerivativeAtNegOne
    (p : JacobiLaurentCoeff) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) jacobiNegOneUnit
    (jacobiLaurentDerivative p)

/-- Apply D_z|_{z=-1} coefficientwise to a bivariate formal q-series. -/
noncomputable def jacobiDifferentiateZAtNegOne
    (F : JacobiBivariateFormal) : PowerSeries ℂ :=
  PowerSeries.mk fun N => jacobiLaurentDerivativeAtNegOne (F.coeff N)

@[simp] theorem jacobiDifferentiateZAtNegOne_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiDifferentiateZAtNegOne F).coeff N =
      jacobiLaurentDerivativeAtNegOne (F.coeff N) := by
  simp [jacobiDifferentiateZAtNegOne]

@[simp] theorem jacobiEvalNegOne_T_one :
    jacobiEvalNegOneHom (LaurentPolynomial.T (1 : ℤ)) = -1 := by
  simp [jacobiEvalNegOneHom, jacobiNegOneUnit]

@[simp] theorem jacobiEvalNegOne_T_neg_one :
    jacobiEvalNegOneHom (LaurentPolynomial.T (-1 : ℤ)) = -1 := by
  simp [jacobiEvalNegOneHom, jacobiNegOneUnit]

/-- At z=-1 the n-th Jacobi factor becomes the expected three Euler factors. -/
theorem jacobiEvalZAtNegOne_factor (n : ℕ) :
    jacobiEvalZAtNegOne (jacobiTripleFactor n) =
      (1 - X ^ (n + 1)) * (1 - X ^ n) * (1 - X ^ (n + 1)) := by
  simp [jacobiEvalZAtNegOne, jacobiTripleFactor, jacobiEvalNegOneHom]

@[simp] theorem jacobiEvalZAtNegOne_factor_zero :
    jacobiEvalZAtNegOne (jacobiTripleFactor 0) = 0 := by
  rw [jacobiEvalZAtNegOne_factor]
  simp

/-- The unique vanishing zero-index factor supplies the entire Euler
derivative of the infinite product at z=-1.  Its own derivative seed is
minus the square of the first Euler factor. -/
theorem jacobiEulerZAtNegOne_factor_zero :
    jacobiEulerZAtNegOne (jacobiTripleFactor 0) =
      -((1 - X : PowerSeries ℂ) ^ 2) := by
  unfold jacobiTripleFactor
  rw [jacobiEulerZAtNegOne_mul, jacobiEulerZAtNegOne_mul]
  simp [jacobiEvalZAtNegOne_factor, jacobiEvalZAtNegOne,
    jacobiEvalNegOneHom]
  ring

/-- Consequently any finite Jacobi product containing the zero-index factor
vanishes under z=-1 evaluation. -/
theorem jacobiEvalZAtNegOne_finsetProduct_eq_zero
    {s : Finset ℕ} (h0 : 0 ∈ s) :
    jacobiEvalZAtNegOne (∏ n ∈ s, jacobiTripleFactor n) = 0 := by
  rw [show (∏ n ∈ s, jacobiTripleFactor n) =
      jacobiTripleFactor 0 * ∏ n ∈ s.erase 0, jacobiTripleFactor n by
        rw [Finset.prod_eq_mul_prod_diff_singleton h0]
        simp]
  simp [jacobiEvalZAtNegOne]

/-- Finite initial Jacobi product used to pass from the coefficientwise
atTop statement to concrete range truncations. -/
noncomputable def jacobiFiniteProduct (M : ℕ) : JacobiBivariateFormal :=
  ∏ n ∈ Finset.range M, jacobiTripleFactor n

@[simp] theorem jacobiFiniteProduct_zero :
    jacobiFiniteProduct 0 = 1 := by
  simp [jacobiFiniteProduct]

theorem jacobiFiniteProduct_succ (M : ℕ) :
    jacobiFiniteProduct (M + 1) =
      jacobiFiniteProduct M * jacobiTripleFactor M := by
  simp [jacobiFiniteProduct, Finset.prod_range_succ]

theorem jacobiEvalZAtNegOne_finiteProduct_eq_zero
    {M : ℕ} (hM : 0 < M) :
    jacobiEvalZAtNegOne (jacobiFiniteProduct M) = 0 := by
  apply jacobiEvalZAtNegOne_finsetProduct_eq_zero
  simp [Finset.mem_range, hM]

@[simp] theorem jacobiEulerZAtNegOne_finiteProduct_one :
    jacobiEulerZAtNegOne (jacobiFiniteProduct 1) =
      -((1 - X : PowerSeries ℂ) ^ 2) := by
  simp [jacobiFiniteProduct, jacobiEulerZAtNegOne_factor_zero]

/-- After the zero-index factor has entered the product, adjoining another
Jacobi factor simply multiplies the Euler derivative by that factor's
z=-1 evaluation; the second Leibniz term vanishes. -/
theorem jacobiEulerZAtNegOne_finiteProduct_succ
    {M : ℕ} (hM : 0 < M) :
    jacobiEulerZAtNegOne (jacobiFiniteProduct (M + 1)) =
      jacobiEulerZAtNegOne (jacobiFiniteProduct M) *
        jacobiEvalZAtNegOne (jacobiTripleFactor M) := by
  rw [jacobiFiniteProduct_succ, jacobiEulerZAtNegOne_mul]
  rw [jacobiEvalZAtNegOne_finiteProduct_eq_zero hM]
  simp

/-- Finite Euler product P_M = ∏_{m=1}^M (1-X^m). -/
noncomputable def jacobiEulerFiniteProduct (M : ℕ) : PowerSeries ℂ :=
  ∏ n ∈ Finset.range M, (1 - X ^ (n + 1))

@[simp] theorem jacobiEulerFiniteProduct_zero :
    jacobiEulerFiniteProduct 0 = 1 := by
  simp [jacobiEulerFiniteProduct]

theorem jacobiEulerFiniteProduct_succ (M : ℕ) :
    jacobiEulerFiniteProduct (M + 1) =
      jacobiEulerFiniteProduct M * (1 - X ^ (M + 1)) := by
  simp [jacobiEulerFiniteProduct, Finset.prod_range_succ]

/-- Exact finite product-side cube formula.  The only discrepancy from
-P_M^3 is the last boundary factor, which disappears coefficientwise as
M→∞. -/
theorem jacobiEulerZAtNegOne_finiteProduct_exact (M : ℕ) :
    jacobiEulerZAtNegOne (jacobiFiniteProduct (M + 1)) =
      -(jacobiEulerFiniteProduct M ^ 3) *
        (1 - X ^ (M + 1)) ^ 2 := by
  induction M with
  | zero =>
      simp [jacobiEulerZAtNegOne_finiteProduct_one]
  | succ M ih =>
      have hpos : 0 < M + 1 := by omega
      rw [show M + 2 = (M + 1) + 1 by omega,
        jacobiEulerZAtNegOne_finiteProduct_succ hpos,
        ih, jacobiEvalZAtNegOne_factor,
        jacobiEulerFiniteProduct_succ]
      ring

theorem tendsto_jacobiEulerFiniteProduct :
    Tendsto jacobiEulerFiniteProduct atTop (𝓝 cmEtaEulerFormal) := by
  simpa [jacobiEulerFiniteProduct, cmEtaEulerFormal] using
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℂ).tendsto_prod_nat

theorem tendsto_X_pow_succ_zero :
    Tendsto (fun M : ℕ => (X : PowerSeries ℂ) ^ (M + 1))
      atTop (𝓝 0) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply tendsto_atTop_of_eventually_const
  filter_upwards [eventually_ge_atTop (d + 1)] with M hM
  simp [PowerSeries.coeff_X_pow]
  omega

theorem tendsto_jacobiEulerBoundary :
    Tendsto (fun M : ℕ => (1 - (X : PowerSeries ℂ) ^ (M + 1)) ^ 2)
      atTop (𝓝 1) := by
  have hsub :
      Tendsto (fun M : ℕ => 1 - (X : PowerSeries ℂ) ^ (M + 1))
        atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_X_pow_succ_zero
  simpa using hsub.pow 2

/-- Product-side J0→J1 limit: differentiating the finite Jacobi products in
the Laurent variable and evaluating at z=-1 converges to minus Euler's cube. -/
theorem tendsto_jacobiEulerZAtNegOne_finiteProduct :
    Tendsto
      (fun M : ℕ =>
        jacobiEulerZAtNegOne (jacobiFiniteProduct (M + 1)))
      atTop (𝓝 (-(cmEtaEulerFormal ^ 3))) := by
  have hmain :
      Tendsto
        (fun M : ℕ => -(jacobiEulerFiniteProduct M ^ 3))
        atTop (𝓝 (-(cmEtaEulerFormal ^ 3))) :=
    (tendsto_jacobiEulerFiniteProduct.pow 3).neg
  have hmul := hmain.mul tendsto_jacobiEulerBoundary
  simpa [jacobiEulerZAtNegOne_finiteProduct_exact] using hmul

/-- J0: formal Jacobi triple product, in the same coefficientwise eventual
product form as the formal pentagonal theorem.

This is the single reusable q-series producer from which the two eta32
specializations should be compiled. -/
def JacobiTripleProductFormal : Prop :=
  ∀ N : ℕ,
    ∀ᶠ s : Finset ℕ in atTop,
      (∏ n ∈ s, jacobiTripleFactor n).coeff N =
        jacobiTripleSeries.coeff N

theorem tendsto_jacobiFiniteProduct_coeff_of_tripleProduct
    (hJ : JacobiTripleProductFormal) (N : ℕ) :
    Tendsto
      (fun M : ℕ => (jacobiFiniteProduct (M + 1)).coeff N)
      atTop (𝓝 (jacobiTripleSeries.coeff N)) := by
  have hRange :
      Tendsto (fun M : ℕ => Finset.range (M + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hEventually :
      ∀ᶠ M : ℕ in atTop,
        (jacobiFiniteProduct (M + 1)).coeff N =
          jacobiTripleSeries.coeff N := by
    filter_upwards [hRange.eventually (hJ N)] with M hM
    simpa [jacobiFiniteProduct] using hM
  exact tendsto_const_nhds.congr' hEventually.symm

theorem tendsto_jacobiEulerZAtNegOne_finiteProduct_of_tripleProduct
    (hJ : JacobiTripleProductFormal) :
    Tendsto
      (fun M : ℕ =>
        jacobiEulerZAtNegOne (jacobiFiniteProduct (M + 1)))
      atTop (𝓝 (jacobiEulerZAtNegOne jacobiTripleSeries)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro N
  have hRange :
      Tendsto (fun M : ℕ => Finset.range (M + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hEventually :
      ∀ᶠ M : ℕ in atTop,
        (jacobiEulerZAtNegOne (jacobiFiniteProduct (M + 1))).coeff N =
          (jacobiEulerZAtNegOne jacobiTripleSeries).coeff N := by
    filter_upwards [hRange.eventually (hJ N)] with M hM
    simp only [jacobiEulerZAtNegOne_coeff]
    rw [hM]
  exact tendsto_const_nhds.congr' hEventually.symm

/-- J0 already forces the classical Jacobi cube identity in the base
q-variable.  Both sides are identified as the unique limit of the same
Euler-differentiated finite products. -/
theorem jacobiCubeBaseSeries_eq_eulerCube
    (hJ : JacobiTripleProductFormal) :
    jacobiCubeBaseSeries = cmEtaEulerFormal ^ 3 := by
  have hFromJ :=
    tendsto_jacobiEulerZAtNegOne_finiteProduct_of_tripleProduct hJ
  have hFromEuler := tendsto_jacobiEulerZAtNegOne_finiteProduct
  have hEq :
      jacobiEulerZAtNegOne jacobiTripleSeries =
        -(cmEtaEulerFormal ^ 3) :=
    tendsto_nhds_unique hFromJ hFromEuler
  rw [jacobiEulerZAtNegOne_tripleSeries] at hEq
  exact neg_injective hEq

/-- J0→J1 compiler: formal differentiation in the Laurent variable followed
by evaluation at z=-1 gives Jacobi's cube identity, then q↦X^8 gives the
eta32 odd factor.  This is an algebraic specialization obligation, not a
second independent q-product theorem. -/
def JacobiCubeSpecializationCompiler : Prop :=
  JacobiTripleProductFormal → cmJacobiOddProductIdentity

/-- J1 is now internally paid from J0: the base cube identity is transported
through q↦X^8 and the leading X. -/
theorem jacobiCubeSpecializationCompiler_paid :
    JacobiCubeSpecializationCompiler := by
  intro hJ
  unfold cmJacobiOddProductIdentity
  rw [cmJacobiOddSeries_eq_X_subst_jacobiCubeBase,
    jacobiCubeBaseSeries_eq_eulerCube hJ]
  rw [PowerSeries.subst_pow
    (PowerSeries.HasSubst.X_pow (by norm_num : (8 : ℕ) ≠ 0))
    cmEtaEulerFormal 3]


/-- Base square-theta coefficient before the level-32 substitution q↦X^4.
The deliberately generous finite range matches the already-existing
level-32 coefficient definition and avoids a separate range-reindexing
lemma. -/
noncomputable def jacobiSquareThetaBaseCoeff (N : ℕ) : ℂ :=
  (if N = 0 then 1 else 0) +
    ∑ s in Finset.range (4 * N + 1),
      if 0 < s ∧ s ^ 2 = N then
        2 * ((-1 : ℂ) ^ s)
      else 0

noncomputable def jacobiSquareThetaBaseSeries : PowerSeries ℂ :=
  PowerSeries.mk jacobiSquareThetaBaseCoeff

@[simp] theorem jacobiSquareThetaBaseSeries_coeff (N : ℕ) :
    jacobiSquareThetaBaseSeries.coeff N =
      jacobiSquareThetaBaseCoeff N := by
  simp [jacobiSquareThetaBaseSeries]

/-- The base square-theta coefficient is exactly the existing level-32
coefficient with its exponent divided by four. -/
theorem jacobiSquareThetaBaseCoeff_eq_cmJacobiEvenCoeff_four_mul
    (N : ℕ) :
    jacobiSquareThetaBaseCoeff N = cmJacobiEvenCoeff (4 * N) := by
  unfold jacobiSquareThetaBaseCoeff cmJacobiEvenCoeff
  congr 1
  · congr
    omega
  · apply Finset.sum_congr rfl
    intro s hs
    by_cases hpos : 0 < s
    · have hiff : 4 * s ^ 2 = 4 * N ↔ s ^ 2 = N := by omega
      simp [hpos, hiff]
    · simp [hpos]

/-- The existing even-square coefficient has support only on exponents
divisible by four. -/
theorem cmJacobiEvenCoeff_eq_zero_of_four_not_dvd
    {N : ℕ} (h4 : ¬ 4 ∣ N) :
    cmJacobiEvenCoeff N = 0 := by
  unfold cmJacobiEvenCoeff
  have hN0 : N ≠ 0 := by
    intro hN
    subst N
    exact h4 (dvd_zero 4)
  rw [if_neg hN0, zero_add]
  apply Finset.sum_eq_zero
  intro s hs
  split_ifs with hterm
  · rcases hterm with ⟨hspos, hsq⟩
    exfalso
    apply h4
    refine ⟨s ^ 2, ?_⟩
    exact hsq.symm
  · rfl

/-- The level-32 even-square series is literally the base theta4 series after
q↦X^4. -/
theorem cmJacobiEvenSeries_eq_subst_jacobiSquareThetaBase :
    cmJacobiEvenSeries =
      jacobiSquareThetaBaseSeries.subst (X ^ 4) := by
  ext N
  rw [cmJacobiEvenSeries_coeff,
    PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
      (by norm_num : (4 : ℕ) ≠ 0)]
  by_cases h4 : 4 ∣ N
  · rw [if_pos h4]
    obtain ⟨m, rfl⟩ := h4
    simp [jacobiSquareThetaBaseSeries_coeff,
      jacobiSquareThetaBaseCoeff_eq_cmJacobiEvenCoeff_four_mul]
  · rw [if_neg h4, cmJacobiEvenCoeff_eq_zero_of_four_not_dvd h4]

/-- The base square-theta identity whose q↦X^4 transport is exactly J2. -/
def JacobiSquareThetaBaseIdentity : Prop :=
  jacobiSquareThetaBaseSeries *
      (cmEtaEulerFormal.subst (X ^ 2)) =
    cmEtaEulerFormal ^ 2

/-- Transport the base theta4 identity to the exact level-32 even-product
identity already consumed by the eta32 weld. -/
theorem cmJacobiEvenProductIdentity_of_squareThetaBase
    (hTheta : JacobiSquareThetaBaseIdentity) :
    cmJacobiEvenProductIdentity := by
  unfold JacobiSquareThetaBaseIdentity at hTheta
  unfold cmJacobiEvenProductIdentity
  have h4 : PowerSeries.HasSubst (X ^ 4 : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have h2 : PowerSeries.HasSubst (X ^ 2 : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have hTransport := congrArg (PowerSeries.subst (X ^ 4)) hTheta
  rw [PowerSeries.subst_mul h4,
    PowerSeries.subst_pow h4,
    PowerSeries.subst_comp_subst_apply h2 h4] at hTransport
  have hx24 :
      PowerSeries.subst (X ^ 4 : PowerSeries ℂ)
          (X ^ 2 : PowerSeries ℂ) =
        (X ^ 8 : PowerSeries ℂ) := by
    rw [PowerSeries.subst_pow h4]
    simp [pow_mul]
  rw [hx24] at hTransport
  rw [← cmJacobiEvenSeries_eq_subst_jacobiSquareThetaBase]
    at hTransport
  exact hTransport

/-- Product-side finite specialization of Jacobi's triple product under
q↦q² and z↦-q. -/
noncomputable def jacobiSquareThetaFiniteProduct (M : ℕ) :
    PowerSeries ℂ :=
  ∏ n ∈ Finset.range M,
    (1 - X ^ (2 * n + 2)) * (1 - X ^ (2 * n + 1)) ^ 2

/-- Finite even Euler product ∏_{m=1}^M (1-q^(2m)). -/
noncomputable def jacobiEvenEulerFiniteProduct (M : ℕ) :
    PowerSeries ℂ :=
  ∏ n ∈ Finset.range M, (1 - X ^ (2 * n + 2))

/-- Finite odd Euler product ∏_{n=0}^{M-1} (1-q^(2n+1)). -/
noncomputable def jacobiOddEulerFiniteProduct (M : ℕ) :
    PowerSeries ℂ :=
  ∏ n ∈ Finset.range M, (1 - X ^ (2 * n + 1))

theorem jacobiSquareThetaFiniteProduct_factor (M : ℕ) :
    jacobiSquareThetaFiniteProduct M =
      jacobiEvenEulerFiniteProduct M *
        jacobiOddEulerFiniteProduct M ^ 2 := by
  unfold jacobiSquareThetaFiniteProduct
    jacobiEvenEulerFiniteProduct jacobiOddEulerFiniteProduct
  rw [← Finset.prod_mul_distrib]
  simp only [mul_pow]
  ring_nf
  rw [Finset.prod_mul_distrib]
  congr 1
  ext n
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- The first 2M Euler factors split into their even and odd parts. -/
theorem jacobiEulerFiniteProduct_two_mul_split (M : ℕ) :
    jacobiEulerFiniteProduct (2 * M) =
      jacobiEvenEulerFiniteProduct M *
        jacobiOddEulerFiniteProduct M := by
  induction M with
  | zero =>
      simp [jacobiEulerFiniteProduct, jacobiEvenEulerFiniteProduct,
        jacobiOddEulerFiniteProduct]
  | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 2 by omega]
      rw [show jacobiEulerFiniteProduct (2 * M + 2) =
          jacobiEulerFiniteProduct (2 * M) *
            (1 - X ^ (2 * M + 1)) *
            (1 - X ^ (2 * M + 2)) by
        rw [show 2 * M + 2 = (2 * M + 1) + 1 by omega,
          jacobiEulerFiniteProduct_succ,
          jacobiEulerFiniteProduct_succ]
        ring]
      rw [ih]
      simp [jacobiEvenEulerFiniteProduct, jacobiOddEulerFiniteProduct,
        Finset.prod_range_succ]
      ring

/-- Exact finite theta4 product identity; this is the product-side analogue
of the finite cube formula used for J1. -/
theorem jacobiSquareThetaFiniteProduct_exact (M : ℕ) :
    jacobiSquareThetaFiniteProduct M *
        jacobiEvenEulerFiniteProduct M =
      jacobiEulerFiniteProduct (2 * M) ^ 2 := by
  rw [jacobiSquareThetaFiniteProduct_factor,
    jacobiEulerFiniteProduct_two_mul_split]
  ring

theorem tendsto_jacobiEvenEulerFiniteProduct :
    Tendsto jacobiEvenEulerFiniteProduct atTop
      (𝓝 (cmEtaEulerFormal.subst (X ^ 2))) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro N
  have hEuler :=
    PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℂ
  have hSub :
      Tendsto
        (fun M : ℕ =>
          PowerSeries.subst (X ^ 2)
            (jacobiEulerFiniteProduct M))
        atTop
        (𝓝 (PowerSeries.subst (X ^ 2) cmEtaEulerFormal)) := by
    -- coefficientwise continuity of the X^2 substitution is immediate.
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    by_cases h2 : 2 ∣ d
    · obtain ⟨k, rfl⟩ := h2
      simp [jacobiEulerFiniteProduct,
        PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
          (by norm_num : (2 : ℕ) ≠ 0)]
      exact
        (PowerSeries.WithPiTopology.continuous_coeff ℂ k).tendsto.comp
          tendsto_jacobiEulerFiniteProduct
    · simp [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
        (by norm_num : (2 : ℕ) ≠ 0), h2]
  have hFinite (M : ℕ) :
      PowerSeries.subst (X ^ 2)
          (jacobiEulerFiniteProduct M) =
        jacobiEvenEulerFiniteProduct M := by
    unfold jacobiEulerFiniteProduct jacobiEvenEulerFiniteProduct
    have h2s : PowerSeries.HasSubst (X ^ 2 : PowerSeries ℂ) :=
      PowerSeries.HasSubst.X_pow (by norm_num)
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro n hn
    rw [PowerSeries.subst_sub h2s]
    simp [PowerSeries.subst_pow h2s, pow_mul]
  simpa [hFinite] using hSub

theorem tendsto_jacobiEulerFiniteProduct_two_mul :
    Tendsto (fun M : ℕ => jacobiEulerFiniteProduct (2 * M))
      atTop (𝓝 cmEtaEulerFormal) :=
  tendsto_jacobiEulerFiniteProduct.comp
    (tendsto_nat_nhds_top.mpr fun N => ⟨N, fun M hM => by omega⟩)

/-- Product-side limit relation for J2.  Any coefficientwise limit of the
specialized Jacobi finite products must satisfy theta4 * P(q²)=P(q)². -/
theorem tendsto_jacobiSquareThetaFiniteProduct_mul_evenEuler :
    Tendsto
      (fun M : ℕ =>
        jacobiSquareThetaFiniteProduct M *
          jacobiEvenEulerFiniteProduct M)
      atTop
      (𝓝 (cmEtaEulerFormal ^ 2)) := by
  simpa [jacobiSquareThetaFiniteProduct_exact] using
    (tendsto_jacobiEulerFiniteProduct_two_mul.pow 2)

/-- Weighted diagonal coefficient implementing q↦q² and z↦-q
coefficientwise.  For target degree N only outer q-degrees d≤N are inspected;
this is exactly the finite-dependency property needed to transfer J0's
eventual coefficient equalities. -/
noncomputable def jacobiWeightedDiagonalCoeff
    (F : JacobiBivariateFormal) (N : ℕ) : ℂ :=
  ∑ d in Finset.range (N + 1),
    (jacobiDiagonalCoeffHom (F.coeff d)).coeff
      ((N : ℤ) - 2 * (d : ℤ))

noncomputable def jacobiWeightedDiagonal
    (F : JacobiBivariateFormal) : PowerSeries ℂ :=
  PowerSeries.mk (jacobiWeightedDiagonalCoeff F)

@[simp] theorem jacobiWeightedDiagonal_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiWeightedDiagonal F).coeff N =
      jacobiWeightedDiagonalCoeff F N := by
  simp [jacobiWeightedDiagonal]

/-- J0 coefficientwise equality transfers automatically through the finite
weighted diagonal operator. -/
theorem tendsto_jacobiWeightedDiagonal_finiteProduct_of_tripleProduct
    (hJ : JacobiTripleProductFormal) :
    Tendsto
      (fun M : ℕ =>
        jacobiWeightedDiagonal (jacobiFiniteProduct (M + 1)))
      atTop
      (𝓝 (jacobiWeightedDiagonal jacobiTripleSeries)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro N
  have hRange :
      Tendsto (fun M : ℕ => Finset.range (M + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hEach :
      ∀ d ∈ Finset.range (N + 1),
        ∀ᶠ M : ℕ in atTop,
          (jacobiFiniteProduct (M + 1)).coeff d =
            jacobiTripleSeries.coeff d := by
    intro d hd
    filter_upwards [hRange.eventually (hJ d)] with M hM
    simpa [jacobiFiniteProduct] using hM
  have hAll :
      ∀ᶠ M : ℕ in atTop,
        ∀ d ∈ Finset.range (N + 1),
          (jacobiFiniteProduct (M + 1)).coeff d =
            jacobiTripleSeries.coeff d :=
    (Filter.eventually_all_finset (Finset.range (N + 1))).2 hEach
  apply tendsto_atTop_of_eventually_const
  filter_upwards [hAll] with M hM
  rw [jacobiWeightedDiagonal_coeff, jacobiWeightedDiagonal_coeff]
  unfold jacobiWeightedDiagonalCoeff
  apply Finset.sum_congr rfl
  intro d hd
  rw [hM d hd]

/-- First algebraic identification still required by J2: the weighted
diagonal of each finite bivariate Jacobi product is the explicit finite
theta4 product. -/
def JacobiWeightedDiagonalFiniteProductAgreement : Prop :=
  ∀ M : ℕ,
    jacobiWeightedDiagonal (jacobiFiniteProduct M) =
      jacobiSquareThetaFiniteProduct M

/-- Second algebraic identification still required by J2: the weighted
diagonal of the paired bilateral Jacobi series is the standard theta4
series. -/
def JacobiWeightedDiagonalTripleSeriesAgreement : Prop :=
  jacobiWeightedDiagonal jacobiTripleSeries =
    jacobiSquareThetaBaseSeries

/-- The weighted diagonal transfer follows from J0 once the two purely
algebraic identification lemmas above are paid. -/
theorem jacobiSquareThetaDiagonalTransfer_of_weightedDiagonalAgreements
    (hFinite : JacobiWeightedDiagonalFiniteProductAgreement)
    (hSeries : JacobiWeightedDiagonalTripleSeriesAgreement) :
    JacobiSquareThetaDiagonalTransfer := by
  intro hJ
  have h :=
    tendsto_jacobiWeightedDiagonal_finiteProduct_of_tripleProduct hJ
  simpa [hFinite, hSeries] using h

/-- The Laurent-series monomial X, packaged as a unit. -/
noncomputable def jacobiLaurentXUnit : (LaurentSeries ℂ)ˣ where
  val := HahnSeries.single (1 : ℤ) 1
  inv := HahnSeries.single (-1 : ℤ) 1
  val_inv := by simp
  inv_val := by simp

/-- The diagonal value z=-X in the Laurent-series target. -/
noncomputable def jacobiDiagonalZUnit : (LaurentSeries ℂ)ˣ :=
  -jacobiLaurentXUnit

/-- Coefficient-ring specialization z↦-X. -/
noncomputable def jacobiDiagonalCoeffHom :
    JacobiLaurentCoeff →+* LaurentSeries ℂ :=
  LaurentPolynomial.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
    jacobiDiagonalZUnit

@[simp] theorem jacobiDiagonalCoeffHom_T (k : ℤ) :
    jacobiDiagonalCoeffHom (LaurentPolynomial.T k) =
      (jacobiDiagonalZUnit : LaurentSeries ℂ) ^ k := by
  simp [jacobiDiagonalCoeffHom]

/-- Apply z↦-X coefficientwise, while retaining the outer q-variable. -/
noncomputable def jacobiDiagonalCoeffMap
    (F : JacobiBivariateFormal) :
    PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.map jacobiDiagonalCoeffHom F

@[simp] theorem jacobiDiagonalCoeffMap_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiDiagonalCoeffMap F).coeff N =
      jacobiDiagonalCoeffHom (F.coeff N) := by
  simp [jacobiDiagonalCoeffMap]

/-- The exact remaining J0→J2 seam: the weighted diagonal
q↦q², z↦-q carries the finite Jacobi products to the base theta4 series in
the coefficientwise power-series topology. -/
def JacobiSquareThetaDiagonalTransfer : Prop :=
  JacobiTripleProductFormal →
    Tendsto jacobiSquareThetaFiniteProduct atTop
      (𝓝 jacobiSquareThetaBaseSeries)

/-- Once the weighted diagonal limit is known, the base theta4 identity is
forced by uniqueness of limits and the already-paid finite product identity. -/
theorem jacobiSquareThetaBaseIdentity_of_diagonalLimit
    (hDiag :
      Tendsto jacobiSquareThetaFiniteProduct atTop
        (𝓝 jacobiSquareThetaBaseSeries)) :
    JacobiSquareThetaBaseIdentity := by
  unfold JacobiSquareThetaBaseIdentity
  have hLeft :=
    hDiag.mul tendsto_jacobiEvenEulerFiniteProduct
  have hRight :=
    tendsto_jacobiSquareThetaFiniteProduct_mul_evenEuler
  exact tendsto_nhds_unique hLeft hRight

/-- J0→base-theta4 compiler from the single weighted diagonal-transfer
owner. -/
theorem jacobiSquareThetaBaseSpecializationCompiler_paid_of_diagonal
    (hDiag : JacobiSquareThetaDiagonalTransfer) :
    JacobiTripleProductFormal → JacobiSquareThetaBaseIdentity := by
  intro hJ
  exact jacobiSquareThetaBaseIdentity_of_diagonalLimit (hDiag hJ)

/-- The former level-32 J2 compiler is internally compiled from the weighted
diagonal transfer. -/
theorem jacobiSquareThetaSpecializationCompiler_paid_of_diagonal
    (hDiag : JacobiSquareThetaDiagonalTransfer) :
    JacobiTripleProductFormal → cmJacobiEvenProductIdentity := by
  intro hJ
  exact cmJacobiEvenProductIdentity_of_squareThetaBase
    (jacobiSquareThetaBaseIdentity_of_diagonalLimit (hDiag hJ))

/-- Complete q-series producer after paying J1, the J2 product-side limit,
and the level-32 transport internally.  Its only remaining q-series
compatibility input is the weighted diagonal transfer of J0. -/
def JacobiEta32FromTripleProductProducer : Prop :=
  JacobiTripleProductFormal ∧
    JacobiSquareThetaDiagonalTransfer

theorem jacobiEta32Products_of_tripleProductProducer
    (h : JacobiEta32FromTripleProductProducer) :
    cmJacobiOddProductIdentity ∧ cmJacobiEvenProductIdentity := by
  rcases h with ⟨hJTP, hDiag⟩
  exact ⟨jacobiCubeSpecializationCompiler_paid hJTP,
    cmJacobiEvenProductIdentity_of_squareThetaBase
      (jacobiSquareThetaBaseIdentity_of_diagonalLimit (hDiag hJTP))⟩

/-- Machine-readable J0/J1/J2 boundary. formalCarrierPaid records that the
correct Laurent/power-series same-object carrier is now implemented; the
actual triple-product proof and the base theta4 diagonal specialization remain
mathematical obligations; the cube specialization and level-32 theta transport
are paid internally. -/
structure JacobiTripleProductBoundaryStatus where
  formalCarrierPaid : Bool
  tripleProductPaid : Bool
  cubeSpecializationPaid : Bool
  squareThetaSpecializationPaid : Bool
  deriving DecidableEq, Repr

def jacobiTripleProductBoundaryStatus : JacobiTripleProductBoundaryStatus :=
  ⟨true, false, true, false⟩

end Synthesis.Millennium.BSD
