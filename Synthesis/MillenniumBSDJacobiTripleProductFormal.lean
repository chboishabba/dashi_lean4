import Synthesis.MillenniumBSDJacobiEta32Reduction
import Mathlib.Algebra.Polynomial.Laurent
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

/-- J0→J2 compiler: the diagonal specialization q↦q², z↦-q gives the
alternating square theta product, then q↦X^4 gives the eta32 even factor. -/
def JacobiSquareThetaSpecializationCompiler : Prop :=
  JacobiTripleProductFormal → cmJacobiEvenProductIdentity

/-- Complete q-series producer after the recut: one reusable Jacobi theorem
plus its two explicit specialization compilers. -/
def JacobiEta32FromTripleProductProducer : Prop :=
  JacobiTripleProductFormal ∧
    JacobiCubeSpecializationCompiler ∧
    JacobiSquareThetaSpecializationCompiler

theorem jacobiEta32Products_of_tripleProductProducer
    (h : JacobiEta32FromTripleProductProducer) :
    cmJacobiOddProductIdentity ∧ cmJacobiEvenProductIdentity := by
  rcases h with ⟨hJTP, hCube, hTheta⟩
  exact ⟨hCube hJTP, hTheta hJTP⟩

/-- Machine-readable J0/J1/J2 boundary. formalCarrierPaid records that the
correct Laurent/power-series same-object carrier is now implemented; the
actual triple-product proof and its two specialization compilers remain
mathematical obligations. -/
structure JacobiTripleProductBoundaryStatus where
  formalCarrierPaid : Bool
  tripleProductPaid : Bool
  cubeSpecializationPaid : Bool
  squareThetaSpecializationPaid : Bool
  deriving DecidableEq, Repr

def jacobiTripleProductBoundaryStatus : JacobiTripleProductBoundaryStatus :=
  ⟨true, false, false, false⟩

end Synthesis.Millennium.BSD
