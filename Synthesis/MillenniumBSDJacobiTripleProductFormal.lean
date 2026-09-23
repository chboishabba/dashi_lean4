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

  Σ_{k∈Z} z^k q^(k(k-1)/2).

The remaining J0 mathematics is to prove this formal identity. The eta32
cube identity is obtained by the standard z-derivative at z=-1; the square
theta identity is obtained by the specialization q↦q², z↦-q. Those
specialization compilers are deliberately kept distinct from the J0 theorem:
the latter is the reusable library result.
-/

namespace Synthesis.Millennium.BSD

open Filter PowerSeries
open scoped LaurentPolynomial

abbrev JacobiLaurentCoeff := LaurentPolynomial ℂ
abbrev JacobiBivariateFormal := PowerSeries JacobiLaurentCoeff

/-- The integer triangular exponent k(k-1)/2, known to be nonnegative. -/
def jacobiTriangularInt (k : ℤ) : ℕ :=
  Int.natAbs (k * (k - 1) / 2)

/-- A finite coefficient formula for the bilateral Jacobi series. Any
solution of k(k-1)/2=N lies in [-N-1,N+1], so this interval contains every
contributor. -/
noncomputable def jacobiTripleCoefficient (N : ℕ) : JacobiLaurentCoeff :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
    if jacobiTriangularInt k = N then
      LaurentPolynomial.T k
    else 0

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

/-- Coefficientwise Euler derivation/evaluation on the bivariate q-series. -/
noncomputable def jacobiEulerZAtNegOne
    (F : JacobiBivariateFormal) : PowerSeries ℂ :=
  PowerSeries.mk fun N => jacobiLaurentEulerAtNegOne (F.coeff N)

@[simp] theorem jacobiEulerZAtNegOne_coeff
    (F : JacobiBivariateFormal) (N : ℕ) :
    (jacobiEulerZAtNegOne F).coeff N =
      jacobiLaurentEulerAtNegOne (F.coeff N) := by
  simp [jacobiEulerZAtNegOne]

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

/-- J0: formal Jacobi triple product, in the same coefficientwise eventual
product form as the formal pentagonal theorem.

This is the single reusable q-series producer from which the two eta32
specializations should be compiled. -/
def JacobiTripleProductFormal : Prop :=
  ∀ N : ℕ,
    ∀ᶠ s : Finset ℕ in atTop,
      (∏ n ∈ s, jacobiTripleFactor n).coeff N =
        jacobiTripleSeries.coeff N

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
