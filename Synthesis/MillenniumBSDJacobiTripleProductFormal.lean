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

/-- J0: formal Jacobi triple product, in the same coefficientwise eventual
product form as the formal pentagonal theorem.

This is the single reusable q-series producer from which the two eta32
specializations should be compiled. -/
def JacobiTripleProductFormal : Prop :=
  ∀ N : ℕ,
    ∀ᶠ s : Finset ℕ in atTop,
      (∏ n ∈ s, jacobiTripleFactor n).coeff N =
        jacobiTripleSeries.coeff N

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
