import RequestProject.QuantumMereologyHamiltonianExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exponential derivative spine

Mathlib owns hasDerivAt_exp_smul_const for a fixed element of a complete normed
algebra. DASHI specializes it to the pinned finite matrix C*-algebra.

For K fixed,

  d/dz exp(z K)   = exp(z K) K,
  d²/dz² exp(z K) = exp(z K) K².

The physical real-time path uses K = -iH. Restricting these complex derivative
receipts to the real-time entropy path is kept as a separate bridge so no
complex-vs-real derivative coercion is hidden.
-/

namespace QuantumMereology

open scoped Matrix.Norms.L2Operator

namespace ExponentialDerivative

variable
  {I : Type*}
  [Fintype I] [DecidableEq I]

noncomputable def complexPath
    (K : Matrix I I ℂ) :
    ℂ → Matrix I I ℂ :=
  fun z => NormedSpace.exp (z • K)

theorem hasDerivAt_complexPath
    (K : Matrix I I ℂ)
    (z : ℂ) :
    HasDerivAt
      (complexPath K)
      (NormedSpace.exp (z • K) * K)
      z := by
  simpa [complexPath] using
    hasDerivAt_exp_smul_const K z

theorem hasDerivAt_complexPath_derivative
    (K : Matrix I I ℂ)
    (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => NormedSpace.exp (w • K) * K)
      ((NormedSpace.exp (z • K) * K) * K)
      z := by
  simpa using
    (hasDerivAt_exp_smul_const K z).mul_const K

structure ComplexSecondDerivativeAt
    (K : Matrix I I ℂ)
    (z : ℂ) : Prop where
  first :
    HasDerivAt
      (complexPath K)
      (NormedSpace.exp (z • K) * K)
      z
  second :
    HasDerivAt
      (fun w : ℂ => NormedSpace.exp (w • K) * K)
      ((NormedSpace.exp (z • K) * K) * K)
      z

theorem complexSecondDerivativeAt
    (K : Matrix I I ℂ)
    (z : ℂ) :
    ComplexSecondDerivativeAt K z where
  first := hasDerivAt_complexPath K z
  second := hasDerivAt_complexPath_derivative K z

def schrodingerGenerator
    (H : Matrix I I ℂ) :
    Matrix I I ℂ :=
  (-Complex.I) • H


/-- Real Fréchet derivative map obtained by restricting a complex derivative
vector to the real axis. This keeps the scalar-field change explicit. -/
noncomputable def realRestrictionDerivative
    (v : Matrix I I ℂ) :
    ℝ →L[ℝ] Matrix I I ℂ :=
  (Complex.reCLM.smulRight v +
    Complex.I • Complex.imCLM.smulRight v).comp
      Complex.ofRealCLM

theorem hasFDerivAt_real_complexPath
    (K : Matrix I I ℂ)
    (t : ℝ) :
    HasFDerivAt
      (fun s : ℝ => complexPath K (s : ℂ))
      (realRestrictionDerivative
        (NormedSpace.exp ((t : ℂ) • K) * K))
      t := by
  have h :=
    (hasDerivAt_complexPath K (t : ℂ)).complexToReal_fderiv'
  simpa [realRestrictionDerivative] using
    h.comp t Complex.ofRealCLM.hasFDerivAt

theorem hasFDerivAt_real_complexPath_derivative
    (K : Matrix I I ℂ)
    (t : ℝ) :
    HasFDerivAt
      (fun s : ℝ =>
        NormedSpace.exp ((s : ℂ) • K) * K)
      (realRestrictionDerivative
        ((NormedSpace.exp ((t : ℂ) • K) * K) * K))
      t := by
  have h :=
    (hasDerivAt_complexPath_derivative K (t : ℂ)).complexToReal_fderiv'
  simpa [realRestrictionDerivative] using
    h.comp t Complex.ofRealCLM.hasFDerivAt

theorem complexPath_schrodingerGenerator
    (H : Matrix I I ℂ)
    (z : ℂ) :
    complexPath (schrodingerGenerator H) z =
      NormedSpace.exp (z • ((-Complex.I) • H)) :=
  rfl

structure Boundary where
  complexDerivativeRealRestrictionPaid : Bool := true
  complexSecondDerivativeAutomaticallyComputesEntropySecondDerivative : Bool := false
  exponentialDerivativeProvesHamiltonianIsEmpirical : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem complex_derivative_real_restriction_is_paid :
    canonicalBoundary.complexDerivativeRealRestrictionPaid = true := rfl

theorem matrix_second_derivative_not_entropy_second_derivative :
    canonicalBoundary.complexSecondDerivativeAutomaticallyComputesEntropySecondDerivative = false := rfl

end ExponentialDerivative

def mathlibExponentialDerivativeSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, hasDerivAt_exp_smul_const"
  claim := "Supplies the derivative of z -> exp(z • K) along a fixed element K in the pinned complete finite matrix normed algebra."

def dashiExponentialDerivativeReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "Specialises the mathlib exponential derivative to the finite matrix carrier, derives first/second complex-parameter derivatives, and pays the real-axis Fréchet-derivative restriction while keeping the entropy-chain-rule bridge explicit."

end QuantumMereology
