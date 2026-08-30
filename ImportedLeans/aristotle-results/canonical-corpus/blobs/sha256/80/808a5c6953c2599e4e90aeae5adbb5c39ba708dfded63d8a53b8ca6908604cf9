import Mathlib

/-!
# Mirror of `DASHI/Analysis/ConcreteComplex.agda`

The Agda module is parametric in a constructed real package.  Here that
interface is represented by explicit carrier operations; transcendental data
and its Cartesian law remain structure fields, exactly preserving the authority
boundary.
-/

namespace AgdaMirror.Analysis

/-- The real operations used by the concrete complex-pair construction. -/
structure ConstructedRealOps where
  Real : Type
  zero : Real
  one : Real
  add : Real → Real → Real
  sub : Real → Real → Real
  mul : Real → Real → Real
  neg : Real → Real

/-- A concrete complex number is a pair of values in the constructed real carrier. -/
structure ComplexPair (R : ConstructedRealOps) where
  re : R.Real
  im : R.Real

namespace ComplexPair

variable {R : ConstructedRealOps}

def zeroC : ComplexPair R := ⟨R.zero, R.zero⟩

def oneC : ComplexPair R := ⟨R.one, R.zero⟩

def imaginaryUnit : ComplexPair R := ⟨R.zero, R.one⟩

def addC (z w : ComplexPair R) : ComplexPair R :=
  ⟨R.add z.re w.re, R.add z.im w.im⟩

def subC (z w : ComplexPair R) : ComplexPair R :=
  ⟨R.sub z.re w.re, R.sub z.im w.im⟩

def mulC (z w : ComplexPair R) : ComplexPair R :=
  ⟨R.sub (R.mul z.re w.re) (R.mul z.im w.im),
   R.add (R.mul z.re w.im) (R.mul z.im w.re)⟩

def conjugateC (z : ComplexPair R) : ComplexPair R := ⟨z.re, R.neg z.im⟩

def normSqC (z : ComplexPair R) : R.Real :=
  R.add (R.mul z.re z.re) (R.mul z.im z.im)

/-- The exact extra algebraic laws exposed by the Agda module. -/
structure ComplexAlgebraLaws (R : ConstructedRealOps) : Prop where
  negInvolutive : ∀ x, R.neg (R.neg x) = x
  negZero : R.neg R.zero = R.zero
  subZeroRight : ∀ x, R.sub x R.zero = x
  zeroSub : ∀ x, R.sub R.zero x = R.neg x

theorem conjugateInvolutiveC (laws : ComplexAlgebraLaws R) (z : ComplexPair R) :
    conjugateC (conjugateC z) = z := by
  cases z
  simp [conjugateC, laws.negInvolutive]

/-- A constructed real exponential interface, sufficient for the complex package. -/
structure ConstructedRealExponential (R : ConstructedRealOps) where
  exp : R.Real → R.Real

/-- Sine, cosine, π, complex exponential, and the Cartesian identity are
imported authority fields, not claims derived by this mirror. -/
structure ConstructedComplexExponential
    (R : ConstructedRealOps) (E : ConstructedRealExponential R) where
  sin : R.Real → R.Real
  cos : R.Real → R.Real
  pi : R.Real
  expC : ComplexPair R → ComplexPair R
  expCartesian : ∀ x y,
    expC ⟨x, y⟩ = ⟨R.mul (E.exp x) (cos y), R.mul (E.exp x) (sin y)⟩

/-- Minimal real transcendental package used by the Agda complex package. -/
structure ConstructedRealTranscendentalPackage where
  real : ConstructedRealOps
  exponential : ConstructedRealExponential real

/-- Bundle of constructed real and complex authority surfaces. -/
structure ConstructedComplexPackage where
  realPackage : ConstructedRealTranscendentalPackage
  algebraLaws : ComplexAlgebraLaws realPackage.real
  complexExponential :
    ConstructedComplexExponential realPackage.real realPackage.exponential

end ComplexPair
end AgdaMirror.Analysis
