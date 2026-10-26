import Mathlib

namespace Synthesis.JacobsonBianchiCosmologicalConstancy

/-- Differential data needed only after the pointwise Einstein-tensor algebra.
The same-object geometry/QFT model must supply these divergence/gradient laws. -/
structure BianchiConstancyData (Point Index : Type*) where
  coupling : ℝ
  divRicci : Point → Index → ℝ
  gradScalarCurvature : Point → Index → ℝ
  divStress : Point → Index → ℝ
  gradPhi : Point → Index → ℝ
  contractedBianchi : ∀ p ν,
    divRicci p ν = gradScalarCurvature p ν / 2
  stressConservation : ∀ p ν,
    divStress p ν = 0
  divergenceOfRecoveredRelation : ∀ p ν,
    divRicci p ν - coupling * divStress p ν = gradPhi p ν

/-- Bianchi plus stress conservation force the gradient of
Λ = R/2 - phi to vanish componentwise. -/
theorem lambdaGradientZero
    {Point Index : Type*}
    (D : BianchiConstancyData Point Index)
    (p : Point) (ν : Index) :
    D.gradScalarCurvature p ν / 2 - D.gradPhi p ν = 0 := by
  have hB := D.contractedBianchi p ν
  have hT := D.stressConservation p ν
  have hR := D.divergenceOfRecoveredRelation p ν
  linarith

/-- Final topological/differential integration surface.  On the selected domain,
a concrete model must prove that a scalar field with vanishing differential is
constant (e.g. on each connected component). -/
structure ZeroGradientConstancySurface (Point Index : Type*) where
  lambdaField : Point → ℝ
  Derivative : (Point → ℝ) → Point → Index → ℝ
  derivativeMatchesLambdaGradient : ∀ p ν,
    Derivative lambdaField p ν = 0
  zeroDerivativeImpliesConstant :
    ∀ f : Point → ℝ,
      (∀ p ν, Derivative f p ν = 0) →
      ∃ Λ : ℝ, ∀ p, f p = Λ

/-- Exact integration compiler once the selected domain supplies the
zero-gradient-to-constant theorem. -/
theorem lambdaIsConstant
    {Point Index : Type*}
    (C : ZeroGradientConstancySurface Point Index) :
    ∃ Λ : ℝ, ∀ p, C.lambdaField p = Λ :=
  C.zeroDerivativeImpliesConstant C.lambdaField C.derivativeMatchesLambdaGradient

/-- Status boundary. -/
def bianchiLambdaGradientCompilerOwned : Bool := true

def lambdaConstancyCompilerOwned : Bool := true

def zeroGradientToGlobalConstantStillRequired : Bool := true

def physicalBianchiStressReceiptsStillRequired : Bool := true

def connectedDomainOrComponentChoiceStillRequired : Bool := true

end Synthesis.JacobsonBianchiCosmologicalConstancy
