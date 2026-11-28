import Integration.Paper9ThetaEisensteinSameObject

/-! Classical Jacobi quartic identity via signed modular residual rigidity.
DASHI attachment: retain the orientation character, then apply the existing
weight-four cusp-zero consumer to its square. Independent of shell counts.
SOURCE-WRITTEN, local kernel pending. -/
namespace Integration.Paper9ThetaAnalyticJacobi
open Complex Filter Function UpperHalfPlane ModularGroup ModularForm
open SlashInvariantForm SlashInvariantFormClass ModularFormClass
open scoped MatrixGroups Real Topology Manifold
open Integration.Paper9ThetaModularTransport
open Integration.Paper9ThetaCuspNormalization
open Integration.Paper9ThetaEisensteinSameObject
noncomputable section

def residual (z : ℂ) := B z - A z - C z
def residualSquare (z : ℂ) := residual z ^ 2

theorem residualS (z : ℂ) (hz : z ≠ 0) :
    residual (-1/z) = -z^2 * residual z := by
  obtain ⟨ha,hb,hc⟩ := sheetsS z hz
  unfold residual
  rw [ha,hb,hc]
  ring

theorem residualT (z : ℂ) : residual (z+1) = -residual z := by
  obtain ⟨ha,hb,hc⟩ := sheetsT z
  unfold residual
  rw [ha,hb,hc]
  ring

theorem squareS (z : ℂ) (hz : z ≠ 0) :
    residualSquare (-1/z) = z^4 * residualSquare z := by
  unfold residualSquare
  rw [residualS z hz]
  ring

theorem squareT (z : ℂ) : residualSquare (z+1) = residualSquare z := by
  unfold residualSquare
  rw [residualT]
  ring

theorem squareDifferentiable (z : ℍ) :
    DifferentiableAt ℂ residualSquare (z:ℂ) := by
  have ha := (th2Differentiable z).pow 4
  have hb := (th3Differentiable z).pow 4
  have hc := (th4Differentiable z).pow 4
  unfold residualSquare residual A B C
  exact ((hb.sub ha).sub hc).pow 2

theorem residualLimit :
    Tendsto (fun z : ℍ => residual z) atImInfty (𝓝 0) := by
  have ha := th2Limit.pow 4
  have hb := th3Limit.pow 4
  have hc := th4Limit.pow 4
  simpa [residual,A,B,C] using (hb.sub ha).sub hc

theorem squareLimit :
    Tendsto (fun z : ℍ => residualSquare z) atImInfty (𝓝 0) := by
  simpa [residualSquare] using residualLimit.pow 2

theorem squareSlash (γ : SL(2,ℤ)) :
    (fun z : ℍ => residualSquare z) ∣[(4:ℤ)] γ =
      fun z : ℍ => residualSquare z :=
  slashFromST residualSquare 4 (fun z => squareS z z.ne_zero)
    (fun z => squareT z) γ

def residualCusp : CuspForm 𝒮ℒ 4 where
  toFun z := residualSquare z
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ squareSlash γ
  holo' := thetaHolo residualSquare squareDifferentiable
  zero_at_cusps' {c} hc γ hγ := by
    rw [squareSlash γ]
    rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
    exact squareLimit

theorem residualZero (z : ℍ) : residual z = 0 := by
  have h : residual z ^ 2 = 0 :=
    cuspZero residualCusp (by norm_num) (by norm_num) z
  by_contra hn
  exact (pow_ne_zero 2 hn) h

theorem analyticJacobi (z : ℍ) : B z = A z + C z := by
  have h := residualZero z
  unfold residual at h
  linear_combination h

-- Reattach the original two-coordinate Legendre polynomial and
-- its oriented discriminant to the very same analytic E4/E6.
theorem originalE4Legendre (z : ℍ) :
    Integration.MoonshineEisensteinAnalytic.E4 z =
      A z^2 - A z * B z + B z^2 := by
  rw [← thetaE4_eq_original]
  have hc : C z = B z - A z := by
    linear_combination -(analyticJacobi z)
  unfold thetaE4
  rw [hc]
  ring

theorem originalE6Legendre (z : ℍ) :
    2 * Integration.MoonshineEisensteinAnalytic.E6 z =
      (A z+B z)*(2*A z-B z)*(A z-2*B z) := by
  rw [← thetaE6_eq_original]
  have hc : C z = B z - A z := by
    linear_combination -(analyticJacobi z)
  unfold thetaE6
  rw [hc]
  ring

theorem originalDiscriminantLegendre (z : ℍ) :
    4 * (Integration.MoonshineEisensteinAnalytic.E4 z ^ 3 -
      Integration.MoonshineEisensteinAnalytic.E6 z ^ 2) =
      27 * (A z * B z * (B z - A z)) ^ 2 := by
  have h : Integration.MoonshineEisensteinAnalytic.E6 z =
      (A z+B z)*(2*A z-B z)*(A z-2*B z)/2 := by
    linear_combination (1/2:ℂ) * originalE6Legendre z
  rw [originalE4Legendre,h]
  ring

#print axioms analyticJacobi
#print axioms originalE4Legendre
#print axioms originalE6Legendre
#print axioms originalDiscriminantLegendre
end
end Integration.Paper9ThetaAnalyticJacobi
