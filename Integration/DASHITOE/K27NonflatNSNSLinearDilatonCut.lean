import Mathlib

/-!
# 26D coupled nonflat NS-NS string beta equations: selected SU(2) flux profile

PRIOR PHYSICS: round SU(2) group manifold with bi-invariant metric,
closed H3=(2/r) vol(S3), spacelike linear dilaton slope |grad Phi|=1/r.
Spacetime is R^(1,22) × S3, total dimension 26. This is a standard
WZW/linear-dilaton leading-alpha-prime effective background, not novel
physics. Source: 26D string-frame action R+4(dPhi)^2-H^2/12 and SU(2)_k
Sugawara c=3k/(k+2).

These statements use the real geometric identities as EXTERNALLY
GROUNDED inputs (Ric_S3=2/r² g, H_ijk=2/r eps_ijk, H parallel).
Only their general reciprocal-radius coefficient and worldsheet-charge
consequences are proved by the Lean kernel if built. No manifold,
gerbe, K27 generators, string vertex algebra or quantum beta-functions
are constructed by this file.
-/
namespace DASHIK27NonflatNSNS

/-- Reciprocal round-sphere radius; for r>0 set u=1/r. -/
def sphereRicciCoeff (u : ℚ) : ℚ := 2 * u ^ 2

/-- Contraction H_iab H_j^ab for H=(2/r)vol_S3 in orthonormal frame. -/
def sphereFluxTensorCoeff (u : ℚ) : ℚ := 8 * u ^ 2

def sphereScalarCurvature (u : ℚ) : ℚ := 6 * u ^ 2

/-- Normalisation H_ijk H^ijk for H=(2/r)vol_S3. -/
def sphereFluxNormSquared (u : ℚ) : ℚ := 24 * u ^ 2

def spacelikeDilatonGradientSquared (u : ℚ) : ℚ := u ^ 2

/-- The S3 components of R_ij+2 Hess(Phi)_ij -H_iab H_j^ab/4.
Hess(Phi) is zero when Phi is linear on the separate flat factor. -/
theorem sphereMetricBetaZero (u : ℚ) :
    sphereRicciCoeff u - sphereFluxTensorCoeff u / 4 = 0 := by
  dsimp [sphereRicciCoeff, sphereFluxTensorCoeff]
  ring

/-- Full D=26 dilaton equation R+4 Delta(Phi)-4|grad Phi|²-H²/12,
where Delta(Phi)=0 and all other Ricci components are flat. -/
theorem fullDilatonBetaZero (u : ℚ) :
    sphereScalarCurvature u
      - 4 * spacelikeDilatonGradientSquared u
      - sphereFluxNormSquared u / 12 = 0 := by
  dsimp [sphereScalarCurvature, spacelikeDilatonGradientSquared,
    sphereFluxNormSquared]
  ring

/-- A timelike linear dilaton of the same magnitude has the WRONG sign
to close this selected 26D dilaton equation. -/
theorem timelikeGradientNotSolution (u : ℚ) (hu : u ≠ 0) :
    sphereScalarCurvature u + 4 * u ^ 2 -
      sphereFluxNormSquared u / 12 ≠ 0 := by
  dsimp [sphereScalarCurvature, sphereFluxNormSquared]
  nlinarith [sq_pos_of_ne_zero hu]

/-- Worldsheet Sugawara central charge, independently known for SU(2)_k. -/
def su2WorldsheetCentralCharge (k : ℚ) : ℚ := 3 * k / (k + 2)

/-- 23 noncompact bosons, one with a spacelike linear-dilaton background
charge. Conformal cancellation requires alphaPrime * V²=1/(k+2). -/
theorem exactMatterCentralCharge (k : ℚ) (hk : k + 2 ≠ 0) :
    23 + 6 / (k + 2) + su2WorldsheetCentralCharge k = 26 := by
  dsimp [su2WorldsheetCentralCharge]
  field_simp
  ring

/-- Selected large-k CLASSICAL radius relation alphaPrime*V²=1/k
does not already equal the exact Sugawara worldsheet requirement.
This is the precise finite-k central-charge residual. -/
theorem unshiftedSlopeAnomaly (k : ℚ) (hk : k ≠ 0)
    (hkp : k + 2 ≠ 0) :
    (23 + 6 / k + su2WorldsheetCentralCharge k) - 26 =
      12 / (k * (k + 2)) := by
  dsimp [su2WorldsheetCentralCharge]
  field_simp
  ring

end DASHIK27NonflatNSNS
