import Mathlib
import Synthesis.JacobsonLocalFrameFieldCompiler

namespace Synthesis.JacobsonLocalFrameEinsteinLambda

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonFlat31EinsteinCompiler
open Synthesis.JacobsonLocalFrameFieldCompiler

universe u

/-- Minkowski trace of a symmetric Ricci tensor in the selected local Lorentz
frame, signature (-,+,+,+). -/
def scalarCurvatureFlat (ricci : SymTensor4) : ℝ :=
  -ricci.tt + ricci.xx + ricci.yy + ricci.zz

/-- Einstein tensor in the same local Lorentz frame:
`G_ab = R_ab - (1/2) R eta_ab`. -/
def einsteinTensor4 (ricci : SymTensor4) : SymTensor4 where
  tt := ricci.tt + scalarCurvatureFlat ricci / 2
  tx := ricci.tx
  ty := ricci.ty
  tz := ricci.tz
  xx := ricci.xx - scalarCurvatureFlat ricci / 2
  xy := ricci.xy
  xz := ricci.xz
  yy := ricci.yy - scalarCurvatureFlat ricci / 2
  yz := ricci.yz
  zz := ricci.zz - scalarCurvatureFlat ricci / 2

/-- Add `Lambda eta_ab` to the local-frame Einstein tensor. -/
def einsteinPlusLambda (ricci : SymTensor4) (Lambda : ℝ) : SymTensor4 where
  tt := (einsteinTensor4 ricci).tt - Lambda
  tx := (einsteinTensor4 ricci).tx
  ty := (einsteinTensor4 ricci).ty
  tz := (einsteinTensor4 ricci).tz
  xx := (einsteinTensor4 ricci).xx + Lambda
  xy := (einsteinTensor4 ricci).xy
  xz := (einsteinTensor4 ricci).xz
  yy := (einsteinTensor4 ricci).yy + Lambda
  yz := (einsteinTensor4 ricci).yz
  zz := (einsteinTensor4 ricci).zz + Lambda

/-- Scalar multiple of a symmetric tensor. -/
def scaledTensor (C : ℝ) (T : SymTensor4) : SymTensor4 where
  tt := C * T.tt
  tx := C * T.tx
  ty := C * T.ty
  tz := C * T.tz
  xx := C * T.xx
  xy := C * T.xy
  xz := C * T.xz
  yy := C * T.yy
  yz := C * T.yz
  zz := C * T.zz

/-- Exact local-frame conversion from the null-cone-recovered metric ambiguity

  Ricci - C Stress = phi eta

to

  Einstein + Lambda eta = C Stress,
  Lambda = R/2 - phi.

No Bianchi identity, conservation law, differentiability, or global geometry is
used here. -/
theorem einsteinLambda_of_metricAmbiguity
    (ricci stress : SymTensor4) (C phi : ℝ)
    (h : tensorSubScaled ricci C stress = metricMultiple phi) :
    einsteinPlusLambda ricci (scalarCurvatureFlat ricci / 2 - phi)
      = scaledTensor C stress := by
  have htt := congrArg SymTensor4.tt h
  have htx := congrArg SymTensor4.tx h
  have hty := congrArg SymTensor4.ty h
  have htz := congrArg SymTensor4.tz h
  have hxx := congrArg SymTensor4.xx h
  have hxy := congrArg SymTensor4.xy h
  have hxz := congrArg SymTensor4.xz h
  have hyy := congrArg SymTensor4.yy h
  have hyz := congrArg SymTensor4.yz h
  have hzz := congrArg SymTensor4.zz h
  simp [tensorSubScaled, metricMultiple] at htt htx hty htz hxx hxy hxz hyy hyz hzz
  ext <;>
    simp [einsteinPlusLambda, einsteinTensor4, scaledTensor, scalarCurvatureFlat] <;>
    linarith [htt, htx, hty, htz, hxx, hxy, hxz, hyy, hyz, hzz]

/-- Point-indexed cosmological coefficient produced from the same Ricci field and
same recovered `phi` field of `JacobsonLocalFrameFieldCompiler`. -/
noncomputable def recoveredLambdaField
    {Point : Type u} (D : LocalFrameJacobsonData Point) : Point → ℝ :=
  fun p => scalarCurvatureFlat (D.ricci p) / 2 - recoveredPhiField D p

/-- Pointwise Einstein equation for the **same** Ricci and stress fields carried
by `LocalFrameJacobsonData`:

  G_ab(p) + Lambda(p) eta_ab = 8 pi G T_ab(p).

The remaining constancy/global step is therefore differential/geometric, not
missing tensor algebra. -/
theorem recoveredLambdaField_spec
    {Point : Type u} (D : LocalFrameJacobsonData Point) (p : Point) :
    einsteinPlusLambda (D.ricci p) (recoveredLambdaField D p)
      = scaledTensor (8 * Real.pi * D.G) (D.stress p) := by
  apply einsteinLambda_of_metricAmbiguity
  exact recoveredPhiField_spec D p

/-- Status boundary. -/
def localFrameEinsteinLambdaCompilerOwned : Bool := true

def pointwiseEinsteinEquationOwnedGivenPhysicalPackage : Bool := true

def bianchiStressConservationStillRequired : Bool := true

def recoveredLambdaRegularityStillRequired : Bool := true

def physicalManifoldAttachmentStillRequired : Bool := true

def empiricalValidationStillRequired : Bool := true

end Synthesis.JacobsonLocalFrameEinsteinLambda
