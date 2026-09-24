import Mathlib
import AgdaMirror.AdK.COMGeometry

/-!
# Exact AdK three-CV input surface

The theorem-bearing surface stops before transcendental angle evaluation.
Theta1/theta2 retain the exact COM triples fed to a deterministic angle
evaluator; dLN retains its two exact COMs and can expose exact squared distance.

This is enough for same-object/mirror equality: equal exact COM inputs force any
shared deterministic downstream evaluator to receive equal arguments.  No `acos`
or floating-point oracle is needed to prove that fact.
-/

namespace AgdaMirror.AdK.CVProjection

open AgdaMirror.AdK.AtomisticConfiguration
open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CanonicalSelectionContent
open AgdaMirror.AdK.COMGeometry

/-- Eight logical selected-content positions used by the source-facing three-CV
surface.  Hinge/core are intentionally repeated because they occupy different
angle positions even though they resolve to the same selection specifications. -/
structure ThreeCVContentSurface where
  theta1First : CanonicalSelectionContent
  theta1Vertex : CanonicalSelectionContent
  theta1Third : CanonicalSelectionContent
  theta2First : CanonicalSelectionContent
  theta2Vertex : CanonicalSelectionContent
  theta2Third : CanonicalSelectionContent
  dlnFirst : CanonicalSelectionContent
  dlnSecond : CanonicalSelectionContent
  deriving DecidableEq, Repr

def threeCVContentSurface
    (configuration : Configuration)
    (dlnPolicy : AtomPolicy) : ThreeCVContentSurface :=
  { theta1First := canonicalContent configuration theta1Lid
    theta1Vertex := canonicalContent configuration hinge
    theta1Third := canonicalContent configuration core
    theta2First := canonicalContent configuration theta2Nmp
    theta2Vertex := canonicalContent configuration core
    theta2Third := canonicalContent configuration hinge
    dlnFirst := canonicalContent configuration (dlnLid dlnPolicy)
    dlnSecond := canonicalContent configuration (dlnNmp dlnPolicy) }

structure AngleCOMTriple where
  first : Option Vec3Q
  vertex : Option Vec3Q
  third : Option Vec3Q
  deriving DecidableEq, Repr

structure ThreeCVInputSurface where
  theta1 : AngleCOMTriple
  theta2 : AngleCOMTriple
  dlnFirst : Option Vec3Q
  dlnSecond : Option Vec3Q
  deriving DecidableEq, Repr

/-- Pure exact COM projection of the transparent eight-position content packet. -/
def ThreeCVContentSurface.toInput
    (surface : ThreeCVContentSurface) : ThreeCVInputSurface :=
  { theta1 :=
      { first := centerOfMass? surface.theta1First
        vertex := centerOfMass? surface.theta1Vertex
        third := centerOfMass? surface.theta1Third }
    theta2 :=
      { first := centerOfMass? surface.theta2First
        vertex := centerOfMass? surface.theta2Vertex
        third := centerOfMass? surface.theta2Third }
    dlnFirst := centerOfMass? surface.dlnFirst
    dlnSecond := centerOfMass? surface.dlnSecond }

def threeCVInputSurface
    (configuration : Configuration)
    (dlnPolicy : AtomPolicy) : ThreeCVInputSurface :=
  (threeCVContentSurface configuration dlnPolicy).toInput

/-- Equality of the transparent content surface is sufficient for equality of
all exact COM inputs to the three CVs. -/
theorem threeCVInput_eq_of_content_surface_eq
    {q₁ q₂ : Configuration}
    {dlnPolicy : AtomPolicy}
    (h : threeCVContentSurface q₁ dlnPolicy =
      threeCVContentSurface q₂ dlnPolicy) :
    threeCVInputSurface q₁ dlnPolicy = threeCVInputSurface q₂ dlnPolicy :=
  congrArg ThreeCVContentSurface.toInput h

/-- Fieldwise selected-content equality compiles to the complete eight-position
content-surface equality. -/
theorem threeCVContentSurface_eq_of_fields
    {q₁ q₂ : Configuration}
    {dlnPolicy : AtomPolicy}
    (hTheta1Lid : canonicalContent q₁ theta1Lid = canonicalContent q₂ theta1Lid)
    (hHinge : canonicalContent q₁ hinge = canonicalContent q₂ hinge)
    (hCore : canonicalContent q₁ core = canonicalContent q₂ core)
    (hTheta2Nmp : canonicalContent q₁ theta2Nmp = canonicalContent q₂ theta2Nmp)
    (hDlnLid : canonicalContent q₁ (dlnLid dlnPolicy) =
      canonicalContent q₂ (dlnLid dlnPolicy))
    (hDlnNmp : canonicalContent q₁ (dlnNmp dlnPolicy) =
      canonicalContent q₂ (dlnNmp dlnPolicy)) :
    threeCVContentSurface q₁ dlnPolicy = threeCVContentSurface q₂ dlnPolicy := by
  apply ThreeCVContentSurface.ext <;> assumption

/-- Fieldwise transparent selected-content equality therefore gives equality of
all exact three-CV inputs. -/
theorem threeCVInput_eq_of_content_eq
    {q₁ q₂ : Configuration}
    {dlnPolicy : AtomPolicy}
    (hTheta1Lid : canonicalContent q₁ theta1Lid = canonicalContent q₂ theta1Lid)
    (hHinge : canonicalContent q₁ hinge = canonicalContent q₂ hinge)
    (hCore : canonicalContent q₁ core = canonicalContent q₂ core)
    (hTheta2Nmp : canonicalContent q₁ theta2Nmp = canonicalContent q₂ theta2Nmp)
    (hDlnLid : canonicalContent q₁ (dlnLid dlnPolicy) =
      canonicalContent q₂ (dlnLid dlnPolicy))
    (hDlnNmp : canonicalContent q₁ (dlnNmp dlnPolicy) =
      canonicalContent q₂ (dlnNmp dlnPolicy)) :
    threeCVInputSurface q₁ dlnPolicy = threeCVInputSurface q₂ dlnPolicy :=
  threeCVInput_eq_of_content_surface_eq
    (threeCVContentSurface_eq_of_fields
      hTheta1Lid hHinge hCore hTheta2Nmp hDlnLid hDlnNmp)

/-- Exact squared distance; no square root is needed for the equality theorem. -/
def distanceSq (a b : Vec3Q) : ℚ :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  let dz := a.z - b.z
  dx * dx + dy * dy + dz * dz

/-- A deterministic downstream angle evaluator receives equal inputs whenever
this Lean theorem gives equal `AngleCOMTriple`s.  Numeric `acos` evaluation is
intentionally outside the theorem-bearing spine. -/
def transcendentalAngleEvaluationPaidHere : Bool := false

example : transcendentalAngleEvaluationPaidHere = false := rfl

end AgdaMirror.AdK.CVProjection
