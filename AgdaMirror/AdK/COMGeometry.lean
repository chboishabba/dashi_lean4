import Mathlib
import AgdaMirror.AdK.CanonicalSelectionContent

/-!
# Exact mass-weighted COM geometry

`centerOfMass?` is a pure function of transparent canonical selected content.
All arithmetic is over `ℚ`.  The `Option` result keeps empty/zero-total-mass
content explicit rather than manufacturing a center of mass.

The core extensionality theorem is therefore ordinary function congruence:
canonical-content equality gives COM equality without an externally supplied
physics/provenance witness.
-/

namespace AgdaMirror.AdK.COMGeometry

open AgdaMirror.AdK.AtomisticConfiguration
open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CanonicalSelectionContent

def sumMass (rows : CanonicalSelectionContent) : ℚ :=
  (rows.map fun row => row.mass).sum

def weightedX (rows : CanonicalSelectionContent) : ℚ :=
  (rows.map fun row => row.mass * row.position.x).sum

def weightedY (rows : CanonicalSelectionContent) : ℚ :=
  (rows.map fun row => row.mass * row.position.y).sum

def weightedZ (rows : CanonicalSelectionContent) : ℚ :=
  (rows.map fun row => row.mass * row.position.z).sum

/-- Exact mass-weighted center of mass over the adopted rational carrier. -/
def centerOfMass? (rows : CanonicalSelectionContent) : Option Vec3Q :=
  let total := sumMass rows
  if total = 0 then
    none
  else
    some
      { x := weightedX rows / total
        y := weightedY rows / total
        z := weightedZ rows / total }

/-- Direct content equality is sufficient for COM equality. -/
theorem centerOfMass_congr
    {left right : CanonicalSelectionContent}
    (h : left = right) :
    centerOfMass? left = centerOfMass? right :=
  congrArg centerOfMass? h

/-- Configuration/selection-facing extensionality used by the CV layer. -/
theorem canonicalContent_centerOfMass_congr
    {q₁ q₂ : Configuration}
    {selection : SelectionSpec}
    (h : canonicalContent q₁ selection = canonicalContent q₂ selection) :
    centerOfMass? (canonicalContent q₁ selection) =
      centerOfMass? (canonicalContent q₂ selection) :=
  congrArg centerOfMass? h

/-- A missing selection remains missing; no arbitrary zero vector is fabricated. -/
example :
    centerOfMass? (Multiset.ofList ([] : List CanonicalAtomRow)) = none := by
  rfl

end AgdaMirror.AdK.COMGeometry
