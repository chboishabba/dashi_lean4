import Synthesis.JacobsonNullConeRigidityTransport

namespace Synthesis.JacobsonFibrewiseFrameAssembly

open Synthesis.JacobsonNullConeRigidityTransport

universe u v w

/-- Point-indexed family of Lorentz-frame transports and field-equation defects.
At each point the physical application supplies one same-object tangent/vector
carrier, one symmetric-tensor carrier, a Lorentz-frame equivalence, and the
null-contracted vanishing relation for the selected defect tensor. -/
structure FibrewiseLorentzData (Point : Type u) where
  V : Point → Type v
  Tensor : Point → Type w
  frame : ∀ p, LorentzFrameTransport (V p) (Tensor p)
  defect : ∀ p, Tensor p
  invisibleOnNull : ∀ p (v : V p),
    (frame p).quad v = 0 →
    (frame p).contraction (defect p) v = 0

/-- Pointwise null-cone rigidity receipt obtained by transporting the concrete
flat 3+1 theorem through the supplied local frame at `p`. -/
theorem pointwiseMetricMultiple
    {Point : Type u} (D : FibrewiseLorentzData Point) (p : Point) :
    ∃ phi : ℝ, D.defect p = (D.frame p).metricMultipleV phi := by
  exact rigidityTransportedThroughFrame
    (D.frame p)
    (D.defect p)
    (D.invisibleOnNull p)

/-- The recovered pointwise metric coefficient as an actual scalar field.
Choice is used only to select the already-proved existential coefficient at
each point; no smoothness or physical calibration is manufactured. -/
noncomputable def recoveredPhi
    {Point : Type u} (D : FibrewiseLorentzData Point) : Point → ℝ :=
  fun p => Classical.choose (pointwiseMetricMultiple D p)

/-- Exact fibrewise assembly: the selected defect tensor equals the local metric
multiple of the recovered coefficient at every point. -/
theorem defect_eq_metricMultiple_recoveredPhi
    {Point : Type u} (D : FibrewiseLorentzData Point) (p : Point) :
    D.defect p = (D.frame p).metricMultipleV (recoveredPhi D p) := by
  exact Classical.choose_spec (pointwiseMetricMultiple D p)

/-- Bundled field-level receipt useful for downstream Einstein/Lambda owners. -/
structure FibrewiseMetricAmbiguityReceipt
    {Point : Type u} (D : FibrewiseLorentzData Point) where
  phiField : Point → ℝ
  defectIsMetricMultiple : ∀ p,
    D.defect p = (D.frame p).metricMultipleV (phiField p)

/-- Canonical receipt compiled from local transported rigidity. -/
noncomputable def canonicalFibrewiseMetricAmbiguityReceipt
    {Point : Type u} (D : FibrewiseLorentzData Point) :
    FibrewiseMetricAmbiguityReceipt D where
  phiField := recoveredPhi D
  defectIsMetricMultiple := defect_eq_metricMultiple_recoveredPhi D

/-- Status boundary.  Pointwise assembly into a scalar field is paid, while a
physical smooth frame field, differentiability/regularity of the recovered
coefficient, and identification with the physical Ricci/stress tensors remain
independent same-object continuum receipts. -/
def fibrewisePointwiseAssemblyOwned : Bool := true

def physicalFrameFieldConstructionStillRequired : Bool := true

def recoveredPhiSmoothnessStillRequired : Bool := true

def recoveredPhiDifferentiabilityStillRequired : Bool := true

def physicalRicciStressFieldIdentificationStillRequired : Bool := true

def globalFrameTrivializationNotRequired : Bool := true

end Synthesis.JacobsonFibrewiseFrameAssembly
