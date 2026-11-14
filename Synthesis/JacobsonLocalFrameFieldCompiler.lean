import Mathlib
import Synthesis.JacobsonFlat31EinsteinCompiler

namespace Synthesis.JacobsonLocalFrameFieldCompiler

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonCouplingNormalization
open Synthesis.JacobsonClausiusNullAlgebra
open Synthesis.JacobsonFlat31EinsteinCompiler

universe u

/-- Point-indexed Jacobson data after a physical model has chosen local Lorentz
components for one Ricci field and one stress-energy field.

The structure deliberately asks for the **same-object Clausius relation** on
those very contractions for every null direction.  It does not manufacture a
Rindler wedge, a QFT state, entropy-area law, heat-flux identification, or a
continuum frame. Those are the physical inputs this compiler consumes. -/
structure LocalFrameJacobsonData (Point : Type u) where
  hbar : ℝ
  G : ℝ
  hbar_ne : hbar ≠ 0
  G_ne : G ≠ 0
  kappa : Point → ℝ
  kappa_ne : ∀ p, kappa p ≠ 0
  ricci : Point → SymTensor4
  stress : Point → SymTensor4
  clausiusOnEveryNull : ∀ p (v : Vec4), minkowskiQuad v = 0 →
    heatFluxIntegrand (kappa p) (contract (stress p) v) =
      unruhTemperature hbar (kappa p) *
        entropyVariationIntegrand
          (bekensteinHawkingAreaDensity hbar G)
          (contract (ricci p) v)

/-- Pointwise equation-of-state compiler.  All scalar normalization, Clausius
null algebra, and flat 3+1 null-cone rigidity are now composed in one theorem:

  Ricci(p) - 8πG Stress(p) = phi(p) eta.

Only the physical construction of `LocalFrameJacobsonData` remains external. -/
theorem pointwiseRicciStressMetricAmbiguity
    {Point : Type u} (D : LocalFrameJacobsonData Point) (p : Point) :
    ∃ phi : ℝ,
      tensorSubScaled (D.ricci p) (8 * Real.pi * D.G) (D.stress p)
        = metricMultiple phi := by
  exact flat31RicciStressMetricAmbiguity_of_clausius
    (D.ricci p)
    (D.stress p)
    D.hbar
    (D.kappa p)
    D.G
    D.hbar_ne
    (D.kappa_ne p)
    D.G_ne
    (D.clausiusOnEveryNull p)

/-- The recovered metric ambiguity as an actual point-indexed scalar field. -/
noncomputable def recoveredPhiField
    {Point : Type u} (D : LocalFrameJacobsonData Point) : Point → ℝ :=
  fun p => Classical.choose (pointwiseRicciStressMetricAmbiguity D p)

/-- Same-object field equation for the selected Ricci/stress fields at every
point.  Regularity of `recoveredPhiField` is intentionally not inferred from
pointwise choice. -/
theorem recoveredPhiField_spec
    {Point : Type u} (D : LocalFrameJacobsonData Point) (p : Point) :
    tensorSubScaled (D.ricci p) (8 * Real.pi * D.G) (D.stress p)
      = metricMultiple (recoveredPhiField D p) := by
  exact Classical.choose_spec (pointwiseRicciStressMetricAmbiguity D p)

/-- Bundled receipt for downstream Einstein-tensor/Bianchi owners. -/
structure LocalFrameEinsteinFieldReceipt
    {Point : Type u} (D : LocalFrameJacobsonData Point) where
  phi : Point → ℝ
  ricciStressMetricRelation : ∀ p,
    tensorSubScaled (D.ricci p) (8 * Real.pi * D.G) (D.stress p)
      = metricMultiple (phi p)

/-- Canonical field receipt compiled from the supplied physical local-horizon
premises. -/
noncomputable def canonicalLocalFrameEinsteinFieldReceipt
    {Point : Type u} (D : LocalFrameJacobsonData Point) :
    LocalFrameEinsteinFieldReceipt D where
  phi := recoveredPhiField D
  ricciStressMetricRelation := recoveredPhiField_spec D

/-- Status boundary.  The equation-of-state composition is now a single typed
compiler.  Its live leaves are exactly construction/identification of the
physical local Lorentz components, same-object Clausius premises, regularity of
the recovered scalar field, and subsequent global/continuum attachment. -/
def localFrameFieldCompilerOwned : Bool := true

def physicalLocalLorentzFrameIdentificationStillRequired : Bool := true

def physicalClausiusSameObjectReceiptStillRequired : Bool := true

def physicalRicciStressIdentificationStillRequired : Bool := true

def recoveredPhiRegularityStillRequired : Bool := true

def continuumGlobalAttachmentStillRequired : Bool := true

end Synthesis.JacobsonLocalFrameFieldCompiler
