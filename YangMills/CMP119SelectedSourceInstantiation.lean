import Mathlib
import YangMills.CMP119LiteralResidualSourceDictionary
import YangMills.CMP119PeriodicPolymerReflectionGeometry

/-!
# Selected CMP119 literal source instantiation package

This is the fail-closed Block-C provenance surface.  It requires the actual
selected E/R/B source components, their literal periodic supports and evaluators,
and the already-existing four-sector source-to-literal residual dictionary to
live on one cutoff `2*n` and one literal SU(2) link configuration carrier.

Nothing in this file manufactures an inhabitant.  The current source-native
CMP119 receipt still marks the literal complete-density instantiation
conditional, so construction of this record remains a source-extraction task.
-/

namespace RequestProject.YangMills

/-- Finite source component decomposition for one nonconstant CMP119 sector. -/
structure CMP119SelectedSectorComponents
    (n : ℕ) [NeZero n] where
  Component : Type
  components : Finset Component
  polymerSupport : Component → CMP119PeriodicLinkPolymer n
  evaluate : Component → SU2TorusLinks (2 * n) → ℝ
  sourceSector : SU2TorusLinks (2 * n) → ℝ
  additiveSourceSemantics :
    sourceSector = fun links =>
      ∑ c in components, evaluate c links

namespace CMP119SelectedSectorComponents

/-- Source sector value is literally the sum of the selected source components. -/
theorem source_eq_component_sum
    {n : ℕ} [NeZero n]
    (sector : CMP119SelectedSectorComponents n)
    (links : SU2TorusLinks (2 * n)) :
    sector.sourceSector links =
      ∑ c in sector.components, sector.evaluate c links :=
  congrFun sector.additiveSourceSemantics links

/-- Every selected component carries the already-built literal periodic placement. -/
noncomputable def placement
    {n : ℕ} [NeZero n]
    (sector : CMP119SelectedSectorComponents n)
    (c : sector.Component) : CMP119PolymerPlacement :=
  cmp119PeriodicPolymerPlacement n (sector.polymerSupport c)

end CMP119SelectedSectorComponents

/--
Complete selected-source provenance package on one literal cutoff/carrier.
`residual` owns the exact source-to-literal E/R/B/V equalities and dyadic tail;
the three component dictionaries identify the actual source polymer families
whose sums are those same E/R/B source terms.
-/
structure CMP119SelectedSourceInstantiation
    (n : ℕ) [NeZero n] where
  residual : CMP119LiteralResidualSourceDictionary (2 * n)
  regularE : CMP119SelectedSectorComponents n
  rOperation : CMP119SelectedSectorComponents n
  boundaryB : CMP119SelectedSectorComponents n

  regularSourceSameObject :
    regularE.sourceSector = residual.sourceRegular
  rOperationSourceSameObject :
    rOperation.sourceSector = residual.sourceROperation
  boundarySourceSameObject :
    boundaryB.sourceSector = residual.sourceBoundary

namespace CMP119SelectedSourceInstantiation

/-- Actual selected E source term is its source component sum. -/
theorem regular_source_eq_component_sum
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (links : SU2TorusLinks (2 * n)) :
    source.residual.sourceRegular links =
      ∑ c in source.regularE.components,
        source.regularE.evaluate c links := by
  rw [← source.regularSourceSameObject]
  exact source.regularE.source_eq_component_sum links

/-- Actual selected R-operation source term is its source component sum. -/
theorem r_operation_source_eq_component_sum
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (links : SU2TorusLinks (2 * n)) :
    source.residual.sourceROperation links =
      ∑ c in source.rOperation.components,
        source.rOperation.evaluate c links := by
  rw [← source.rOperationSourceSameObject]
  exact source.rOperation.source_eq_component_sum links

/-- Actual selected boundary source term is its source component sum. -/
theorem boundary_source_eq_component_sum
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (links : SU2TorusLinks (2 * n)) :
    source.residual.sourceBoundary links =
      ∑ c in source.boundaryB.components,
        source.boundaryB.evaluate c links := by
  rw [← source.boundarySourceSameObject]
  exact source.boundaryB.source_eq_component_sum links

/-- Same-object selected literal residual = selected source residual. -/
theorem literal_residual_eq_source
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (links : SU2TorusLinks (2 * n)) :
    su2FullResidual
        source.residual.literalRegular
        source.residual.literalROperation
        source.residual.literalBoundary
        source.residual.literalVacuum links =
      source.residual.sourceResidual links :=
  congrFun source.residual.literalResidualEqSourceResidual links

/-- Once source provenance is populated, all existing dyadic residual machinery is inherited. -/
def toDyadicResidualWeld
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n) :
    CMP119LiteralDyadicResidualWeld (2 * n) :=
  source.residual.toDyadicResidualWeld

/-- Exact Block-C existence proposition; deliberately uninhabited by this file. -/
def CMP119SelectedSourceInstantiationExists : Prop :=
  ∃ (n : ℕ) (_ : NeZero n), Nonempty (CMP119SelectedSourceInstantiation n)

end CMP119SelectedSourceInstantiation

end RequestProject.YangMills
