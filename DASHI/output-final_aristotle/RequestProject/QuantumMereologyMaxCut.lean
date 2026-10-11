import RequestProject.QuantumMereologySchwingerObjective
import RequestProject.QuantumMereologySelection

/-!
# Quantum mereology selected-TPS max-cut

This module composes the already-owned source-shaped Schwinger selection with
factor-relation geometry without manufacturing any missing physical producer.

The same selected candidate indexes the tensor-product structure consumed by the
downstream geometry.  A criterion collision that changes a declared
geometry-sensitive consumer is then an ordinary `CriterionCollision`, so the
existing consumer-sufficiency, factorisation and mandatory-refinement-separation
theorems apply directly.

The Lean lane currently stops at spatial geometry.  The Agda lane has a typed
spatial-geometry -> spacetime promotion owner; no such Lean owner is silently
invented here.
-/

namespace QuantumMereology
namespace MaxCut

structure SelectedSchwingerSpatialPipeline
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    (D : SchwingerObjective.SearchData W PointerInit) where
  selectionReceipt : PreferredTPSSelectionReceipt D.selectionProblem
  state : W.State
  geometry : FactorRelationGeometry W (D.realizes selectionReceipt.selected)

def selectedTPS
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    (P : SelectedSchwingerSpatialPipeline D) : TensorProductStructure W :=
  D.realizes P.selectionReceipt.selected

theorem selected_minimizes_schwinger_score
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    (P : SelectedSchwingerSpatialPipeline D)
    (other : D.Candidate)
    (hOther : D.Admissible other) :
    D.score P.selectionReceipt.selected ≤ D.score other :=
  SchwingerObjective.SearchData.selected_minimizes_schwinger_score
    D P.selectionReceipt other hOther

def selectedEmergentGeometry
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    (P : SelectedSchwingerSpatialPipeline D) : P.geometry.Geometry :=
  emergentGeometry P.geometry P.state

/-! ## Geometry-sensitive consumer descent -/

structure GeometryCriterionConsumer
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    (D : SchwingerObjective.SearchData W PointerInit) where
  Surface : Type
  Outcome : Type
  observeCriterion : D.Candidate → Surface
  geometryOutcome : D.Candidate → Outcome

namespace GeometryCriterionConsumer

def asSurface
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    (G : GeometryCriterionConsumer D) :
    CriterionConsumerSurface D.selectionProblem where
  Surface := G.Surface
  Outcome := G.Outcome
  observeCriterion := G.observeCriterion
  consumer := G.geometryOutcome

end GeometryCriterionConsumer

def GeometryCriterionCollision
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    (G : GeometryCriterionConsumer D) : Prop :=
  CriterionCollision G.asSurface

theorem geometryCriterionCollisionBlocksSufficiency
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    {G : GeometryCriterionConsumer D}
    (collision : GeometryCriterionCollision G) :
    ¬ G.asSurface.Sufficient :=
  criterionCollisionBlocksConsumerSufficiency collision

theorem geometryCriterionCollisionBlocksFactorisation
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    {G : GeometryCriterionConsumer D}
    (collision : GeometryCriterionCollision G) :
    ¬ Nonempty (CriterionFactorisation G.asSurface) :=
  criterionCollisionBlocksFactorisation collision

theorem geometryCriterionCollisionForcesSeparationInEveryRepair
    {W : BareQuantumWorld}
    {PointerInit : Type*}
    [Fintype PointerInit] [Nonempty PointerInit]
    {D : SchwingerObjective.SearchData W PointerInit}
    {G : GeometryCriterionConsumer D}
    {Refinement : Type}
    {refine : D.Candidate → Refinement}
    (collision : GeometryCriterionCollision G)
    (repair : CriterionRefinementRepair G.asSurface Refinement refine) :
    refine collision.left ≠ refine collision.right :=
  criterionCollisionForcesSeparationInEveryRepair collision repair

/-! ## Fail-closed terminal boundary -/

structure Boundary where
  sourceWrittenProducerCreatesSelection : Bool := false
  selectedTPSCreatesGeometryWithoutPairRelation : Bool := false
  spatialGeometryCreatesSpacetime : Bool := false
  currentLeanOwnsTypedSpacetimePromotion : Bool := false
  geometryCriterionCollisionCreatesRefinementObligation : Bool := true
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem source_written_producer_does_not_create_selection :
    canonicalBoundary.sourceWrittenProducerCreatesSelection = false := rfl

theorem selected_tps_does_not_create_geometry_without_pair_relation :
    canonicalBoundary.selectedTPSCreatesGeometryWithoutPairRelation = false := rfl

theorem spatial_geometry_does_not_create_spacetime :
    canonicalBoundary.spatialGeometryCreatesSpacetime = false := rfl

theorem current_lean_has_no_typed_spacetime_promotion_owner :
    canonicalBoundary.currentLeanOwnsTypedSpacetimePromotion = false := rfl

theorem geometry_collision_creates_refinement_obligation :
    canonicalBoundary.geometryCriterionCollisionCreatesRefinementObligation = true := rfl

def dashiQuantumMereologyMaxCutReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI"
  claim := "Composes the source-shaped Schwinger minimizer theorem, exact selected-TPS indexing, factor-relation geometry, and geometry-sensitive consumer collision/refinement theorems. It creates no minimizer, CPO eigenprojector, pair-relation law, spacetime promotion, Einstein dynamics, or empirical authority."

end MaxCut
end QuantumMereology
