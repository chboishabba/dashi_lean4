import Integration.RationalAlbertCubicRigidity
import Integration.TeleodynamicsExceptionalLieExperiment

/-!
# Teleodynamics / LILA exceptional cubic-structure experiment adapter

Finite Weyl fit, Lie-generator fit and Albert cubic/Jordan fit answer different
questions.  This owner adds the strongest algebraic layer currently available
on the literal rational Albert carrier.

The experiment ladder is:

root/codebook alignment
< finite Weyl action
< infinitesimal Lie action
< cubic preservation
< unit fixation
< adjoint/cross compatibility
< Jordan-product compatibility
< rational-form/group recognition
< empirical mechanism/target realization.

No earlier layer manufactures a later one.
-/

namespace Integration.TeleodynamicsExceptionalCubicExperiment

open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertNative
open RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

structure ExceptionalCubicAssay where
  cubicResidualMeasured : Bool
  unitResidualMeasured : Bool
  traceResidualMeasured : Bool
  tracePairResidualMeasured : Bool
  adjointResidualMeasured : Bool
  crossResidualMeasured : Bool
  jordanResidualMeasured : Bool
  heldOutCompositionMeasured : Bool
  decoderCompatibilityMeasured : Bool
  futureConsumerMeasured : Bool
  deriving Repr

/-- Exact model-facing projection intertwiner for one native cubic-norm
automorphism.  This is a mathematical receipt, not an empirical claim that any
real model supplies it. -/
structure AlbertProjectionIntertwiner {X : Type*}
    (project : X → A27) (intervention : X → X)
    (g : CubicNormAutomorphism) : Prop where
  intertwines : ∀ x, project (intervention x) = g.forward (project x)

/-- If a model projection exactly intertwines a native cubic-norm automorphism,
then its projected Jordan product transforms equivariantly as well. -/
theorem projectedJordanEquivariance
    {X : Type*} {project : X → A27} {intervention : X → X}
    (g : CubicNormAutomorphism)
    (h : AlbertProjectionIntertwiner project intervention g)
    (x y : X) :
    jordanProduct (project (intervention x)) (project (intervention y)) =
      g.forward (jordanProduct (project x) (project y)) := by
  rw [h.intertwines, h.intertwines]
  symm
  exact cubicNormAutomorphism_map_jordan g (project x) (project y)

structure Boundary where
  finiteWeylEvidenceStillSeparate : Bool
  LieEvidenceStillSeparate : Bool
  cubicResidualSeparatedFromWeylResidual : Bool
  unitFixingMeasuredSeparately : Bool
  adjointResidualMeasuredSeparately : Bool
  jordanResidualMeasuredSeparately : Bool
  exactCubicNormIntertwinerImpliesProjectedJordanEquivariance : Bool
  cubicFitCreatesRationalF4Classification : Bool
  exceptionalFitCreatesMechanism : Bool
  exceptionalFitCreatesPhenomenology : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteWeylEvidenceStillSeparate := true
  LieEvidenceStillSeparate := true
  cubicResidualSeparatedFromWeylResidual := true
  unitFixingMeasuredSeparately := true
  adjointResidualMeasuredSeparately := true
  jordanResidualMeasuredSeparately := true
  exactCubicNormIntertwinerImpliesProjectedJordanEquivariance := true
  cubicFitCreatesRationalF4Classification := false
  exceptionalFitCreatesMechanism := false
  exceptionalFitCreatesPhenomenology := false

inductive ExceptionalFitCreatesMechanism : Prop
inductive ExceptionalFitCreatesPhenomenology : Prop

 theorem exceptional_fit_does_not_create_mechanism :
    ¬ ExceptionalFitCreatesMechanism := by intro h; cases h

 theorem exceptional_fit_does_not_create_phenomenology :
    ¬ ExceptionalFitCreatesPhenomenology := by intro h; cases h

end Integration.TeleodynamicsExceptionalCubicExperiment
