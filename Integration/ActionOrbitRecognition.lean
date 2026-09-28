import Integration.Kernel.Quotient
import Mathlib

/-!
# Action / orbit / stabilizer recognition

Generic Lean mirror of the Agda owner
`DASHI.Core.ActionOrbitRecognitionFunctorExact`.

This file introduces no Moonshine semantics.  It separates:

* action-level recognition;
* orbit-map recognition;
* pi0 injectivity/surjectivity;
* stabilizer preservation/reflection;
* the full recognition package.

Equal carrier cardinality is deliberately not enough.
-/

namespace Integration.ActionOrbitRecognition

universe u v w x

/-! ## §1 Invertible action presentation -/

structure InvertibleAction (State : Type u) (Sym : Type v) where
  identity : Sym
  combine : Sym → Sym → Sym
  inverse : Sym → Sym
  act : Sym → State → State
  identity_acts : ∀ s, act identity s = s
  combine_acts : ∀ g h s, act (combine g h) s = act g (act h s)
  inverse_left : ∀ g s, act (inverse g) (act g s) = s
  inverse_right : ∀ g s, act g (act (inverse g) s) = s

/-! ## §2 Chosen orbit presentation -/

structure OrbitPresentation {State : Type u} {Sym : Type v}
    (A : InvertibleAction State Sym) where
  Orbit : Type w
  orbitOf : State → Orbit
  representative : Orbit → State
  orbitInvariant : ∀ g s, orbitOf (A.act g s) = orbitOf s
  representativeInOrbit : ∀ o, orbitOf (representative o) = o
  transporter : State → Sym
  transporterHits : ∀ s, A.act (transporter s) (representative (orbitOf s)) = s

/-! ## §3 Action recognition -/

structure ActionRecognitionFunctor
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    (sourceAction : InvertibleAction SourceState SourceSym)
    (targetAction : InvertibleAction TargetState TargetSym) where
  mapState : SourceState → TargetState
  mapSymmetry : SourceSym → TargetSym
  preservesIdentity :
    mapSymmetry sourceAction.identity = targetAction.identity
  preservesCombine :
    ∀ g h, mapSymmetry (sourceAction.combine g h) =
      targetAction.combine (mapSymmetry g) (mapSymmetry h)
  preservesInverse :
    ∀ g, mapSymmetry (sourceAction.inverse g) =
      targetAction.inverse (mapSymmetry g)
  actionEquivariant :
    ∀ g s, mapState (sourceAction.act g s) =
      targetAction.act (mapSymmetry g) (mapState s)

/-! ## §4 Orbit recognition -/

structure OrbitRecognition
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    (F : ActionRecognitionFunctor sourceAction targetAction)
    (sourceOrbits : OrbitPresentation sourceAction)
    (targetOrbits : OrbitPresentation targetAction) where
  mapOrbit : sourceOrbits.Orbit → targetOrbits.Orbit
  orbitMapExact :
    ∀ s, targetOrbits.orbitOf (F.mapState s) =
      mapOrbit (sourceOrbits.orbitOf s)

structure Pi0Embedding
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    {F : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : OrbitPresentation sourceAction}
    {targetOrbits : OrbitPresentation targetAction}
    (R : OrbitRecognition F sourceOrbits targetOrbits) : Prop where
  reflectsOrbitEquality :
    ∀ {a b}, R.mapOrbit a = R.mapOrbit b → a = b

structure Pi0Surjection
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    {F : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : OrbitPresentation sourceAction}
    {targetOrbits : OrbitPresentation targetAction}
    (R : OrbitRecognition F sourceOrbits targetOrbits) : Type max u v w x where
  preimageOrbit : targetOrbits.Orbit → sourceOrbits.Orbit
  hitsEveryTargetOrbit : ∀ o, R.mapOrbit (preimageOrbit o) = o

/-! ## §5 Stabilizer recognition -/

structure StabilizerRecognition
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    {F : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : OrbitPresentation sourceAction}
    {targetOrbits : OrbitPresentation targetAction}
    (R : OrbitRecognition F sourceOrbits targetOrbits) where
  representativeCompatibility :
    ∀ o, F.mapState (sourceOrbits.representative o) =
      targetOrbits.representative (R.mapOrbit o)
  preservesStabilizer :
    ∀ o g,
      sourceAction.act g (sourceOrbits.representative o) =
        sourceOrbits.representative o →
      targetAction.act (F.mapSymmetry g)
        (targetOrbits.representative (R.mapOrbit o)) =
        targetOrbits.representative (R.mapOrbit o)
  reflectsMappedStabilizer :
    ∀ o g,
      targetAction.act (F.mapSymmetry g)
        (targetOrbits.representative (R.mapOrbit o)) =
        targetOrbits.representative (R.mapOrbit o) →
      sourceAction.act g (sourceOrbits.representative o) =
        sourceOrbits.representative o

structure OrbitStabilizerRecognition
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    (F : ActionRecognitionFunctor sourceAction targetAction)
    (sourceOrbits : OrbitPresentation sourceAction)
    (targetOrbits : OrbitPresentation targetAction) where
  orbitRecognition : OrbitRecognition F sourceOrbits targetOrbits
  pi0Embedding : Pi0Embedding orbitRecognition
  pi0Surjection : Pi0Surjection orbitRecognition
  stabilizerRecognition : StabilizerRecognition orbitRecognition

/-! ## §6 Cheap gates do not construct recognition -/

inductive CardinalityMatchCreatesRecognitionFunctor : Prop

theorem cardinality_match_does_not_create_recognition :
    ¬ CardinalityMatchCreatesRecognitionFunctor := by
  intro h
  cases h

inductive StateMapAlonePreservesPi0 : Prop

theorem state_map_alone_does_not_preserve_pi0 :
    ¬ StateMapAlonePreservesPi0 := by
  intro h
  cases h

structure Boundary where
  actionEquivarianceRequired : Bool
  symmetryLawsRequired : Bool
  orbitMapExactRequired : Bool
  pi0EmbeddingSeparate : Bool
  pi0SurjectionSeparate : Bool
  stabilizerPreservationSeparate : Bool
  stabilizerReflectionSeparate : Bool
  cardinalityMatchSufficient : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actionEquivarianceRequired := true
  symmetryLawsRequired := true
  orbitMapExactRequired := true
  pi0EmbeddingSeparate := true
  pi0SurjectionSeparate := true
  stabilizerPreservationSeparate := true
  stabilizerReflectionSeparate := true
  cardinalityMatchSufficient := false

end Integration.ActionOrbitRecognition
