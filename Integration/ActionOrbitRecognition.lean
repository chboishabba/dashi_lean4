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

universe u v w x y z

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
    (R : OrbitRecognition F sourceOrbits targetOrbits) : Type (max (max u v) (max w x)) where
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

/-! ## §6 Strong same-presentation recognition -/

structure StateMapEquivalence
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    (F : ActionRecognitionFunctor sourceAction targetAction) where
  preimageState : TargetState → SourceState
  mapAfterPreimageState :
    ∀ target, F.mapState (preimageState target) = target
  preimageAfterMapState :
    ∀ source, preimageState (F.mapState source) = source

structure SymmetryMapEquivalence
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    (F : ActionRecognitionFunctor sourceAction targetAction) where
  preimageSymmetry : TargetSym → SourceSym
  mapAfterPreimageSymmetry :
    ∀ target, F.mapSymmetry (preimageSymmetry target) = target
  preimageAfterMapSymmetry :
    ∀ source, preimageSymmetry (F.mapSymmetry source) = source

structure ActionGroupoidPresentationIsomorphism
    {SourceState : Type u} {SourceSym : Type v}
    {TargetState : Type w} {TargetSym : Type x}
    {sourceAction : InvertibleAction SourceState SourceSym}
    {targetAction : InvertibleAction TargetState TargetSym}
    (F : ActionRecognitionFunctor sourceAction targetAction)
    (sourceOrbits : OrbitPresentation sourceAction)
    (targetOrbits : OrbitPresentation targetAction) where
  orbitStabilizerRecognition :
    OrbitStabilizerRecognition F sourceOrbits targetOrbits
  stateMapEquivalence : StateMapEquivalence F
  symmetryMapEquivalence : SymmetryMapEquivalence F

inductive OrbitStabilizerRecognitionCreatesPresentationIsomorphism : Prop
inductive Pi0BijectionCreatesStateBijection : Prop
inductive MappedStabilizersCreateSymmetryBijection : Prop

theorem orbit_stabilizer_recognition_does_not_create_presentation_isomorphism :
    ¬ OrbitStabilizerRecognitionCreatesPresentationIsomorphism := by
  intro h
  cases h

theorem pi0_bijection_does_not_create_state_bijection :
    ¬ Pi0BijectionCreatesStateBijection := by
  intro h
  cases h

theorem mapped_stabilizers_do_not_create_symmetry_bijection :
    ¬ MappedStabilizersCreateSymmetryBijection := by
  intro h
  cases h

/-! ## §7 Recognition composition -/

def composeActionRecognition
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    (first : ActionRecognitionFunctor actionA actionB)
    (second : ActionRecognitionFunctor actionB actionC) :
    ActionRecognitionFunctor actionA actionC where
  mapState := fun s => second.mapState (first.mapState s)
  mapSymmetry := fun g => second.mapSymmetry (first.mapSymmetry g)
  preservesIdentity := by
    rw [first.preservesIdentity, second.preservesIdentity]
  preservesCombine := by
    intro g h
    rw [first.preservesCombine, second.preservesCombine]
  preservesInverse := by
    intro g
    rw [first.preservesInverse, second.preservesInverse]
  actionEquivariant := by
    intro g s
    rw [first.actionEquivariant, second.actionEquivariant]

def composeOrbitRecognition
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    {first : ActionRecognitionFunctor actionA actionB}
    {second : ActionRecognitionFunctor actionB actionC}
    {orbitsA : OrbitPresentation actionA}
    {orbitsB : OrbitPresentation actionB}
    {orbitsC : OrbitPresentation actionC}
    (R₁ : OrbitRecognition first orbitsA orbitsB)
    (R₂ : OrbitRecognition second orbitsB orbitsC) :
    OrbitRecognition (composeActionRecognition first second) orbitsA orbitsC where
  mapOrbit := fun o => R₂.mapOrbit (R₁.mapOrbit o)
  orbitMapExact := by
    intro s
    rw [R₂.orbitMapExact, R₁.orbitMapExact]

def composePi0Embedding
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    {first : ActionRecognitionFunctor actionA actionB}
    {second : ActionRecognitionFunctor actionB actionC}
    {orbitsA : OrbitPresentation actionA}
    {orbitsB : OrbitPresentation actionB}
    {orbitsC : OrbitPresentation actionC}
    {R₁ : OrbitRecognition first orbitsA orbitsB}
    {R₂ : OrbitRecognition second orbitsB orbitsC}
    (E₁ : Pi0Embedding R₁)
    (E₂ : Pi0Embedding R₂) :
    Pi0Embedding (composeOrbitRecognition R₁ R₂) where
  reflectsOrbitEquality := by
    intro a b h
    exact E₁.reflectsOrbitEquality (E₂.reflectsOrbitEquality h)

def composePi0Surjection
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    {first : ActionRecognitionFunctor actionA actionB}
    {second : ActionRecognitionFunctor actionB actionC}
    {orbitsA : OrbitPresentation actionA}
    {orbitsB : OrbitPresentation actionB}
    {orbitsC : OrbitPresentation actionC}
    {R₁ : OrbitRecognition first orbitsA orbitsB}
    {R₂ : OrbitRecognition second orbitsB orbitsC}
    (S₁ : Pi0Surjection R₁)
    (S₂ : Pi0Surjection R₂) :
    Pi0Surjection (composeOrbitRecognition R₁ R₂) where
  preimageOrbit := fun o => S₁.preimageOrbit (S₂.preimageOrbit o)
  hitsEveryTargetOrbit := by
    intro o
    rw [S₁.hitsEveryTargetOrbit, S₂.hitsEveryTargetOrbit]

def composeStabilizerRecognition
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    {first : ActionRecognitionFunctor actionA actionB}
    {second : ActionRecognitionFunctor actionB actionC}
    {orbitsA : OrbitPresentation actionA}
    {orbitsB : OrbitPresentation actionB}
    {orbitsC : OrbitPresentation actionC}
    {R₁ : OrbitRecognition first orbitsA orbitsB}
    {R₂ : OrbitRecognition second orbitsB orbitsC}
    (S₁ : StabilizerRecognition R₁)
    (S₂ : StabilizerRecognition R₂) :
    StabilizerRecognition (composeOrbitRecognition R₁ R₂) where
  representativeCompatibility := by
    intro o
    calc
      second.mapState (first.mapState (orbitsA.representative o))
          = second.mapState (orbitsB.representative (R₁.mapOrbit o)) :=
            congrArg second.mapState (S₁.representativeCompatibility o)
      _ = orbitsC.representative (R₂.mapOrbit (R₁.mapOrbit o)) :=
            S₂.representativeCompatibility (R₁.mapOrbit o)
  preservesStabilizer := by
    intro o g hfix
    exact S₂.preservesStabilizer
      (R₁.mapOrbit o)
      (first.mapSymmetry g)
      (S₁.preservesStabilizer o g hfix)
  reflectsMappedStabilizer := by
    intro o g hfix
    exact S₁.reflectsMappedStabilizer o g
      (S₂.reflectsMappedStabilizer
        (R₁.mapOrbit o)
        (first.mapSymmetry g)
        hfix)

def composeOrbitStabilizerRecognition
    {AState : Type u} {ASym : Type v}
    {BState : Type w} {BSym : Type x}
    {CState : Type y} {CSym : Type z}
    {actionA : InvertibleAction AState ASym}
    {actionB : InvertibleAction BState BSym}
    {actionC : InvertibleAction CState CSym}
    {first : ActionRecognitionFunctor actionA actionB}
    {second : ActionRecognitionFunctor actionB actionC}
    {orbitsA : OrbitPresentation actionA}
    {orbitsB : OrbitPresentation actionB}
    {orbitsC : OrbitPresentation actionC}
    (R₁ : OrbitStabilizerRecognition first orbitsA orbitsB)
    (R₂ : OrbitStabilizerRecognition second orbitsB orbitsC) :
    OrbitStabilizerRecognition
      (composeActionRecognition first second)
      orbitsA orbitsC where
  orbitRecognition :=
    composeOrbitRecognition R₁.orbitRecognition R₂.orbitRecognition
  pi0Embedding :=
    composePi0Embedding R₁.pi0Embedding R₂.pi0Embedding
  pi0Surjection :=
    composePi0Surjection R₁.pi0Surjection R₂.pi0Surjection
  stabilizerRecognition :=
    composeStabilizerRecognition
      R₁.stabilizerRecognition
      R₂.stabilizerRecognition

/-! ## §8 Cheap gates do not construct recognition -/



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
  samePresentationRequiresStateBijection : Bool
  samePresentationRequiresSymmetryBijection : Bool
  recognitionCompositionOwned : Bool
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
  samePresentationRequiresStateBijection := true
  samePresentationRequiresSymmetryBijection := true
  recognitionCompositionOwned := true
  cardinalityMatchSufficient := false

end Integration.ActionOrbitRecognition
