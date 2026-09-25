import Mathlib

/-!
# Action/orbit/stabilizer recognition core

Lean mirror of the repository's Agda recognition contract.  This is deliberately
stronger than a map of finite sets: a recognition morphism must preserve the
symmetry algebra, intertwine the actions, descend exactly to orbit carriers,
and preserve/reflect stabilizer membership.
-/

namespace Integration.ActionOrbitRecognition

structure InvertibleAction (State Symmetry : Type) where
  identity : Symmetry
  combine : Symmetry → Symmetry → Symmetry
  inverse : Symmetry → Symmetry
  act : Symmetry → State → State
  identity_act : ∀ s, act identity s = s
  combine_act : ∀ g h s, act (combine g h) s = act g (act h s)
  inverse_left : ∀ g s, act (inverse g) (act g s) = s
  inverse_right : ∀ g s, act g (act (inverse g) s) = s

structure OrbitPresentation
    {State Symmetry : Type}
    (A : InvertibleAction State Symmetry) where
  Orbit : Type
  orbitOf : State → Orbit
  representative : Orbit → State
  orbit_invariant : ∀ g s, orbitOf (A.act g s) = orbitOf s
  representative_exact : ∀ o, orbitOf (representative o) = o

structure ActionRecognitionFunctor
    {SourceState SourceSymmetry TargetState TargetSymmetry : Type}
    (source : InvertibleAction SourceState SourceSymmetry)
    (target : InvertibleAction TargetState TargetSymmetry) where
  mapState : SourceState → TargetState
  mapSymmetry : SourceSymmetry → TargetSymmetry
  preservesIdentity :
    mapSymmetry source.identity = target.identity
  preservesCombine :
    ∀ g h, mapSymmetry (source.combine g h) =
      target.combine (mapSymmetry g) (mapSymmetry h)
  preservesInverse :
    ∀ g, mapSymmetry (source.inverse g) =
      target.inverse (mapSymmetry g)
  actionEquivariant :
    ∀ g s, mapState (source.act g s) =
      target.act (mapSymmetry g) (mapState s)

structure OrbitRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Type}
    {source : InvertibleAction SourceState SourceSymmetry}
    {target : InvertibleAction TargetState TargetSymmetry}
    (F : ActionRecognitionFunctor source target)
    (sourceOrbits : OrbitPresentation source)
    (targetOrbits : OrbitPresentation target) where
  mapOrbit : sourceOrbits.Orbit → targetOrbits.Orbit
  orbitMapExact :
    ∀ s, targetOrbits.orbitOf (F.mapState s) =
      mapOrbit (sourceOrbits.orbitOf s)

theorem mapped_action_stays_in_mapped_orbit
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {F : ActionRecognitionFunctor source target}
    {sourceOrbits : OrbitPresentation source}
    {targetOrbits : OrbitPresentation target}
    (R : OrbitRecognition F sourceOrbits targetOrbits)
    (g : SG) (s : SS) :
    targetOrbits.orbitOf (F.mapState (source.act g s)) =
      R.mapOrbit (sourceOrbits.orbitOf s) := by
  rw [F.actionEquivariant]
  rw [targetOrbits.orbit_invariant]
  exact R.orbitMapExact s

structure Pi0Embedding
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {F : ActionRecognitionFunctor source target}
    {sourceOrbits : OrbitPresentation source}
    {targetOrbits : OrbitPresentation target}
    (R : OrbitRecognition F sourceOrbits targetOrbits) where
  reflectsOrbitEquality :
    ∀ {a b}, R.mapOrbit a = R.mapOrbit b → a = b

structure Pi0Surjection
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {F : ActionRecognitionFunctor source target}
    {sourceOrbits : OrbitPresentation source}
    {targetOrbits : OrbitPresentation target}
    (R : OrbitRecognition F sourceOrbits targetOrbits) where
  preimageOrbit : targetOrbits.Orbit → sourceOrbits.Orbit
  hitsEveryTargetOrbit :
    ∀ o, R.mapOrbit (preimageOrbit o) = o

structure StabilizerRecognition
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {F : ActionRecognitionFunctor source target}
    {sourceOrbits : OrbitPresentation source}
    {targetOrbits : OrbitPresentation target}
    (R : OrbitRecognition F sourceOrbits targetOrbits) where
  representativeCompatibility :
    ∀ o, F.mapState (sourceOrbits.representative o) =
      targetOrbits.representative (R.mapOrbit o)
  preservesStabilizer :
    ∀ o g,
      source.act g (sourceOrbits.representative o) =
        sourceOrbits.representative o →
      target.act (F.mapSymmetry g)
          (targetOrbits.representative (R.mapOrbit o)) =
        targetOrbits.representative (R.mapOrbit o)
  reflectsMappedStabilizer :
    ∀ o g,
      target.act (F.mapSymmetry g)
          (targetOrbits.representative (R.mapOrbit o)) =
        targetOrbits.representative (R.mapOrbit o) →
      source.act g (sourceOrbits.representative o) =
        sourceOrbits.representative o

structure FullRecognition
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    (F : ActionRecognitionFunctor source target)
    (sourceOrbits : OrbitPresentation source)
    (targetOrbits : OrbitPresentation target) where
  orbitRecognition : OrbitRecognition F sourceOrbits targetOrbits
  pi0Embedding : Pi0Embedding orbitRecognition
  pi0Surjection : Pi0Surjection orbitRecognition
  stabilizerRecognition : StabilizerRecognition orbitRecognition

namespace FullRecognition

theorem targetOrbit_to_source_injective
    {SS SG TS TG : Type}
    {source : InvertibleAction SS SG}
    {target : InvertibleAction TS TG}
    {F : ActionRecognitionFunctor source target}
    {sourceOrbits : OrbitPresentation source}
    {targetOrbits : OrbitPresentation target}
    (R : FullRecognition F sourceOrbits targetOrbits) :
    Function.Injective R.pi0Surjection.preimageOrbit := by
  intro a b h
  have hm :
      R.orbitRecognition.mapOrbit
          (R.pi0Surjection.preimageOrbit a) =
        R.orbitRecognition.mapOrbit
          (R.pi0Surjection.preimageOrbit b) :=
    congrArg R.orbitRecognition.mapOrbit h
  simpa [R.pi0Surjection.hitsEveryTargetOrbit] using hm

end FullRecognition

inductive RecognitionPromotionError
  | cardinalityMatchOnly
  | stateMapWithoutActionEquivariance
  | orbitBijectionWithoutStabilizerControl
  deriving DecidableEq, Repr

end Integration.ActionOrbitRecognition
