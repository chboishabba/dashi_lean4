import Mathlib
import Integration.OggSSPSmallCharacteristicRecognition
import Integration.ProvenancePreservingRecognition

/-!
# Independent Base369 recognition for small-characteristic Ogg/SSP carriers

Lean mirror of the live Agda independent-target recognitions:

* p=3: exact same-object recognition between the residual KernelTrit-style
  carrier and an independent SSPTrit Base369 target.
* p=2: exact recognition of both the gauge and retained-orientation semantics
  against an independent OrientationPolarity × NineOrbit target.

The p=2 arithmetic branch choice remains open.
-/

namespace Integration.OggSSPIndependentBase369Recognition

open Integration.ActionOrbitRecognition
open Integration.ProvenancePreservingRecognition
open Integration.OggSSPSmallCharacteristicRecognition

/-! ## p=3 independent Base369 target -/

inductive SSPTrit
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr, Fintype

def negateSSP : SSPTrit → SSPTrit
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

def p3TargetAct : C2 → SSPTrit → SSPTrit
  | .e, s => s
  | .flip, s => negateSSP s

def p3TargetAction : InvertibleAction SSPTrit C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := p3TargetAct
  identity_act := by intro s; cases s <;> rfl
  combine_act := by intro g h s; cases g <;> cases h <;> cases s <;> rfl
  inverse_left := by intro g s; cases g <;> cases s <;> rfl
  inverse_right := by intro g s; cases g <;> cases s <;> rfl

inductive P3TargetOrbit
  | zero
  | nonzero
  deriving DecidableEq, Repr, Fintype

def p3TargetOrbitOf : SSPTrit → P3TargetOrbit
  | .zero => .zero
  | .neg => .nonzero
  | .pos => .nonzero

def p3TargetRepresentative : P3TargetOrbit → SSPTrit
  | .zero => .zero
  | .nonzero => .pos

def p3TargetOrbitPresentation : OrbitPresentation p3TargetAction where
  Orbit := P3TargetOrbit
  orbitOf := p3TargetOrbitOf
  representative := p3TargetRepresentative
  orbit_invariant := by
    intro g s
    cases g <;> cases s <;> rfl
  representative_exact := by
    intro o
    cases o <;> rfl

def kernelToSSP : P3State → SSPTrit
  | .negative => .neg
  | .zero => .zero
  | .positive => .pos

def sspToKernel : SSPTrit → P3State
  | .neg => .negative
  | .zero => .zero
  | .pos => .positive

theorem kernel_ssp_roundtrip (s : P3State) :
    sspToKernel (kernelToSSP s) = s := by
  cases s <;> rfl

theorem ssp_kernel_roundtrip (s : SSPTrit) :
    kernelToSSP (sspToKernel s) = s := by
  cases s <;> rfl

theorem kernelToSSP_injective :
    Function.Injective kernelToSSP := by
  intro a b h
  have := congrArg sspToKernel h
  simpa [kernel_ssp_roundtrip] using this

theorem kernelToSSP_equivariant (g : C2) (s : P3State) :
    kernelToSSP (p3Action.act g s) =
      p3TargetAction.act g (kernelToSSP s) := by
  cases g <;> cases s <;> rfl

def p3IndependentActionRecognition :
    ActionRecognitionFunctor p3Action p3TargetAction where
  mapState := kernelToSSP
  mapSymmetry := id
  preservesIdentity := rfl
  preservesCombine := by intro g h; rfl
  preservesInverse := by intro g; rfl
  actionEquivariant := kernelToSSP_equivariant

def sourceOrbitToTarget : P3Orbit → P3TargetOrbit
  | .zero => .zero
  | .nonzero => .nonzero

def targetOrbitToSource : P3TargetOrbit → P3Orbit
  | .zero => .zero
  | .nonzero => .nonzero

theorem source_target_orbit_roundtrip (o : P3Orbit) :
    targetOrbitToSource (sourceOrbitToTarget o) = o := by
  cases o <;> rfl

theorem target_source_orbit_roundtrip (o : P3TargetOrbit) :
    sourceOrbitToTarget (targetOrbitToSource o) = o := by
  cases o <;> rfl

def p3IndependentOrbitRecognition :
    OrbitRecognition
      p3IndependentActionRecognition
      p3OrbitPresentation
      p3TargetOrbitPresentation where
  mapOrbit := sourceOrbitToTarget
  orbitMapExact := by
    intro s
    cases s <;> rfl

def p3IndependentPi0Embedding :
    Pi0Embedding p3IndependentOrbitRecognition where
  reflectsOrbitEquality := by
    intro a b h
    cases a <;> cases b
    · rfl
    · cases h
    · cases h
    · rfl

def p3IndependentPi0Surjection :
    Pi0Surjection p3IndependentOrbitRecognition where
  preimageOrbit := targetOrbitToSource
  hitsEveryTargetOrbit := target_source_orbit_roundtrip

def p3IndependentStabilizerRecognition :
    StabilizerRecognition p3IndependentOrbitRecognition where
  representativeCompatibility := by
    intro o
    cases o <;> rfl
  preservesStabilizer := by
    intro o g h
    cases o with
    | zero => cases g <;> rfl
    | nonzero =>
      cases g with
      | e => rfl
      | flip => cases h
  reflectsMappedStabilizer := by
    intro o g h
    cases o with
    | zero => cases g <;> rfl
    | nonzero =>
      cases g with
      | e => rfl
      | flip => cases h

def p3IndependentFullRecognition :
    FullRecognition
      p3IndependentActionRecognition
      p3OrbitPresentation
      p3TargetOrbitPresentation where
  orbitRecognition := p3IndependentOrbitRecognition
  pi0Embedding := p3IndependentPi0Embedding
  pi0Surjection := p3IndependentPi0Surjection
  stabilizerRecognition := p3IndependentStabilizerRecognition

def p3SourceProvenance : P3State → P3State := id
def p3TargetProvenance : SSPTrit → SSPTrit := id

def p3ProvenanceActionRecognition :
    ProvenancePreservingActionRecognition
      p3SourceProvenance
      p3TargetProvenance where
  actionRecognition := p3IndependentActionRecognition
  mapProvenance := kernelToSSP
  provenanceCommutes := by intro s; rfl
  reflectsMappedProvenance := by
    intro a b h
    exact kernelToSSP_injective h

def p3ProvenanceOrbitRecognition :
    ProvenancePreservingOrbitRecognition
      p3ProvenanceActionRecognition
      p3OrbitPresentation
      p3TargetOrbitPresentation where
  fullRecognition := p3IndependentFullRecognition

/-! ## p=2 independent Base369 target -/

inductive OrientationPolarity
  | negative
  | positive
  deriving DecidableEq, Repr, Fintype

def sideToPolarity : StrictSide → OrientationPolarity
  | .lower => .negative
  | .upper => .positive

def polarityToSide : OrientationPolarity → StrictSide
  | .negative => .lower
  | .positive => .upper

theorem side_polarity_roundtrip (s : StrictSide) :
    polarityToSide (sideToPolarity s) = s := by
  cases s <;> rfl

theorem polarity_side_roundtrip (p : OrientationPolarity) :
    sideToPolarity (polarityToSide p) = p := by
  cases p <;> rfl

abbrev P2IndependentState := OrientationPolarity × NineOrbit

def p2SourceToTarget : P2State → P2IndependentState
  | (s, o) => (sideToPolarity s, o)

def p2TargetToSource : P2IndependentState → P2State
  | (p, o) => (polarityToSide p, o)

theorem p2_source_target_roundtrip (s : P2State) :
    p2TargetToSource (p2SourceToTarget s) = s := by
  rcases s with ⟨side, orbit⟩
  cases side <;> rfl

theorem p2_target_source_roundtrip (s : P2IndependentState) :
    p2SourceToTarget (p2TargetToSource s) = s := by
  rcases s with ⟨polarity, orbit⟩
  cases polarity <;> rfl

theorem p2SourceToTarget_injective :
    Function.Injective p2SourceToTarget := by
  intro a b h
  have := congrArg p2TargetToSource h
  simpa [p2_source_target_roundtrip] using this

def flipSide : StrictSide → StrictSide
  | .lower => .upper
  | .upper => .lower

def flipPolarity : OrientationPolarity → OrientationPolarity
  | .negative => .positive
  | .positive => .negative

def p2GaugeSourceAct : C2 → P2State → P2State
  | .e, s => s
  | .flip, (side, orbit) => (flipSide side, orbit)

def p2GaugeSourceAction : InvertibleAction P2State C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := p2GaugeSourceAct
  identity_act := by intro s; rfl
  combine_act := by
    intro g h s
    cases g <;> cases h <;> rcases s with ⟨side, orbit⟩ <;> cases side <;> rfl
  inverse_left := by
    intro g s
    cases g <;> rcases s with ⟨side, orbit⟩ <;> cases side <;> rfl
  inverse_right := by
    intro g s
    cases g <;> rcases s with ⟨side, orbit⟩ <;> cases side <;> rfl

def p2GaugeTargetAct : C2 → P2IndependentState → P2IndependentState
  | .e, s => s
  | .flip, (polarity, orbit) => (flipPolarity polarity, orbit)

def p2GaugeTargetAction : InvertibleAction P2IndependentState C2 where
  identity := .e
  combine := c2Combine
  inverse := c2Inverse
  act := p2GaugeTargetAct
  identity_act := by intro s; rfl
  combine_act := by
    intro g h s
    cases g <;> cases h <;> rcases s with ⟨p, o⟩ <;> cases p <;> rfl
  inverse_left := by
    intro g s
    cases g <;> rcases s with ⟨p, o⟩ <;> cases p <;> rfl
  inverse_right := by
    intro g s
    cases g <;> rcases s with ⟨p, o⟩ <;> cases p <;> rfl

def p2GaugeSourceOrbitPresentation : OrbitPresentation p2GaugeSourceAction where
  Orbit := NineOrbit
  orbitOf := Prod.snd
  representative := fun o => (.upper, o)
  orbit_invariant := by
    intro g s
    cases g <;> rcases s with ⟨side, orbit⟩ <;> cases side <;> rfl
  representative_exact := by intro o; rfl

def p2GaugeTargetOrbitPresentation : OrbitPresentation p2GaugeTargetAction where
  Orbit := NineOrbit
  orbitOf := Prod.snd
  representative := fun o => (.positive, o)
  orbit_invariant := by
    intro g s
    cases g <;> rcases s with ⟨p, o⟩ <;> cases p <;> rfl
  representative_exact := by intro o; rfl

theorem p2Gauge_equivariant (g : C2) (s : P2State) :
    p2SourceToTarget (p2GaugeSourceAction.act g s) =
      p2GaugeTargetAction.act g (p2SourceToTarget s) := by
  cases g <;> rcases s with ⟨side, orbit⟩ <;> cases side <;> rfl

def p2GaugeActionRecognition :
    ActionRecognitionFunctor p2GaugeSourceAction p2GaugeTargetAction where
  mapState := p2SourceToTarget
  mapSymmetry := id
  preservesIdentity := rfl
  preservesCombine := by intro g h; rfl
  preservesInverse := by intro g; rfl
  actionEquivariant := p2Gauge_equivariant

def p2GaugeOrbitRecognition :
    OrbitRecognition
      p2GaugeActionRecognition
      p2GaugeSourceOrbitPresentation
      p2GaugeTargetOrbitPresentation where
  mapOrbit := id
  orbitMapExact := by intro s; rfl

def p2GaugePi0Embedding :
    Pi0Embedding p2GaugeOrbitRecognition where
  reflectsOrbitEquality := by intro a b h; exact h

def p2GaugePi0Surjection :
    Pi0Surjection p2GaugeOrbitRecognition where
  preimageOrbit := id
  hitsEveryTargetOrbit := by intro o; rfl

def p2GaugeStabilizerRecognition :
    StabilizerRecognition p2GaugeOrbitRecognition where
  representativeCompatibility := by intro o; rfl
  preservesStabilizer := by
    intro o g h
    cases g with
    | e => rfl
    | flip => cases h
  reflectsMappedStabilizer := by
    intro o g h
    cases g with
    | e => rfl
    | flip => cases h

def p2GaugeFullRecognition :
    FullRecognition
      p2GaugeActionRecognition
      p2GaugeSourceOrbitPresentation
      p2GaugeTargetOrbitPresentation where
  orbitRecognition := p2GaugeOrbitRecognition
  pi0Embedding := p2GaugePi0Embedding
  pi0Surjection := p2GaugePi0Surjection
  stabilizerRecognition := p2GaugeStabilizerRecognition

def p2RetainedSourceAction : InvertibleAction P2State PUnit :=
  p2DiscreteAction

def p2RetainedTargetAction : InvertibleAction P2IndependentState PUnit where
  identity := PUnit.unit
  combine := fun _ _ => PUnit.unit
  inverse := fun _ => PUnit.unit
  act := fun _ s => s
  identity_act := by intro s; rfl
  combine_act := by intro _ _ s; rfl
  inverse_left := by intro _ s; rfl
  inverse_right := by intro _ s; rfl

def p2RetainedTargetOrbitPresentation :
    OrbitPresentation p2RetainedTargetAction where
  Orbit := P2IndependentState
  orbitOf := id
  representative := id
  orbit_invariant := by intro _ s; rfl
  representative_exact := by intro s; rfl

def p2RetainedActionRecognition :
    ActionRecognitionFunctor p2RetainedSourceAction p2RetainedTargetAction where
  mapState := p2SourceToTarget
  mapSymmetry := id
  preservesIdentity := rfl
  preservesCombine := by intro _ _; rfl
  preservesInverse := by intro _; rfl
  actionEquivariant := by intro _ s; rfl

def p2RetainedOrbitRecognition :
    OrbitRecognition
      p2RetainedActionRecognition
      p2DiscreteOrbitPresentation
      p2RetainedTargetOrbitPresentation where
  mapOrbit := p2SourceToTarget
  orbitMapExact := by intro s; rfl

def p2RetainedPi0Embedding :
    Pi0Embedding p2RetainedOrbitRecognition where
  reflectsOrbitEquality := by
    intro a b h
    exact p2SourceToTarget_injective h

def p2RetainedPi0Surjection :
    Pi0Surjection p2RetainedOrbitRecognition where
  preimageOrbit := p2TargetToSource
  hitsEveryTargetOrbit := p2_target_source_roundtrip

def p2RetainedStabilizerRecognition :
    StabilizerRecognition p2RetainedOrbitRecognition where
  representativeCompatibility := by intro s; rfl
  preservesStabilizer := by intro _ _ _; rfl
  reflectsMappedStabilizer := by intro _ _ _; rfl

def p2RetainedFullRecognition :
    FullRecognition
      p2RetainedActionRecognition
      p2DiscreteOrbitPresentation
      p2RetainedTargetOrbitPresentation where
  orbitRecognition := p2RetainedOrbitRecognition
  pi0Embedding := p2RetainedPi0Embedding
  pi0Surjection := p2RetainedPi0Surjection
  stabilizerRecognition := p2RetainedStabilizerRecognition

def p2SourceOrientationProvenance : P2State → StrictSide := Prod.fst
def p2TargetOrientationProvenance : P2IndependentState → OrientationPolarity := Prod.fst

def p2GaugeProvenanceActionRecognition :
    ProvenancePreservingActionRecognition
      p2SourceOrientationProvenance
      p2TargetOrientationProvenance where
  actionRecognition := p2GaugeActionRecognition
  mapProvenance := sideToPolarity
  provenanceCommutes := by
    intro s
    rcases s with ⟨side, orbit⟩
    rfl
  reflectsMappedProvenance := by
    intro a b h
    rcases a with ⟨sa, oa⟩
    rcases b with ⟨sb, ob⟩
    cases sa <;> cases sb <;> simp [p2SourceToTarget, p2TargetOrientationProvenance] at h ⊢

def p2GaugeProvenanceOrbitRecognition :
    ProvenancePreservingOrbitRecognition
      p2GaugeProvenanceActionRecognition
      p2GaugeSourceOrbitPresentation
      p2GaugeTargetOrbitPresentation where
  fullRecognition := p2GaugeFullRecognition

def p2RetainedProvenanceActionRecognition :
    ProvenancePreservingActionRecognition
      p2SourceOrientationProvenance
      p2TargetOrientationProvenance where
  actionRecognition := p2RetainedActionRecognition
  mapProvenance := sideToPolarity
  provenanceCommutes := by
    intro s
    rcases s with ⟨side, orbit⟩
    rfl
  reflectsMappedProvenance := by
    intro a b h
    rcases a with ⟨sa, oa⟩
    rcases b with ⟨sb, ob⟩
    cases sa <;> cases sb <;> simp [p2SourceToTarget, p2TargetOrientationProvenance] at h ⊢

def p2RetainedProvenanceOrbitRecognition :
    ProvenancePreservingOrbitRecognition
      p2RetainedProvenanceActionRecognition
      p2DiscreteOrbitPresentation
      p2RetainedTargetOrbitPresentation where
  fullRecognition := p2RetainedFullRecognition

structure IndependentRecognitionBoundary where
  p3ExactRechartPaid : Bool
  p3FullRecognitionPaid : Bool
  p3ExactProvenancePreserved : Bool
  p2GaugeRecognitionPaid : Bool
  p2RetainedRecognitionPaid : Bool
  p2GaugeOrientationProvenancePreserved : Bool
  p2RetainedOrientationProvenancePreserved : Bool
  p2ArithmeticBranchDecided : Bool
  deriving Repr

def canonicalBoundary : IndependentRecognitionBoundary where
  p3ExactRechartPaid := true
  p3FullRecognitionPaid := true
  p3ExactProvenancePreserved := true
  p2GaugeRecognitionPaid := true
  p2RetainedRecognitionPaid := true
  p2GaugeOrientationProvenancePreserved := true
  p2RetainedOrientationProvenancePreserved := true
  p2ArithmeticBranchDecided := false

end Integration.OggSSPIndependentBase369Recognition
