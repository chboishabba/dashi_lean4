import Mathlib
import CondensedMatter.YbSb2BdGSymmetryBoundary

namespace CondensedMatter
namespace YbSb2

/-!
Attribution boundary:

SOURCE (Kataria et al.): an effective YbSb2 INT BdG model with a modeled
Majorana surface branch.

DASHI: this file formalizes the additional obligations needed before such a
mode can be used as a topological quantum-computing platform.

The hierarchy is intentionally strict:
  modeled surface Majorana
    != isolated Majorana defect mode
    != parity-protected logical qubit
    != non-Abelian braid representation
    != universal quantum computation
    != experimentally validated device.
-/

structure MajoranaPhysicalPlatform where
  surfaceMode : MajoranaSurfaceWitness
  isolatedDefectMode : Prop
  isolatedDefectModeWitness : isolatedDefectMode
  fermionParityProtected : Prop
  fermionParityProtectedWitness : fermionParityProtected

structure MajoranaLogicalEncoding (P : MajoranaPhysicalPlatform) where
  LogicalBasis : Type
  encode : LogicalBasis → Prop
  parityEncodingIsPhysical : Prop
  parityEncodingWitness : parityEncodingIsPhysical

structure MajoranaBraidGateLayer
    {P : MajoranaPhysicalPlatform}
    (E : MajoranaLogicalEncoding P) where
  BraidWord : Type
  LogicalGate : Type
  interpretBraid : BraidWord → LogicalGate
  nonAbelianRepresentation : Prop
  nonAbelianRepresentationWitness : nonAbelianRepresentation
  preservesCodeSpace : Prop
  preservesCodeSpaceWitness : preservesCodeSpace

structure MajoranaComputationLayer
    {P : MajoranaPhysicalPlatform}
    {E : MajoranaLogicalEncoding P}
    (B : MajoranaBraidGateLayer E) where
  Circuit : Type
  runCircuit : Circuit → Prop
  faultProtectedLogicalAction : Prop
  faultProtectedLogicalActionWitness : faultProtectedLogicalAction

/--
Majorana/Ising braiding is not promoted to universality by construction.
A universal-computation theorem must supply an additional completion resource.
-/
structure UniversalCompletion
    {P : MajoranaPhysicalPlatform}
    {E : MajoranaLogicalEncoding P}
    {B : MajoranaBraidGateLayer E}
    (C : MajoranaComputationLayer B) where
  ExtraResource : Type
  extraResource : ExtraResource
  universalGateSet : Prop
  universalGateSetWitness : universalGateSet

/--
Terminal YbSb2-to-device bridge.  It deliberately has no canonical inhabitant.
-/
structure YbSb2MajoranaQuantumComputerBridge where
  platform : MajoranaPhysicalPlatform
  encoding : MajoranaLogicalEncoding platform
  braidLayer : MajoranaBraidGateLayer encoding
  computationLayer : MajoranaComputationLayer braidLayer

  sourceModelIdentifiedWithPhysicalMajoranaPlatform : Prop
  sourceModelIdentificationWitness :
    sourceModelIdentifiedWithPhysicalMajoranaPlatform

  encodedReadoutExperimentallyResolved : Prop
  encodedReadoutWitness :
    encodedReadoutExperimentallyResolved

end YbSb2
end CondensedMatter
