import Mathlib
import AgdaMirror.AdK.PDBMirrorSelectedFixture
import AgdaMirror.AdK.CVProjection

/-!
# Transparent PDB mirror fixtures projected through the native Lean AdK CV spine

This owner is the direct weld:

  observed transport mirror
      -> transparent exact-rational selected Configuration
      -> CanonicalSelectionContent
      -> exact mass-weighted COM
      -> ThreeCVInputSurface

No Python manifest, SHA equality premise, or external SelectionEquivalent witness
sits in that theorem path.

Li-Liu-Ji 2015 provides the source-facing CV definitions and quotes approximate
crystal endpoints (4AKE open, 1AKE closed). Those published approximate values
are comparison coordinates only; they are not promoted to exact equalities with
these literal mirror projections.

Both PDB chains and both explicit dLN evaluator policies remain available because
neither chain selection nor the exact dLN atom subset is source-paid here.
-/

namespace AgdaMirror.AdK.PDBMirrorCVProjection

open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CVProjection
open AgdaMirror.AdK.PDBMirrorSelectedFixture

structure MirrorCVProjection where
  fixture : PDBMirrorSelectedFixture
  dlnPolicy : AtomPolicy
  contentSurface : ThreeCVContentSurface
  inputSurface : ThreeCVInputSurface

def projectFixture
    (fixture : PDBMirrorSelectedFixture)
    (dlnPolicy : AtomPolicy) : MirrorCVProjection :=
  let content := threeCVContentSurface fixture.configuration dlnPolicy
  { fixture := fixture
    dlnPolicy := dlnPolicy
    contentSurface := content
    inputSurface := content.toInput }

def fourAKEChainABackbone : MirrorCVProjection :=
  projectFixture fourAKEChainA .backbone

def fourAKEChainAHeavy : MirrorCVProjection :=
  projectFixture fourAKEChainA .heavy

def fourAKEChainBBackbone : MirrorCVProjection :=
  projectFixture fourAKEChainB .backbone

def fourAKEChainBHeavy : MirrorCVProjection :=
  projectFixture fourAKEChainB .heavy

def oneAKEChainABackbone : MirrorCVProjection :=
  projectFixture oneAKEChainA .backbone

def oneAKEChainAHeavy : MirrorCVProjection :=
  projectFixture oneAKEChainA .heavy

def oneAKEChainBBackbone : MirrorCVProjection :=
  projectFixture oneAKEChainB .backbone

def oneAKEChainBHeavy : MirrorCVProjection :=
  projectFixture oneAKEChainB .heavy

/-- Li-Liu-Ji identifies PDB entries but does not source-pay a chain choice in
this reconstruction. -/
def chainChoiceSourcePaid : Bool := false

/-- dLN domain ranges are source-paid; the exact atom subset is not. -/
def dlnAtomSubsetSourceResolved : Bool := false

/-- Approximate published endpoint values remain diagnostics, not definitional
equalities attached to the literal mirror data. -/
def publishedApproximateEndpointsPromotedToExactFixtureEqualities : Bool := false

/-- Mirror transport remains artifact provenance only. -/
def mirrorTransportCreatesScientificAuthority : Bool := false

example : fourAKEChainABackbone.fixture.chain = "A" := rfl
example : fourAKEChainBBackbone.fixture.chain = "B" := rfl
example : oneAKEChainAHeavy.dlnPolicy = .heavy := rfl
example : oneAKEChainBBackbone.dlnPolicy = .backbone := rfl

end AgdaMirror.AdK.PDBMirrorCVProjection
