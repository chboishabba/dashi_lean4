import AgdaMirror.AdK.PDBMirrorCVProjection
import AgdaMirror.AdK.PDBMirrorSelectionCardinality

/-!
# AdK real-mirror runtime probe

This file is intentionally executable rather than theorem-authoritative.  Once a
Lean execution surface is available it prints the exact rational CV input
surfaces computed from the transparent mirror rows and the kernel-computed
selection cardinality profiles.

The resulting log is an execution receipt. It does not create scientific source
authority or canonical wwPDB byte parity.
-/

open AgdaMirror.AdK.PDBMirrorCVProjection
open AgdaMirror.AdK.PDBMirrorSelectionCardinality

#eval fourAKEChainASelectionCardinality
#eval fourAKEChainBSelectionCardinality
#eval oneAKEChainASelectionCardinality
#eval oneAKEChainBSelectionCardinality

#eval fourAKEChainABackbone.inputSurface
#eval fourAKEChainAHeavy.inputSurface
#eval fourAKEChainBBackbone.inputSurface
#eval fourAKEChainBHeavy.inputSurface

#eval oneAKEChainABackbone.inputSurface
#eval oneAKEChainAHeavy.inputSurface
#eval oneAKEChainBBackbone.inputSurface
#eval oneAKEChainBHeavy.inputSurface
