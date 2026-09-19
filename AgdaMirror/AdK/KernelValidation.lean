import AgdaMirror.AdK.NonFactorability
import AgdaMirror.AdK.PDBMirrorSelectionCardinality
import AgdaMirror.AdK.PDBMirrorCVProjection
import AgdaMirror.AdK.PDBMirrorSourceEndpointAudit

/-!
# AdK exact-CV kernel validation

This root checks both:
1. the abstract canonical non-factorability/recharting theorem; and
2. the real 4AKE/1AKE A/B selected-mirror manifestations carried through the
   same typed selection/content/COM/CV spine.

Attribution remains upstream:
- Li-Liu-Ji 2015 owns the source-facing CV selection/domain roles.
- Prohaska et al. owns the adopted rounded atomic-mass convention.
- Crenshaw 1991 is conceptual motivation for the generic source lane, not owner
  of the DASHI factorisation theorem.
- mirror Git objects remain transport provenance only.
- DASHI owns the exact rational reconstruction and bridge mathematics.

`#print axioms` remains so future elaboration exposes actual kernel dependency
surfaces rather than relying only on source inspection.
-/

namespace AgdaMirror.AdK.KernelValidation

open AgdaMirror.AdK.NonFactorability
open AgdaMirror.AdK.PDBMirrorSelectionCardinality
open AgdaMirror.AdK.PDBMirrorCVProjection
open AgdaMirror.AdK.PDBMirrorSourceEndpointAudit

#check adkConfigurationNonFactorabilityWitness
#check adkThreeCVInput_not_factors_through
#check adkThreeCVRecharting_not_factors_through

#check fourAKEChainASelectionCardinalityExact
#check fourAKEChainBSelectionCardinalityExact
#check oneAKEChainASelectionCardinalityExact
#check oneAKEChainBSelectionCardinalityExact

#check fourAKEChainABackbone.inputSurface
#check fourAKEChainBBackbone.inputSurface
#check oneAKEChainABackbone.inputSurface
#check oneAKEChainBBackbone.inputSurface

#check fourAKEChainAHeavy.inputSurface
#check fourAKEChainBHeavy.inputSurface
#check oneAKEChainAHeavy.inputSurface
#check oneAKEChainBHeavy.inputSurface

#check fourAKEChainABackboneDiagnostic
#check oneAKEChainABackboneDiagnostic

#print axioms adkThreeCVInput_not_factors_through
#print axioms adkThreeCVRecharting_not_factors_through
#print axioms fourAKEChainASelectionCardinalityExact

end AgdaMirror.AdK.KernelValidation
