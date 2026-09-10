/-!
# Reusable Spine

Domain-neutral Lean infrastructure recovered from the TOE consolidation.
It owns generic observer, Gram/Schur, phase, norm, finite-reindexing, and
two-regime constructions.  Domain lanes should adapt to this surface instead
of duplicating its algebra; imports remain evidence of reuse, not a claim that
the domain-specific hypotheses have been discharged.
-/

import Spine.EndToEnd
import Spine.RateBlockSchur
import Spine.TwoRegime
import Spine.RiemannBridge
import Spine.JMD
