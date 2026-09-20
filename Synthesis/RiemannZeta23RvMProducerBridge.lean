import Zeta23.Hypotheses
import Zeta23.RvM.LocalCount

/-!
# Exact Zeta23 Riemann--von Mangoldt producer bridge

The RH branch had previously consumed only

  Zeta23.RvM.zetaZeroConfig_local_count.

The upstream Zeta23 development actually packages the stronger analytic inputs
in `PaperInputs` and discharges that package for the literal zeta zero
configuration by `paperInputs_zeta`.

This file deliberately starts with the narrowest possible same-object bridge:
it aliases the exact upstream theorem-bearing object and its RvM component
without restating or weakening either theorem.

The next module may destructure the RvM main-term field once its v4.28-facing
field shape has been checked.  No Boolean receipt or replacement hypothesis is
introduced here.
-/

noncomputable section

namespace Synthesis

open Zeta23

/-- The exact theorem-bearing analytic-input package for Mathlib's zeta zeros. -/
def literalZetaPaperInputs := paperInputs_zeta

/-- The exact Riemann--von Mangoldt component of the literal zeta input package. -/
def literalZetaRvM := paperInputs_zeta.RvM

/--
The already-consumed local-count theorem is on the same literal
`zetaZeroConfig`; retain it beside the stronger RvM package so subsequent
transport cannot silently change zero carriers.
-/
def literalZetaLocalCount := Zeta23.RvM.zetaZeroConfig_local_count

end Synthesis
