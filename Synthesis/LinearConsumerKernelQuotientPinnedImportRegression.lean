import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Synthesis.LinearConsumerKernelQuotient

/-!
Pinned-import regression for the generic consumer-family kernel bypass.

The producer must use mathlib modules that exist at the repository-pinned
`v4.28.0` tag.  This regression keeps the required theorem surface visible
without introducing any RSA/CADO semantics.
-/

namespace Synthesis

#check LinearMap.ker
#check Submodule.mem_iInf
#check same_outputs_iff_sub_mem_iInf_ker
#check jointly_injective_of_iInf_ker_eq_bot

end Synthesis
