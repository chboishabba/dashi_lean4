import Statements
import Supplements.Kernels.MainTheorems

/-!
# Minimal top-level RH/GRH dependency cut in the author's original Lean 4.33.1

Source-preserving STEELMAN/BIDI/REVERSE SOLVE.

The original fork's src/Main.lean imports
`Supplements.Kernels.MainTheoremsAll`, which additionally imports
`MainTheoremsCritical` and `...SmallClassNumbers.CorGKOf`.
The five published theorem bodies use `rhOfAll`, `allChi`,
`claimAll.2.1`, and `critAll`, all defined in the narrower
`Supplements.Kernels.MainTheorems`.

This external fork's source dependencies remain intact; this file merely
selects a smaller root import closure. It does NOT assert that the imported
source graph is small, replace any original axiom, or add a proof shortcut.
Build only in the pinned fork's original Lean 4.33.1 environment.
-/

namespace DASHI.AlpogeRH.TopCut

theorem rh_from_original_core : RiemannHypothesis :=
  _root_.rhOfAll

theorem explicit_zeta_zeros_from_original_core :
    RiemannZetaZerosOnLine :=
  _root_.rhOfAll

theorem dirichlet_right_half_from_original_core :
    DirichletLNonvanishingRightOfHalf :=
  _root_.allChi

theorem dirichlet_critical_strip_from_original_core :
    DirichletLZerosOnLine :=
  (_root_.claimAll).2.1

theorem primitive_dirichlet_critical_strip_from_original_core :
    PrimitiveDirichletLZerosOnLine :=
  _root_.critAll

#print axioms rh_from_original_core
#print axioms explicit_zeta_zeros_from_original_core
#print axioms dirichlet_right_half_from_original_core
#print axioms dirichlet_critical_strip_from_original_core
#print axioms primitive_dirichlet_critical_strip_from_original_core

end DASHI.AlpogeRH.TopCut
