import Main

/-!
# Exact locally materialized source handoff (Lean/Mathlib 4.33.1 ONLY)

This file is new DASHI adapter code, not a copy of the unlicensed external
submission. It is compilable only when the user has separately acquired the
published original source from its author, checked the exact archive SHA-256,
and provided its original `Main` and dependencies in this isolated toolchain.

Do NOT expose `sorry`, `axiom` or a synthesized witness to satisfy this import.
-/-

namespace DASHI.AlpogeRH

/-- Original submitted theorem, not a restated RH axiom. -/
theorem original_mathlib_rh : RiemannHypothesis :=
  _root_.riemannHypothesis

/-- Actual same-source zero-location theorem. -/
theorem original_riemann_zero_location : RiemannZetaZerosOnLine :=
  _root_.riemannZeta_eq_zero_re

/-- All-Dirichlet-character nonvanishing, with original source scope. -/
theorem original_dirichlet_nonvanishing :
    DirichletLNonvanishingRightOfHalf :=
  _root_.LFunction_ne_zero_of_half_lt_re

/-- All-Dirichlet-character critical-strip zero-location. -/
theorem original_dirichlet_zeros : DirichletLZerosOnLine :=
  _root_.LFunction_eq_zero_re

/-- Primitive-character critical-strip zero-location. -/
theorem original_primitive_dirichlet_zeros :
    PrimitiveDirichletLZerosOnLine :=
  _root_.LFunction_eq_zero_re_of_isPrimitive

#print axioms original_mathlib_rh
#print axioms original_riemann_zero_location
#print axioms original_dirichlet_nonvanishing
#print axioms original_dirichlet_zeros
#print axioms original_primitive_dirichlet_zeros

end DASHI.AlpogeRH
