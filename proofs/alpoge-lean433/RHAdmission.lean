import Main

/-!
# Exact locally materialized source handoff (isolated pinned toolchain)

DASHI adapter code: the original v4.33.1 source and the licensed v4.35.0
readable/compact rewritings expose the same five names and the byte-identical
Statements.lean. Select and verify the exact source through checkout_fork_source.sh.
The toolchains are separate; no imported olean is carried across versions.
The new licensed source retains Alpöge/Claude/Anthropic provenance.

Do NOT expose `sorry`, `axiom` or a synthesized witness to satisfy this import.
-/

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


/-- Actual all-character zero -> vanishing signed horizontal displacement.
The source predicate is the literal Mathlib LFunction, not a finite proxy.
This is restricted to the original open strip, including imprimitive characters. -/
theorem original_dirichlet_zero_horizontal
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hlo : 0 < s.re) (hhi : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    s.re - (1 / 2 : ℝ) = 0 := by
  rw [original_dirichlet_zeros N χ s hlo hhi hz]
  ring

/-- The exact horizontal factor collapses for the same actual zero.
This does not imply an independent signed ordinate/prime/far estimate. -/
theorem original_dirichlet_cosh_collapse
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hlo : 0 < s.re) (hhi : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) (u : ℝ) :
    Real.cosh ((s.re - (1 / 2 : ℝ)) * u) = 1 := by
  rw [original_dirichlet_zero_horizontal N χ s hlo hhi hz]
  simp

#print axioms original_dirichlet_zero_horizontal
#print axioms original_dirichlet_cosh_collapse

end DASHI.AlpogeRH
