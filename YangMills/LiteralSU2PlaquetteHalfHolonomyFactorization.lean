import Mathlib
import YangMills.LiteralSU2WilsonReflectionPlane

/-!
# Literal 4D plaquette half-holonomy factorization

For the ACTUAL link-derived plaquette
  U_mu(x) U_nu(x+mu) U_mu(x+nu)^(-1) U_nu(x)^(-1),
there are two oriented two-link paths with the same endpoints:

  A = U_mu(x) U_nu(x+mu),
  B = U_nu(x) U_mu(x+nu).

The plaquette is exactly A B^{-1}.  Therefore its normalized SU(2)
Wilson cost is exactly

  1 - q(A,B),

where q is the quaternion relative-trace Gram kernel already used in
the full exponential reflection-positivity proof.

This file closes an important same-object seam: the positive kernel is
not attached to arbitrary independent quaternion variables; it is
evaluated on half-holonomies BUILT FROM THE SAME literal 4D lattice links
as the finite Wilson action.

A full OS reflection theorem still needs the geometric statement that
the chosen crossing plaquettes are exactly the plaquettes crossing one
time-reflection plane and that all remaining action terms split into
the two reflected halves.  The local crossing factor itself is now exact.
-/

namespace RequestProject.YangMills

/-- First oriented two-link path around a literal plaquette. -/
def su2PlaquetteFirstHalfPath {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    SU2PlaquetteHolonomy :=
  links x μ * links (su2Shift x μ) ν

/-- Second oriented two-link path with the same plaquette endpoints. -/
def su2PlaquetteSecondHalfPath {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    SU2PlaquetteHolonomy :=
  links x ν * links (su2Shift x ν) μ

/--
Exact literal-link identity:
plaquette holonomy = first half-path * inverse(second half-path).
-/
theorem su2_plaquette_eq_half_path_relative_holonomy
    {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    su2Plaquette links x μ ν =
      su2PlaquetteFirstHalfPath links x μ ν *
        (su2PlaquetteSecondHalfPath links x μ ν)⁻¹ := by
  unfold su2Plaquette su2PlaquetteFirstHalfPath
    su2PlaquetteSecondHalfPath
  group

/--
The actual normalized fundamental trace of a literal plaquette is the
relative quaternion Gram scalar of its two physical half paths.
-/
theorem su2_literal_plaquette_trace_eq_half_path_gram
    {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    (su2Plaquette links x μ ν).a =
      su2RelativeFundamentalTrace
        (su2PlaquetteFirstHalfPath links x μ ν)
        (su2PlaquetteSecondHalfPath links x μ ν) := by
  rw [su2_plaquette_eq_half_path_relative_holonomy]
  rfl

/--
The positive Wilson plaquette cost on the SAME literal link field is
exactly 1 minus the crossing Gram scalar.
-/
theorem su2_literal_plaquette_cost_eq_one_sub_half_path_gram
    {L : ℕ}
    (links : SU2TorusLinks L)
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    su2PositivePlaquetteCost (su2Plaquette links x μ ν) =
      1 -
        su2RelativeFundamentalTrace
          (su2PlaquetteFirstHalfPath links x μ ν)
          (su2PlaquetteSecondHalfPath links x μ ν) := by
  rw [su2_real_trace_normalization,
    su2_literal_plaquette_trace_eq_half_path_gram]

/-- Literal plaquette descriptors reused by a selected reflection cut. -/
abbrev SU2LiteralPlaquetteIndex (L : ℕ) :=
  SU2TorusSite L × Fin 4 × Fin 4

def su2LiteralCrossingFirstBoundary
    {L : ℕ}
    (links : SU2TorusLinks L) :
    SU2LiteralPlaquetteIndex L → SU2PlaquetteHolonomy :=
  fun p =>
    su2PlaquetteFirstHalfPath links p.1 p.2.1 p.2.2

def su2LiteralCrossingSecondBoundary
    {L : ℕ}
    (links : SU2TorusLinks L) :
    SU2LiteralPlaquetteIndex L → SU2PlaquetteHolonomy :=
  fun p =>
    su2PlaquetteSecondHalfPath links p.1 p.2.1 p.2.2

/--
Sum of literal crossing plaquette normalized traces is exactly the
crossing-boundary Gram sum consumed by the RP theorem.
-/
theorem su2_literal_crossing_trace_sum_eq
    {L : ℕ}
    (crossings : Finset (SU2LiteralPlaquetteIndex L))
    (links : SU2TorusLinks L) :
    (∑ p ∈ crossings, (su2Plaquette links p.1 p.2.1 p.2.2).a) =
      su2CrossingTraceSum crossings
        (su2LiteralCrossingFirstBoundary links)
        (su2LiteralCrossingSecondBoundary links) := by
  unfold su2CrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  exact su2_literal_plaquette_trace_eq_half_path_gram
    links p.1 p.2.1 p.2.2

/--
The product of ACTUAL link-derived Wilson Boltzmann factors on any
finite selected plaquette set equals the abstract crossing-plane kernel
evaluated on the two literal half-path boundary fields.

This is the exact same-object bridge needed by the finite Wilson RP lane.
-/
theorem su2_literal_crossing_wilson_product_eq_kernel
    {L : ℕ}
    (crossings : Finset (SU2LiteralPlaquetteIndex L))
    (links : SU2TorusLinks L)
    (β : ℝ) :
    (∏ p ∈ crossings,
      Real.exp
        (-(β *
          su2PositivePlaquetteCost
            (su2Plaquette links p.1 p.2.1 p.2.2)))) =
      su2WilsonCrossingPlaneKernel crossings β
        (su2LiteralCrossingFirstBoundary links)
        (su2LiteralCrossingSecondBoundary links) := by
  rw [show
    (∏ p ∈ crossings,
      Real.exp
        (-(β *
          su2PositivePlaquetteCost
            (su2Plaquette links p.1 p.2.1 p.2.2)))) =
      Real.exp
        (∑ p ∈ crossings,
          -(β *
            su2PositivePlaquetteCost
              (su2Plaquette links p.1 p.2.1 p.2.2))) by
        symm
        exact Real.exp_sum crossings
          (fun p =>
            -(β *
              su2PositivePlaquetteCost
                (su2Plaquette links p.1 p.2.1 p.2.2)))]
  unfold su2WilsonCrossingPlaneKernel
  rw [← Real.exp_add]
  congr 1
  rw [← su2_literal_crossing_trace_sum_eq crossings links]
  simp_rw [su2_literal_plaquette_cost_eq_one_sub_half_path_gram]
  simp only [su2_literal_plaquette_trace_eq_half_path_gram]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const_zero, sub_zero]
  have hcard :
      (∑ _p ∈ crossings, (1 : ℝ)) =
        (crossings.card : ℝ) := by simp
  rw [show
    (∑ p ∈ crossings,
      -(β *
        (1 -
          su2RelativeFundamentalTrace
            (su2PlaquetteFirstHalfPath links p.1 p.2.1 p.2.2)
            (su2PlaquetteSecondHalfPath links p.1 p.2.1 p.2.2)))) =
      -(β * (crossings.card : ℝ)) +
        β *
          (∑ p ∈ crossings,
            su2RelativeFundamentalTrace
              (su2PlaquetteFirstHalfPath links p.1 p.2.1 p.2.2)
              (su2PlaquetteSecondHalfPath links p.1 p.2.1 p.2.2)) by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, hcard]
        ring]
  ring

end RequestProject.YangMills
