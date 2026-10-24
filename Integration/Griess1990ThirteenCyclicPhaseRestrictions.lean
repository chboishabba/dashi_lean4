import Integration.Griess1990RationalF3CubedActualAction
import Integration.Griess1990RationalTrialityMatrixWitness
import Mathlib

/-!
# All thirteen cyclic C3 restrictions of Griess's A=(Z/3)^3

Original mathematics: Robert L. Griess Jr., *J. Algebra* 131 (1990)
281-293, DOI 10.1016/0021-8693(90)90176-O. Griess constructs an
elementary-abelian normal subgroup A=(Z/3)^3 with normalizer SL3(3)
on the COMPLEX Albert algebra. This formal source restricts its
actual Q-rational tau-real Albert character matrices built upstream.

There are thirteen *lines* in F3^3, i.e. thirteen different order-three
subgroups. Each restricted C3 has rational fixed-dimension nine,
cyclotomic complement dimension eighteen, and over Q(omega) three
phase eigenspaces dimension nine apiece. For any two distinct lines
the common fixed space has dimension three; for the three chosen
independent axes, it has dimension one (the original Albert unit).

This is the explicit comparison the earlier 883/8 vs 888/8 question
needed: the source-selected symmetry gives THIRTEEN possible cyclic
phase axes; no source theorem singles out the arbitrary octonion
coordinate rotation responsible for engineered 888/8.

Chen--Lam--Shimakura's separate Z3-orbifold Moonshine VOA V^sharp
(arXiv:1606.05961; Math. Z. 288, 2018) does have source-established
three phase sectors. This 27D finite Albert eigenspace is NOT those
infinite VOA summands, and does not construct a selected Monster
3B same-element chart, a Vnatural mode or any physical observable.

All native_decide declarations below are SOURCE-WRITTEN; the
Lean/Lake kernel did not run in the authoring environment.
-/

namespace Integration.Griess1990ThirteenCyclicPhaseRestrictions

open Integration.Griess1990RationalF3CubedActualAction
open Integration.Griess1990RationalTrialityMatrixWitness

/-- Antipodal representatives in lexicographic F3^3 order.
This is the actual 13-line projective plane over F3, not 13
separately hypothesized physical charge sectors. -/
def lineDirection : Fin 13 → Fin 3 × Fin 3 × Fin 3 :=
![
  (0, 0, 1),
  (0, 1, 0),
  (0, 1, 1),
  (0, 1, 2),
  (1, 0, 0),
  (1, 0, 1),
  (1, 0, 2),
  (1, 1, 0),
  (1, 1, 1),
  (1, 1, 2),
  (1, 2, 0),
  (1, 2, 1),
  (1, 2, 2)
]

/-- Restrict the SAME Q-linear Griess character action to a chosen
order-three direction. The result is an actual 27x27 matrix. -/
def sourceLineGenerator (i : Fin 13) : Matrix (Fin 27) (Fin 27) ℚ :=
  let d := lineDirection i
  sourceGenerator0 ^ d.1.val *
    sourceGenerator1 ^ d.2.1.val *
      sourceGenerator2 ^ d.2.2.val

/-- Averaging idempotent for invariants of this chosen C3. -/
def sourceLineFixedProjector (i : Fin 13) :
    Matrix (Fin 27) (Fin 27) ℚ :=
  (1/3 : ℚ) •
    ((1 : Matrix (Fin 27) (Fin 27) ℚ) +
      sourceLineGenerator i + (sourceLineGenerator i)^2)

theorem all_thirteen_cyclic_orders :
    ∀ i : Fin 13, (sourceLineGenerator i)^3 = 1 := by
  native_decide

theorem all_thirteen_fixed_idempotents :
    ∀ i : Fin 13,
      sourceLineFixedProjector i * sourceLineFixedProjector i =
        sourceLineFixedProjector i := by
  native_decide

/-- Rank=trace for each rational idempotent; trace=9 is a
checkable precise fixed-dimension receipt. -/
theorem all_thirteen_rational_fixed_dimensions :
    ∀ i : Fin 13,
      Matrix.trace (sourceLineFixedProjector i) = (9 : ℚ) := by
  native_decide

theorem every_distinct_line_pair_common_fixed_dimension :
    ∀ i j : Fin 13, i ≠ j →
      Matrix.trace
        (sourceLineFixedProjector i * sourceLineFixedProjector j) =
        (3 : ℚ) := by
  native_decide

/-- The selected three independent axes are lines 4,1,0 in the
lexicographically ordered projective F3^3 directions. -/
theorem three_axis_common_fixed_is_unit_projection :
    sourceLineFixedProjector 4 *
      sourceLineFixedProjector 1 *
        sourceLineFixedProjector 0 =
      (fun (i : Fin 27) (j : Fin 27) =>
        if i = 0 ∧ j = 0 then (1 : ℚ) else 0) := by
  native_decide

/-- The actual original Albert unit is fixed by all thirteen
cyclic subgroups: no arbitrary spatial-origin-site identification. -/
theorem same_source_unit_fixed_in_all_thirteen :
    ∀ i : Fin 13,
      applyWitness (sourceLineFixedProjector i) sourceOne =
      sourceOne := by
  native_decide

/-- Restrict each of the 13 subgroups to the literal NATIVE
Cayley-Dickson Albert using the already-constructed invertible
rational same-object 27×27 matrix. -/
def nativeLineFixedProjector (i : Fin 13) :
    Matrix (Fin 27) (Fin 27) ℚ :=
  sourceToNative * sourceLineFixedProjector i * nativeToSource

theorem same_native_thirteen_trace_dimensions :
    ∀ i : Fin 13, Matrix.trace (nativeLineFixedProjector i) = 9 := by
  native_decide

end Integration.Griess1990ThirteenCyclicPhaseRestrictions
