import NSBControl.Rational345R831PhysicalNonlinear
import NSBControl.Rational345R823Cutoff4Separation

/-!
# Cutoff-four touched-only R823 decision compiler

For the radius-four witness, the literal R781/R798 fully-separated family is
empty: the overlap radius is three shells while every retained mode lies in
shell 0, 1, or 2.  Hence the actual R823 separated observables vanish,

  N_sep = 0,   Q_sep = 0,

and the cubic/quintic demand is identically zero.  The only nonlinear semantic
content still needed is that the complete nonlinear selected rate is the
R822 signed comparable/touched fold.

This file compiles that one same-object theorem into the already-built R831
physical reserve decision.
-/

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4
open Rational345R823Cutoff4Separation

/-- Exact remaining cutoff-four semantic datum.  `signedComparableCC` denotes
the real carrier implementation of the actual R822 touched/comparable signed
fold.  The field below is the single same-object theorem still to be proved
from the real R760/R781/R822 primitive cells. -/
structure R823Cutoff4TouchedData where
  signedComparableCC : State → ℝ
  signedComparableCC_continuous : Continuous signedComparableCC
  touched_sameObject :
    ∀ x, IsR823PhysicalState x →
      selectedNonlinear x = signedComparableCC x

/-- The cutoff-four degeneration constructs the generic R823 nonlinear data
with both fully-separated observables identically zero. -/
def physicalNonlinearData_of_cutoff4Touched
    (data : R823Cutoff4TouchedData) : R823PhysicalNonlinearData where
  nestedFourHelicityWork := fun _ => 0
  qsep := fun _ => 0
  signedComparableCC := data.signedComparableCC
  nestedFourHelicityWork_continuous := continuous_const
  qsep_continuous := continuous_const
  signedComparableCC_continuous := data.signedComparableCC_continuous
  nonlinear_sameObject := by
    intro x hx
    rw [data.touched_sameObject x hx]
    ring

/-- Once the one touched-fold same-object theorem is supplied, the negative
R830 physical packet refutes the R823 reserve inequality. -/
theorem r830_refutes_r823_reserve_of_cutoff4Touched
    (data : R823Cutoff4TouchedData) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_physicalNonlinearData
    (physicalNonlinearData_of_cutoff4Touched data)

/-- In this specialized witness the exact R823 demand rate is zero. -/
theorem cutoff4_demandRate_zero
    (data : R823Cutoff4TouchedData) (x : State) :
    (r823PhysicalPointwiseWeld_of_nonlinearData
      (physicalNonlinearData_of_cutoff4Touched data)).demandRate x = 0 := by
  rfl

/-- The separated-family max-cut has removed N_sep and Q_sep from the live
semantic frontier. -/
def r823Cutoff4DecisionReducedToTouchedSameObject : Bool := true

/-- Exact remaining R823 decision leaf after all cutoff-four reductions. -/
def r823Cutoff4TouchedSameObjectClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
