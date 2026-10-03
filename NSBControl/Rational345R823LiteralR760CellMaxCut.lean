import NSBControl.Rational345R823RealSemanticProvenance
import NSBControl.Rational345R823TouchedPartition

/-!
# One-leaf literal R760 max-cut for the R823 decision lane

After the real R823 definitions are ported, the cutoff-four decision lane no
longer has an independent semantic-reserve leaf and a separate touched-carrier
leaf.  Both reduce to one same-object statement about the complete literal R760
cell fold.

This file packages a genuine cellwise carrier over the real radius-four mode
cube.  R781/R822 touched selection contributes no further theorem at cutoff
four: the touched fold is the complete fold.  Therefore once the complete
literal R760 cell sum is identified with the already-proved R760 scalar normal
form, all reserve/demand semantics, R830 integration, and R831 contradiction
follow automatically.

The remaining cell formula itself is deliberately not guessed here.  It must be
instantiated by the real port of the R749/R760 original signed cell, preserving
its original multiplicity.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823LiteralR760CellMaxCut

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823TouchedNormalForm
open Rational345R823TouchedPartition
open Rational345R823RealSemanticProvenance

/-- Concrete finite incidence address for the real radius-four R760 fold. -/
abbrev R760Incidence := Mode × Mode × Mode

/-- A literal real R760 cell carrier.  Continuity is a routine finite-cell
certificate; the only substantive field is that the complete
original-multiplicity cell sum is the R760 scalar total already normalized to
`selectedNonlinear`. -/
structure LiteralR760CellCarrier where
  cell : State → R760Incidence → ℝ

  completeFold_continuous :
    Continuous (fun x : State => ∑ i : R760Incidence, cell x i)

  completeFold_sameObject :
    ∀ x, IsR823PhysicalState x →
      (∑ i : R760Incidence, cell x i) = r760SwapPairedResidualTotal x

/-- Complete original-multiplicity R760 cell sum. -/
def literalR760CompleteFold
    (data : LiteralR760CellCarrier) (x : State) : ℝ :=
  ∑ i : R760Incidence, data.cell x i

/-- R781/R822 touched fold at cutoff four.  The generic touched partition is
used explicitly so this is visibly a selector result rather than an alias. -/
def literalR760TouchedFold
    (data : LiteralR760CellCarrier) (x : State) : ℝ :=
  ccTouchedFold4 (fun i : R760Incidence => data.cell x i)

/-- Cutoff-four R781 degeneracy: every retained original R760 cell is touched,
so the touched fold is exactly the complete fold with unchanged multiplicity. -/
theorem literalR760TouchedFold_eq_completeFold
    (data : LiteralR760CellCarrier) (x : State) :
    literalR760TouchedFold data x = literalR760CompleteFold data x := by
  exact ccTouchedFold4_eq_completeFold
    (fun i : R760Incidence => data.cell x i)

/-- Continuity of the complete literal fold is part of the concrete cell
carrier certificate. -/
theorem literalR760CompleteFold_continuous
    (data : LiteralR760CellCarrier) :
    Continuous (literalR760CompleteFold data) := by
  exact data.completeFold_continuous

/-- The touched fold inherits continuity from its exact equality with the
complete finite fold. -/
theorem literalR760TouchedFold_continuous
    (data : LiteralR760CellCarrier) :
    Continuous (literalR760TouchedFold data) := by
  have hfun : literalR760TouchedFold data = literalR760CompleteFold data := by
    funext x
    exact literalR760TouchedFold_eq_completeFold data x
  rw [hfun]
  exact literalR760CompleteFold_continuous data

/-- One complete-fold same-object theorem constructs the previous two-step
R760-cellwise -> R781/R822-touched carrier interface. -/
def touchedCarrierWeld_of_literalR760Cell
    (data : LiteralR760CellCarrier) :
    R823Cutoff4TouchedCarrierWeldData where
  r760CellwiseFold := literalR760CompleteFold data
  touchedSignedFold := literalR760TouchedFold data
  touchedSignedFold_continuous := literalR760TouchedFold_continuous data
  touched_eq_r760Cellwise := by
    intro x _hx
    exact literalR760TouchedFold_eq_completeFold data x
  r760Cellwise_eq_totalNormalForm := by
    intro x hx
    exact data.completeFold_sameObject x hx

/-- The one literal R760 complete-fold theorem reaches the definition-faithful
real R823 terminal semantic interface. -/
def terminalSemanticWeld_of_literalR760Cell
    (data : LiteralR760CellCarrier) :
    R823PhysicalReserveSemanticWeld :=
  realSemanticWeld_of_literalTouchedCarrier
    (touchedCarrierWeld_of_literalR760Cell data)

/-- Terminal decision compiler from the single literal R760 cell carrier. -/
theorem r830_refutes_r823_reserve_of_literalR760Cell
    (data : LiteralR760CellCarrier) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_terminalSemanticWeld
    (terminalSemanticWeld_of_literalR760Cell data)

/-- All semantic/touched/integration machinery has been compressed to the
complete literal R760 cell-fold identification. -/
def r823DecisionReducedToLiteralR760CompleteFold : Bool := true

/-- Honest final source-level mathematical leaf. -/
def r823LiteralR760CompleteFoldSameObjectClosed : Bool := false

end Rational345R823LiteralR760CellMaxCut
end NSBControl
