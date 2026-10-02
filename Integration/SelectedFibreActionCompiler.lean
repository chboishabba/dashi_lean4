import Integration.MoonshineNeutralCuspRelationCrossPollination
import Mathlib

/-!
# Selected-fibre action restriction compiler

Generic Lean mirror of the Agda outgoing Sheet9 compiler.

Given an action on Fine × Sheet, the only extra datum required to restrict it
to one sheet fibre is a selected fine point whose fibre is preserved. The
induced sheet action is then forced by second projection, and the exact
intertwining of the selected fibre is compiler output.

This module is deliberately generic. It does not claim that an actual Monster
multiplicity action or an invariant Fine10 fibre has been supplied in Lean.
-/

namespace Integration.SelectedFibreActionCompiler

universe u v w

structure ProductAction (Inertia : Type u) (Fine : Type v) (Sheet : Type w) where
  act : Inertia → (Fine × Sheet) → (Fine × Sheet)

structure SelectedFineInvariant
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    (action : ProductAction Inertia Fine Sheet) where
  selectedFine : Fine
  preserved :
    ∀ inertia sheet,
      (action.act inertia (selectedFine, sheet)).1 = selectedFine

def compiledSheetAct
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    {action : ProductAction Inertia Fine Sheet}
    (invariant : SelectedFineInvariant action)
    (inertia : Inertia) (sheet : Sheet) : Sheet :=
  (action.act inertia (invariant.selectedFine, sheet)).2

theorem compiled_action_stays_in_selected_fibre
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    {action : ProductAction Inertia Fine Sheet}
    (invariant : SelectedFineInvariant action)
    (inertia : Inertia) (sheet : Sheet) :
    action.act inertia (invariant.selectedFine, sheet) =
      (invariant.selectedFine, compiledSheetAct invariant inertia sheet) := by
  apply Prod.ext
  · exact invariant.preserved inertia sheet
  · rfl

structure SheetActionRestriction
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    (action : ProductAction Inertia Fine Sheet) where
  selectedFine : Fine
  sheetAct : Inertia → Sheet → Sheet
  finePreserved :
    ∀ inertia sheet,
      (action.act inertia (selectedFine, sheet)).1 = selectedFine
  intertwines :
    ∀ inertia sheet,
      action.act inertia (selectedFine, sheet) =
        (selectedFine, sheetAct inertia sheet)

def compileRestriction
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    {action : ProductAction Inertia Fine Sheet}
    (invariant : SelectedFineInvariant action) :
    SheetActionRestriction action where
  selectedFine := invariant.selectedFine
  sheetAct := compiledSheetAct invariant
  finePreserved := invariant.preserved
  intertwines := compiled_action_stays_in_selected_fibre invariant

def restrictionToInvariant
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    {action : ProductAction Inertia Fine Sheet}
    (restriction : SheetActionRestriction action) :
    SelectedFineInvariant action where
  selectedFine := restriction.selectedFine
  preserved := restriction.finePreserved

theorem compile_returns_selected_fine
    {Inertia : Type u} {Fine : Type v} {Sheet : Type w}
    {action : ProductAction Inertia Fine Sheet}
    (invariant : SelectedFineInvariant action) :
    (compileRestriction invariant).selectedFine = invariant.selectedFine := rfl

/-! The intended trialectic specialization has a ten-state fine coordinate and
a nine-state outgoing sheet, but the action remains an external input. -/

abbrev Fine10 := Fin 10
abbrev OutgoingNineSheet :=
  Integration.MoonshineNeutralCuspRelationCrossPollination.NinePoint

theorem fine10_count : Fintype.card Fine10 = 10 := by decide
theorem outgoing_sheet_count : Fintype.card OutgoingNineSheet = 9 := by decide

inductive CountSelectsInvariantFineFibre : Prop
inductive CompilerCreatesExternalAction : Prop

theorem count_does_not_select_invariant_fibre :
    ¬ CountSelectsInvariantFineFibre := by
  intro h
  cases h

theorem compiler_does_not_create_external_action :
    ¬ CompilerCreatesExternalAction := by
  intro h
  cases h

structure Boundary where
  genericProductActionOwned : Bool
  invariantFineIsOnlyRestrictionDatum : Bool
  inducedSheetActionIsProjection : Bool
  selectedFibreIntertwiningGenerated : Bool
  restrictionCompilesFromInvariant : Bool
  countSelectsInvariantFineFibre : Bool
  externalActionConstructedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  genericProductActionOwned := true
  invariantFineIsOnlyRestrictionDatum := true
  inducedSheetActionIsProjection := true
  selectedFibreIntertwiningGenerated := true
  restrictionCompilesFromInvariant := true
  countSelectsInvariantFineFibre := false
  externalActionConstructedHere := false

end Integration.SelectedFibreActionCompiler
