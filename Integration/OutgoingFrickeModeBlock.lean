import Integration.TrialecticIncomingFrickeSeparation
import Integration.SelectedFibreActionCompiler
import Integration.MoonshineC6TenRankWeightTwelveCrossPollination
import Integration.MoonshineNeutralCuspRelationCrossPollination
import Mathlib

/-!
# Outgoing Fricke-like fine motion: 9-state no-go and 18-state replacement

Lean mirror of the Agda outgoing recognition fork.

For a product action on Completion10 × NinePoint:

* an invariant selected completion state gives a 9-state sheet restriction via
  the generic selected-fibre compiler;
* if a distinguished action element projects on Completion10 as finiteFricke,
  no selected single fine fibre can be invariant;
* finiteFricke preserves Mode5 and flips Phase2, so the natural stable block
  over one mode is Phase2 × NinePoint, with 18 states.
-/

namespace Integration.OutgoingFrickeModeBlock

open Integration.TrialecticIncomingFrickeSeparation
open Integration.SelectedFibreActionCompiler
open Integration.MoonshineC6TenRankWeightTwelveCrossPollination
open Integration.MoonshineNeutralCuspRelationCrossPollination

abbrev FineCarrier := Completion10
abbrev Sheet9 := NinePoint

def flipPhase2 : Phase2 → Phase2
  | .direct => .counter
  | .counter => .direct

theorem flipPhase2_involutive (p : Phase2) :
    flipPhase2 (flipPhase2 p) = p := by
  cases p <;> rfl

theorem finiteFricke_mode_phase (m : Mode5) (p : Phase2) :
    finiteFricke (modePhaseToTen (m,p)) =
      modePhaseToTen (m, flipPhase2 p) := by
  cases m <;> cases p <;> rfl

structure FineFrickeElement
    {Inertia : Type} (action : ProductAction Inertia FineCarrier Sheet9) where
  frickeInertia : Inertia
  fineProjectionIsFricke :
    ∀ fine sheet,
      (action.act frickeInertia (fine,sheet)).1 = finiteFricke fine

theorem fine_fricke_element_rejects_selected_fine
    {Inertia : Type}
    {action : ProductAction Inertia FineCarrier Sheet9}
    (element : FineFrickeElement action)
    (invariant : SelectedFineInvariant action) :
    False := by
  let sheet : Sheet9 := (.zero,.zero)
  have hfricke :
      (action.act element.frickeInertia
        (invariant.selectedFine,sheet)).1 =
        finiteFricke invariant.selectedFine :=
    element.fineProjectionIsFricke invariant.selectedFine sheet
  have hfixed :
      finiteFricke invariant.selectedFine = invariant.selectedFine :=
    hfricke.symm.trans (invariant.preserved element.frickeInertia sheet)
  exact finiteFricke_no_fixed_point invariant.selectedFine hfixed

abbrev ModeBlock18 := Phase2 × Sheet9

theorem mode_block_count :
    Fintype.card ModeBlock18 = 18 := by
  native_decide

def embedModeBlock (mode : Mode5) : ModeBlock18 → FineCarrier × Sheet9
  | (phase,sheet) => (modePhaseToTen (mode,phase),sheet)

def compiledFrickeBlockAct
    {Inertia : Type}
    {action : ProductAction Inertia FineCarrier Sheet9}
    (element : FineFrickeElement action)
    (mode : Mode5) : ModeBlock18 → ModeBlock18
  | (phase,sheet) =>
      (flipPhase2 phase,
       (action.act element.frickeInertia
         (modePhaseToTen (mode,phase),sheet)).2)

theorem compiled_fricke_block_intertwines
    {Inertia : Type}
    {action : ProductAction Inertia FineCarrier Sheet9}
    (element : FineFrickeElement action)
    (mode : Mode5)
    (state : ModeBlock18) :
    action.act element.frickeInertia (embedModeBlock mode state) =
      embedModeBlock mode (compiledFrickeBlockAct element mode state) := by
  rcases state with ⟨phase,sheet⟩
  apply Prod.ext
  · calc
      (action.act element.frickeInertia
        (modePhaseToTen (mode,phase),sheet)).1
          = finiteFricke (modePhaseToTen (mode,phase)) :=
            element.fineProjectionIsFricke _ _
      _ = modePhaseToTen (mode,flipPhase2 phase) :=
            finiteFricke_mode_phase mode phase
  · rfl

inductive ActualMonsterFineFrickeElementRecognized : Prop
inductive NineStateSheetInvariantUnderFineFricke : Prop

theorem nine_state_sheet_not_invariant_under_fine_fricke :
    ¬ NineStateSheetInvariantUnderFineFricke := by
  intro h
  cases h

theorem actual_monster_fine_fricke_element_still_open :
    ¬ ActualMonsterFineFrickeElementRecognized := by
  intro h
  cases h

structure Boundary where
  fineFrickeElementContractOwned : Bool
  singleFineInvariantRejectedUnderFricke : Bool
  modeBlockPhase2TimesSheet9Owned : Bool
  modeBlockCount18 : Bool
  finiteFrickePreservesModeAndFlipsPhase : Bool
  frickeBlockActionCompilerOwned : Bool
  actualMonsterFineFrickeElementPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fineFrickeElementContractOwned := true
  singleFineInvariantRejectedUnderFricke := true
  modeBlockPhase2TimesSheet9Owned := true
  modeBlockCount18 := true
  finiteFrickePreservesModeAndFlipsPhase := true
  frickeBlockActionCompilerOwned := true
  actualMonsterFineFrickeElementPaid := false

end Integration.OutgoingFrickeModeBlock
