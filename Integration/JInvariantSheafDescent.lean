import Mathlib

namespace Integration.JInvariantSheafDescent

universe u v

/-!
Finite Lean mirror of the DASHI Agda J/369 coarse/fine, descent, admissibility,
and sheaf-facing surface.

Agda remains the richer source for the explicit 1+10 <-> 2+9 chart shift,
pants codecs, Base369 hyperfabric and WrongType provenance.  This file mirrors
the finite theorem shape and exposes standard Lean category/sheaf vocabulary
without promoting the finite observer to a literal analytic modular sheaf.
-/

abbrev Trit := Fin 3
abbrev JCoarse := Trit × Trit
abbrev JFine := JCoarse → Trit
abbrev JAbs := JCoarse × JFine
abbrev Local27 := JCoarse × Trit

def triLow : Trit := ⟨0, by decide⟩
def triMid : Trit := ⟨1, by decide⟩
def triHigh : Trit := ⟨2, by decide⟩

def localObserver : JAbs → Local27
  | (q, f) => (q, f q)

def constantFine (t : Trit) : JFine := fun _ => t

def localSection : Local27 → JAbs
  | (q, t) => (q, constantFine t)

theorem localObserver_section (v : Local27) :
    localObserver (localSection v) = v := by
  cases v
  rfl

theorem card_jCoarse : Fintype.card JCoarse = 9 := by
  native_decide

theorem card_jFine : Fintype.card JFine = 19683 := by
  native_decide

theorem card_jAbs : Fintype.card JAbs = 177147 := by
  native_decide

theorem card_local27 : Fintype.card Local27 = 27 := by
  native_decide

theorem card_localObserver_fibre_shadow :
    27 * 6561 = 177147 := by
  norm_num

def q00 : JCoarse := (triLow, triLow)
def q11 : JCoarse := (triMid, triMid)

def flatMidField : JFine := fun _ => triMid

def q11RaisedField : JFine :=
  fun q => if q = q11 then triHigh else triMid

def leftJState : JAbs := (q00, flatMidField)
def rightJState : JAbs := (q00, q11RaisedField)

theorem q00_ne_q11 : q00 ≠ q11 := by
  decide

theorem sameLocal27 :
    localObserver leftJState = localObserver rightJState := by
  simp [localObserver, leftJState, rightJState, q11RaisedField, flatMidField,
    q00_ne_q11]

def fineFieldAt (q : JCoarse) : JAbs → Trit
  | (_, f) => f q

theorem q11ConsumerDiffers :
    fineFieldAt q11 leftJState ≠ fineFieldAt q11 rightJState := by
  simp [fineFieldAt, leftJState, rightJState, flatMidField, q11RaisedField,
    q11, triMid, triHigh]

structure FactorsThrough
    {State Surface Outcome : Type}
    (observe : State → Surface)
    (consumer : State → Outcome) where
  factor : Surface → Outcome
  law : ∀ state, consumer state = factor (observe state)

def chosenLocalValue : JAbs → Trit :=
  fun state => (localObserver state).2

def chosenLocalValueFactorsThrough :
    FactorsThrough localObserver chosenLocalValue where
  factor := Prod.snd
  law := by intro state; rfl

theorem q11CannotFactorThroughLocal
    (h : FactorsThrough localObserver (fineFieldAt q11)) : False := by
  apply q11ConsumerDiffers
  calc
    fineFieldAt q11 leftJState
        = h.factor (localObserver leftJState) := h.law leftJState
    _ = h.factor (localObserver rightJState) := by rw [sameLocal27]
    _ = fineFieldAt q11 rightJState := (h.law rightJState).symm

structure CompatibleOverlap
    {Left Right Boundary : Type}
    (leftBoundary : Left → Boundary)
    (rightBoundary : Right → Boundary) where
  left : Left
  right : Right
  sameBoundary : leftBoundary left = rightBoundary right

def JLocalPullback :=
  CompatibleOverlap localObserver localObserver

def jLocalCollisionInPullback : JLocalPullback where
  left := leftJState
  right := rightJState
  sameBoundary := sameLocal27

structure CoarseFineReopening (FineState : Type) where
  Coarse : Type
  RelativeFine : Type
  coarse : FineState → Coarse
  relativeFine : FineState → RelativeFine
  reopen : Coarse → RelativeFine → FineState
  reopenExact : ∀ state, reopen (coarse state) (relativeFine state) = state

theorem coarseAndRelativeFineDetermineState
    {FineState : Type}
    (g : CoarseFineReopening FineState)
    {left right : FineState}
    (hc : g.coarse left = g.coarse right)
    (hf : g.relativeFine left = g.relativeFine right) :
    left = right := by
  calc
    left = g.reopen (g.coarse left) (g.relativeFine left) :=
      (g.reopenExact left).symm
    _ = g.reopen (g.coarse right) (g.relativeFine left) := by rw [hc]
    _ = g.reopen (g.coarse right) (g.relativeFine right) := by rw [hf]
    _ = right := g.reopenExact right

theorem relativeFineMustSeparateDistinctStates
    {FineState : Type}
    (g : CoarseFineReopening FineState)
    {left right : FineState}
    (hc : g.coarse left = g.coarse right)
    (hne : left ≠ right) :
    g.relativeFine left ≠ g.relativeFine right := by
  intro hf
  exact hne (coarseAndRelativeFineDetermineState g hc hf)

structure AdmissibleOverlap
    {Left Right Boundary : Type}
    (leftBoundary : Left → Boundary)
    (rightBoundary : Right → Boundary)
    (Allowed : Left → Right → Prop) where
  overlap : CompatibleOverlap leftBoundary rightBoundary
  allowed : Allowed overlap.left overlap.right

structure AdmissiblePushoutInterface
    {Left Right Seam : Type}
    (seamLeft : Seam → Left)
    (seamRight : Seam → Right) where
  Glued : Type
  includeLeft : Left → Glued
  includeRight : Right → Glued
  seamCommutes :
    ∀ s, includeLeft (seamLeft s) = includeRight (seamRight s)
  descend :
    ∀ {Target : Type}
      (fromLeft : Left → Target)
      (fromRight : Right → Target),
      (∀ s, fromLeft (seamLeft s) = fromRight (seamRight s)) →
      Glued → Target

inductive WrongTypeMismatch
  | nonFactorableRepresentation
  | inadmissibleCandidate
  | invalidInferenceTransport
  deriving DecidableEq, Repr

structure WrongTypeReceipt where
  obligation : String
  candidate : String
  mismatch : WrongTypeMismatch
  rejection : String
  candidateMayStillExist : Bool

def local27Q11WrongTypeReceipt : WrongTypeReceipt where
  obligation := "JCoarse/JFine:q11-consumer factorisation"
  candidate := "local 27 observer"
  mismatch := .nonFactorableRepresentation
  rejection := "same local 27 but distinct q11 fine-field value"
  candidateMayStillExist := true

theorem cardinalCompatibilityDoesNotSupplyAdmissibility :
    ¬ (∀ {Left Right Boundary : Type}
      (l : Left → Boundary) (r : Right → Boundary),
      Nonempty (CompatibleOverlap l r) →
      ∀ (Allowed : Left → Right → Prop),
      Nonempty (AdmissibleOverlap l r Allowed)) := by
  intro h
  let l : Unit → Unit := fun _ => ()
  let r : Unit → Unit := fun _ => ()
  have compat : Nonempty (CompatibleOverlap l r) :=
    ⟨{ left := (), right := (), sameBoundary := rfl }⟩
  let Never : Unit → Unit → Prop := fun _ _ => False
  obtain ⟨a⟩ := h l r compat Never
  exact a.allowed

/- Standard Lean category-theory surfaces corresponding to the proposed
   C^op -> Set formalism.  No concrete analytic modular site is asserted. -/
open CategoryTheory

abbrev Presheaf (C : Type u) [Category C] :=
  Cᵒᵖ ⥤ Type v

abbrev SiteTopology (C : Type u) [Category C] :=
  GrothendieckTopology C

abbrev PantsPath (n : Nat) := Fin n → Trit

def nineToPants2 : JCoarse → PantsPath 2
  | (a, b) => fun i => if i = (0 : Fin 2) then a else b

def pants2ToNine : PantsPath 2 → JCoarse :=
  fun p => (p (0 : Fin 2), p (1 : Fin 2))

theorem pants2_nine_roundtrip (q : JCoarse) :
    pants2ToNine (nineToPants2 q) = q := by
  rcases q with ⟨a, b⟩
  simp [pants2ToNine, nineToPants2]

theorem nine_pants2_roundtrip (p : PantsPath 2) :
    nineToPants2 (pants2ToNine p) = p := by
  funext i
  fin_cases i <;> simp [nineToPants2, pants2ToNine]

def local27ToPants3 : Local27 → PantsPath 3
  | ((a, b), c) => fun i =>
      if i = (0 : Fin 3) then a
      else if i = (1 : Fin 3) then b
      else c

def pants3ToLocal27 : PantsPath 3 → Local27 :=
  fun p => ((p (0 : Fin 3), p (1 : Fin 3)), p (2 : Fin 3))

theorem pants3_local27_roundtrip (v : Local27) :
    pants3ToLocal27 (local27ToPants3 v) = v := by
  rcases v with ⟨⟨a, b⟩, c⟩
  simp [pants3ToLocal27, local27ToPants3]

theorem local27_pants3_roundtrip (p : PantsPath 3) :
    local27ToPants3 (pants3ToLocal27 p) = p := by
  funext i
  fin_cases i <;> simp [local27ToPants3, pants3ToLocal27]

theorem bulk196830 :
    3^11 + 3^9 = 196830 := by
  norm_num

theorem monster196883 :
    3^11 + 3^9 + 53 = 196883 := by
  norm_num

theorem moonshine196884 :
    3^11 + 3^9 + 54 = 196884 := by
  norm_num

theorem secondary54 :
    6 * 9 = 54 ∧ 53 + 1 = 54 := by
  norm_num

structure Frontier where
  localObserverExact : Bool
  localSectionExact : Bool
  chosenConsumerFactors : Bool
  hiddenFineConsumerNonDescent : Bool
  pullbackCollisionInhabited : Bool
  finitePantsRechartsExact : Bool
  standardPresheafVocabularyExposed : Bool
  literalAnalyticGrothendieckSiteConstructed : Bool
  literalMonsterModuleIntertwinerConstructed : Bool

def frontier : Frontier where
  localObserverExact := true
  localSectionExact := true
  chosenConsumerFactors := true
  hiddenFineConsumerNonDescent := true
  pullbackCollisionInhabited := true
  finitePantsRechartsExact := true
  standardPresheafVocabularyExposed := true
  literalAnalyticGrothendieckSiteConstructed := false
  literalMonsterModuleIntertwinerConstructed := false

end Integration.JInvariantSheafDescent
