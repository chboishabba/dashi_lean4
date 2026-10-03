/-!
DASHI-original query-relative ternary hypervoxel depth mathematics.
McNamara, "A System of Wrong" Episode 4: nine cells are (violated, imposed).
Higher coordinates, collision proofs, and witness carriers below are DASHI.
Crenshaw 1991 DOI 10.2307/1229039 motivates distinct intersectional
positions; Kimmerer, Two-Eyed Seeing, and custodianship require separately
sourced knowledge/authority; none supplies these mathematics. Lacan/Irigaray
and Marxist/materialist lenses are not collapsed into legal sources.

Cartesian growth 3^n, block composition 27^3, and genuine
function-space tetration 3^27 are different constructions.
-/
import AgdaMirror.Law.WrongTypeGrid

namespace AgdaMirror.Law.WrongTypeGrid.RelationalDepth

abbrev Hypervoxel (n : Nat) := Fin n → Mode

def productSize (n : Nat) : Nat := 3 ^ n

theorem sizeXY : productSize 2 = 9 := by decide
theorem sizeXYZ : productSize 3 = 27 := by decide
theorem sizeXYZA : productSize 4 = 81 := by decide
theorem threeBlocks27 : 27 ^ 3 = 19683 := by decide

def FitsThrough {S V O : Type} (view : S → V) (query : S → O) : Prop :=
  ∃ f : V → O, ∀ s, query s = f (view s)

/-- Dropping an axis produces a collision between two otherwise
    identical configurations with different answers to its value. -/
def dropHead {n : Nat} (s : Hypervoxel (n+1)) : Hypervoxel n :=
  fun i => s i.succ

def askHead {n : Nat} (s : Hypervoxel (n+1)) : Mode := s ⟨0, Nat.zero_lt_succ n⟩

def allCare {n : Nat} : Hypervoxel n := fun _ => .care

def withHead {n : Nat} (m : Mode) : Hypervoxel (n+1) :=
  fun i => if i.val = 0 then m else .care

theorem dropHead_same {n : Nat} :
    dropHead (withHead (n := n) .care) =
      dropHead (withHead (n := n) .power) := by
  funext i
  simp [dropHead, withHead]

theorem head_diff {n : Nat} :
    askHead (withHead (n := n) .care) ≠
      askHead (withHead (n := n) .power) := by
  decide

theorem head_not_factors_through_tail (n : Nat) :
    ¬ FitsThrough (dropHead (n := n)) (askHead (n := n)) := by
  intro h
  obtain ⟨f, hf⟩ := h
  have l := hf (withHead (n := n) .care)
  have r := hf (withHead (n := n) .power)
  have e : (Mode.care : Mode) = Mode.power := by
    calc
      Mode.care = f (dropHead (withHead (n := n) .care)) := by simpa [askHead, withHead] using l
      _ = f (dropHead (withHead (n := n) .power)) := by rw [dropHead_same]
      _ = Mode.power := by simpa [askHead, withHead] using r.symm
  cases e

theorem no_tail_rechart_recovers_head (n : Nat) {View : Type}
    (chart : Hypervoxel n → View) :
    ¬ FitsThrough (fun s => chart (dropHead s))
        (askHead (n := n)) := by
  intro h
  obtain ⟨f, hf⟩ := h
  apply head_not_factors_through_tail n
  exact ⟨fun x => f (chart x), hf⟩

-- A four-axis consumer which needs all four values admits no
-- single-coordinate deletion. This establishes width=4 only relative
-- to this chosen family of coordinate projections.
abbrev Quad := Mode × Mode × Mode × Mode
abbrev Triple := Mode × Mode × Mode

inductive ThreeView
  | omitX | omitY | omitZ | omitA

def observeThree : ThreeView → Quad → Triple
  | .omitX, (_, y, z, a) => (y,z,a)
  | .omitY, (x, _, z, a) => (x,z,a)
  | .omitZ, (x, y, _, a) => (x,y,a)
  | .omitA, (x, y, z, _) => (x,y,z)

def allCareQuad : Quad := (.care,.care,.care,.care)
def alter : ThreeView → Quad
  | .omitX => (.power,.care,.care,.care)
  | .omitY => (.care,.power,.care,.care)
  | .omitZ => (.care,.care,.power,.care)
  | .omitA => (.care,.care,.care,.power)

theorem observe_same (v : ThreeView) :
    observeThree v allCareQuad = observeThree v (alter v) := by
  cases v <;> rfl

theorem quad_different (v : ThreeView) : allCareQuad ≠ alter v := by
  cases v <;> decide

theorem no_three_view_factors_identity (v : ThreeView) :
    ¬ FitsThrough (observeThree v) (fun q : Quad => q) := by
  intro h
  obtain ⟨f, hf⟩ := h
  apply quad_different v
  calc
    allCareQuad = f (observeThree v allCareQuad) := hf _
    _ = f (observeThree v (alter v)) := by rw [observe_same]
    _ = alter v := (hf _).symm

theorem all_four_factors_identity :
    FitsThrough (fun q : Quad => q) (fun q => q) := by
  exact ⟨id, by intro q; rfl⟩

/-- Evidence-carrying situated fibre: no term of this type is a legal finding. -/
structure RelationalFibre (n : Nat) where
  address : Hypervoxel n
  actorAndInterestReference : String
  legalSystemAndPeriodReference : String
  sourceRevisionReference : String
  custodialAuthorityReference : String
  interpretationReference : String
  evidenceReference : String

/-- Compatibility is a required producer, not automatic evidence of gluing. -/
structure CompatibleGluing {n m : Nat}
    (left : RelationalFibre n) (right : RelationalFibre m) where
  sharedInterface : String
  identityAndTimeEvidence : Prop
  normativeComparisonEvidence : Prop
  sharedInterfaceEvidence : Prop

end AgdaMirror.Law.WrongTypeGrid.RelationalDepth
