import Integration.E6Mod3WeylAction
import Integration.Griess1990Moufang81Determinant
import Integration.E6F3ExteriorSquare
import Mathlib

/-!
# ORIGINAL 243/240 five-trit cut ↔ source M81 CARRIER; action firewall

Source-history: the literal T5 243 and diagonal-deleted 240 come from
the older DASHI trialectic kernel (Lean #43, Agda #1094).
The 240≠E8/action obstruction already lives in Lean #47:
T5RelativeE6ActionRestrictionObstruction.
The order-81 commutative nonassociative Moufang product is original
Robert L. Griess Jr., J. Algebra 131 (1990), 281-293
(DOI:10.1016/0021-8693(90)90176-O).

This module gives the strongest honest join: a *literal reversible*
five-coordinate chart from the OLD standardized T5 to the UNDERLYING
81-element Griess loop carrier × F3, with old diagonal mapped to
{loop identity}×F3. This is not a loop/group isomorphism, a
normalizer-equivariant map, or an E8 root recognition.

The SAME 243 source T5 carries a distinct E6 quadratic form whose
strata are 1+80+90+72. Removing the old diagonal yields
80+90+70, not E8's correctly structured 72+6+6×27.

All native_decide theorems SOURCE-WRITTEN, NOT kernel checked here.
-/

namespace Integration.Griess1990OriginalT5Moufang243240Chart

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.Griess1990Moufang81Determinant

/-- The original F3^5 coordinates, not a newly invented 243 carrier. -/
abbrev Five := F3Five

/-- The existing PR #43 literal constant-diagonal cut translated into the
same standardized F3^5 coordinates; the PR #47 obstruction module is not
present on this branch. This predicate matches its OldDiagonal definition. -/
def OldDiagonal (z : Five) : Prop :=
  z.z0 = z.z1 ∧ z.z1 = z.z2 ∧ z.z2 = z.z3 ∧ z.z3 = z.z4

instance (z : Five) : Decidable (OldDiagonal z) := inferInstance

/-- Original 240, the selected 3-point diagonal excluded. -/
def OldRelativeT5 := {z : Five // ¬ OldDiagonal z}
instance : Fintype OldRelativeT5 := inferInstance

theorem old_relative_t5_card : Fintype.card OldRelativeT5 = 240 := by
  native_decide

/-- The source M81 *set*: original grade coordinates plus central
phase. The extra F3 parameter belongs to the original fifth-trit
difference chart and does NOT identify itself as a second center. -/
def fiveToM81 (z : Five) : Loop81 × ZMod 3 :=
  (⟨![z.z0-z.z4, z.z1-z.z4, z.z2-z.z4], z.z3-z.z4⟩, z.z4)

/-- Literal inverse of the original diagonal-centering map. -/
def m81ToFive (p : Loop81 × ZMod 3) : Five :=
  ⟨p.1.grade 0 + p.2, p.1.grade 1 + p.2,
   p.1.grade 2 + p.2, p.1.central + p.2, p.2⟩

theorem five_chart_left_roundtrip :
    ∀ z : Five, m81ToFive (fiveToM81 z) = z := by native_decide

theorem five_chart_right_roundtrip :
    ∀ p : Loop81 × ZMod 3, fiveToM81 (m81ToFive p) = p := by native_decide

def fiveM81CarrierEquiv : Five ≃ Loop81 × ZMod 3 where
  toFun := fiveToM81
  invFun := m81ToFive
  left_inv := five_chart_left_roundtrip
  right_inv := five_chart_right_roundtrip

theorem five_card243 : Fintype.card Five = 243 := by native_decide

theorem original_diagonal_iff_selected_m81_identity :
    ∀ z : Five, OldDiagonal z ↔ (fiveToM81 z).1 = identity := by native_decide

/-- Actual old diagonal-deleted carrier imported from existing Lean #47. -/
abbrev Old240 := OldRelativeT5

/-- Griess's literal 81-element loop with only its unique UNIT removed;
do not confuse this with the unrelated 80-point E6 nonzero null shell. -/
def PuncturedM81 := {m : Loop81 // m ≠ identity}

instance : Fintype PuncturedM81 := inferInstance

theorem loop81_cardinality : Fintype.card Loop81 = 81 := by native_decide

theorem punctured_loop80 : Fintype.card PuncturedM81 = 80 := by native_decide

def old240ToPuncturedLoop (z : Old240) :
    PuncturedM81 × ZMod 3 :=
  (⟨(fiveToM81 z.1).1, by
    have h : ∀ y : Five, ¬ OldDiagonal y →
      (fiveToM81 y).1 ≠ identity := by native_decide
    exact h z.1 z.2⟩, (fiveToM81 z.1).2)

/-- This provides the actual two-sided, selected-chart set bridge;
it does NOT carry the Moufang product to T5 coordinatewise addition. -/
theorem old240_to_punctured_loop_bijective :
    Function.Bijective old240ToPuncturedLoop := by native_decide

def old240EquivPuncturedM81TimesF3 :
    Old240 ≃ PuncturedM81 × ZMod 3 :=
  Equiv.ofBijective old240ToPuncturedLoop
    old240_to_punctured_loop_bijective

theorem actual_original_240_card :
    Fintype.card Old240 = 240 := old_relative_t5_card

/-- Counts FROM ACTUAL SOURCE M81 GRADE, not E6 quadratic shells. -/
def noncentralGrade (z : Old240) : Prop :=
  (fiveToM81 z.1).1.grade ≠ 0

instance (z : Old240) : Decidable (noncentralGrade z) := inferInstance

theorem original240_noncentral_grade_234 :
    (Finset.univ.filter fun z : Old240 => noncentralGrade z).card = 234 := by
  native_decide

theorem original240_zero_grade_nonidentity_6 :
    (Finset.univ.filter fun z : Old240 => ¬ noncentralGrade z).card = 6 := by
  native_decide

/-- The competing E6 root recognition consumes *this exact* Q=2
stratum on the SAME standardized five-trit carrier. -/
def old240QuadraticCount (q : ZMod 3) : Nat :=
  (Finset.univ.filter fun z : Five =>
    ¬ OldDiagonal z ∧ standardQuadratic z = q).card

theorem original240_qzero_80 : old240QuadraticCount 0 = 80 := by native_decide
theorem original240_qone_90 : old240QuadraticCount 1 = 90 := by native_decide
theorem original240_qtwo_70 : old240QuadraticCount 2 = 70 := by native_decide

/-- The deleted diagonal includes the zero vector and two Q=2 vectors.
In particular it removes TWO elements of the originally recognized E6
root shell: a concrete reason the E6 inherited action cannot restrict. -/
theorem old_deleted_diagonal_qprofile :
    (Finset.univ.filter fun z : Five =>
      OldDiagonal z ∧ standardQuadratic z = 0).card = 1 ∧
    (Finset.univ.filter fun z : Five =>
      OldDiagonal z ∧ standardQuadratic z = 1).card = 0 ∧
    (Finset.univ.filter fun z : Five =>
      OldDiagonal z ∧ standardQuadratic z = 2).card = 2 := by
  native_decide

/-- Source-identical explicit witness from PR #47: E6 simple s3
takes the non-diagonal vector (2,2,1,1,1) to a deleted diagonal
vector. This uses the ACTUAL original E6 action, not a fake action
on a 240-point cardinality proxy. -/
def e6EscapedDiagonal : Five := ⟨2,2,1,1,1⟩

theorem e6_escaped_is_in_old240 : ¬ OldDiagonal e6EscapedDiagonal := by
  native_decide

theorem e6_s3_returns_to_old_diagonal :
    OldDiagonal (reflectStandard .s3 e6EscapedDiagonal) := by
  native_decide

theorem original240_inherited_E6_action_blocked :
    ¬ (∀ s (z : Old240), ¬ OldDiagonal (reflectStandard s z.1)) := by
  intro h
  exact (h .s3 ⟨e6EscapedDiagonal, e6_escaped_is_in_old240⟩)
    e6_s3_returns_to_old_diagonal

end Integration.Griess1990OriginalT5Moufang243240Chart
