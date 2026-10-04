import Mathlib.Tactic
import NSBControl.Rational345R823RealMultiplierDifference
import NSBControl.Rational345Round71ZeroModeUnique

/-!
# Real R572 physical inner fold

The ambient Lean convolution sums over all 729×729 input pairs.  Agda R572 is
stated on the physical nonzero resonant fibre.  For zero-mean states these are
exactly the same operator: all pairs touching k=0 vanish, and nonresonant pairs
already vanish in the literal ordered term.

This file then pairs (p,q) with (q,p), obtaining twice the projected
nonlinearity, and rewrites every active pair to the real four-sign
multiplier-difference vector from the R571/R106 port.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823RealInnerFold

open Rational345RealRadius4
open Rational345Round71ZeroMode
open Rational345R823RealHelicalCore

classical

def physicalPairActive (p q k : Mode) : Prop :=
  nonzeroMode p ∧ nonzeroMode q ∧ Resonates p q k

instance (p q k : Mode) : Decidable (physicalPairActive p q k) := inferInstance

theorem physicalPairActive_swap_iff (p q k : Mode) :
    physicalPairActive q p k ↔ physicalPairActive p q k := by
  constructor
  · rintro ⟨hq, hp, hres⟩
    exact ⟨hp, hq, resonates_swap hres⟩
  · rintro ⟨hp, hq, hres⟩
    exact ⟨hq, hp, resonates_swap hres⟩

def physicalOrderedTerm (u : State) (p q k : Mode) : Vec3 :=
  if physicalPairActive p q k then
    orderedPairVector k p q (u p) (u q)
  else 0

def physicalOrderedFold (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode, physicalOrderedTerm u p q k

def physicalPairedTerm (u : State) (p q k : Mode) : Vec3 :=
  if physicalPairActive p q k then
    pairInteractionVector k p q (u p) (u q)
  else 0

def physicalPairedFold (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode, physicalPairedTerm u p q k

def fourSignInnerTerm (u : State) (p q k : Mode) : Vec3 :=
  if physicalPairActive p q k then fourSignInner u p q k else 0

def fourSignInnerFold (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode, fourSignInnerTerm u p q k

/-- On a zero-mean state, pruning the ambient ordered convolution to nonzero
physical resonant pairs changes nothing. -/
theorem physicalOrderedFold_eq_projectedNonlinearity
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (hzero : u zeroMode = 0) :
    physicalOrderedFold u k = projectedNonlinearity u k := by
  unfold physicalOrderedFold projectedNonlinearity projectedBilinear
  rw [if_neg hk]
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro q hqMem
  by_cases hp0 : isZeroMode p
  · have hup : u p = 0 := value_zero_of_isZero u hzero p hp0
    simp [physicalOrderedTerm, physicalPairActive, hp0,
      orderedPairVector, projectedOrderedBilinear, hup]
  · by_cases hq0 : isZeroMode q
    · have huq : u q = 0 := value_zero_of_isZero u hzero q hq0
      simp [physicalOrderedTerm, physicalPairActive, hp0, hq0,
        orderedPairVector, projectedOrderedBilinear, huq]
    · by_cases hres : Resonates p q k
      · simp [physicalOrderedTerm, physicalPairActive, hp0, hq0, hres,
          orderedPairVector, projectedOrderedBilinear]
      · simp [physicalOrderedTerm, physicalPairActive, hp0, hq0, hres,
          orderedPairVector, projectedOrderedBilinear]

/-- One paired physical cell is the ordered cell plus its p/q partner. -/
theorem physicalPairedTerm_eq_ordered_plus_swap
    (u : State) (p q k : Mode) :
    physicalPairedTerm u p q k =
      physicalOrderedTerm u p q k + physicalOrderedTerm u q p k := by
  by_cases h : physicalPairActive p q k
  · have hs : physicalPairActive q p k :=
      (physicalPairActive_swap_iff p q k).2 h
    simp [physicalPairedTerm, physicalOrderedTerm, h, hs,
      pairInteractionVector]
  · have hs : ¬ physicalPairActive q p k := by
      intro hsq
      exact h ((physicalPairActive_swap_iff p q k).1 hsq)
    simp [physicalPairedTerm, physicalOrderedTerm, h, hs]

/-- Summing the swap partner over the complete finite pair set gives the same
ordered fold. -/
theorem swappedPhysicalOrderedFold_eq
    (u : State) (k : Mode) :
    (∑ p : Mode, ∑ q : Mode, physicalOrderedTerm u q p k) =
      physicalOrderedFold u k := by
  unfold physicalOrderedFold
  simpa using
    (Fintype.sum_comm (fun p q : Mode => physicalOrderedTerm u p q k)).symm

/-- Real counterpart of R310/R572: the complete physical paired inner fold is
twice the literal projected nonlinearity. -/
theorem physicalPairedFold_eq_twiceProjectedNonlinearity
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (hzero : u zeroMode = 0) :
    physicalPairedFold u k =
      projectedNonlinearity u k + projectedNonlinearity u k := by
  calc
    physicalPairedFold u k
        = (∑ p : Mode, ∑ q : Mode, physicalOrderedTerm u p q k) +
          (∑ p : Mode, ∑ q : Mode, physicalOrderedTerm u q p k) := by
            unfold physicalPairedFold
            simp_rw [physicalPairedTerm_eq_ordered_plus_swap]
            simp only [Finset.sum_add_distrib]
    _ = physicalOrderedFold u k + physicalOrderedFold u k := by
          rw [swappedPhysicalOrderedFold_eq]
          rfl
    _ = projectedNonlinearity u k + projectedNonlinearity u k := by
          rw [physicalOrderedFold_eq_projectedNonlinearity u k hk hzero]

/-- On a physical transverse state, every active paired cell is the four-sign
multiplier-difference cell. -/
theorem physicalPairedTerm_eq_fourSignInnerTerm
    (u : State) (p q k : Mode)
    (hk : nonzeroMode k)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    physicalPairedTerm u p q k = fourSignInnerTerm u p q k := by
  by_cases h : physicalPairActive p q k
  · rcases h with ⟨hp, hq, hres⟩
    simp only [physicalPairedTerm, fourSignInnerTerm,
      if_pos ⟨hp, hq, hres⟩]
    calc
      pairInteractionVector k p q (u p) (u q)
          = fourComponentPairInteraction u p q k := by
              simpa [pairedInteraction] using
                pairedInteraction_expands_four_components
                  u p q k hres hp hq (htrans p) (htrans q)
      _ = fourSignInner u p q k :=
            fourComponentPairInteraction_eq_fourSignInner
              u p q k hres hk hp hq (htrans p) (htrans q)
  · simp [physicalPairedTerm, fourSignInnerTerm, h]

/-- Real R572 terminal identity: the physical paired inner fold is literally
the four-sign multiplier-difference fold. -/
theorem physicalPairedFold_eq_fourSignInnerFold
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (_hzero : u zeroMode = 0)
    (htrans : ∀ m : Mode, bilinearDot (kComplex m) (u m) = 0) :
    physicalPairedFold u k = fourSignInnerFold u k := by
  unfold physicalPairedFold fourSignInnerFold
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro q hqMem
  exact physicalPairedTerm_eq_fourSignInnerTerm u p q k hk htrans

/-- Real R572 is now represented on the R830 carrier. -/
def r823RealR572PhysicalInnerFoldClosed : Bool := true

end Rational345R823RealInnerFold
end NSBControl
