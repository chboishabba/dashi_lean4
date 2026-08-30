import Mathlib

/-!
# GradedClock — Bott (mod 8) and Leech (mod 24) graded residues

A "graded clock" is a cyclic residue counter.  Two clocks recur throughout the
Moonshine atlas:

* the **Bott clock** of period `8` — real Bott periodicity `KO^{n+8} ≃ KO^n`;
* the **Leech clock** of period `24` — the dimension of the Leech lattice and
  the weight of the modular discriminant `Δ`.

Because `24 = 3 · 8`, the Leech clock refines the Bott clock: a residue that
survives the Bott fold (mod 8) and lands in the same class mod 24 is said to be
*clock-coherent*.  The Monster irrep dimension `196883` is clock-coherent with
residue `3` on both clocks.

This module records the elementary arithmetic of the two clocks so downstream
modules (e.g. `RequestProject.CRTTorus`) can refer to the graded residues.
-/

namespace GradedClock

/-- The Bott period. -/
def bottPeriod : Nat := 8

/-- The Leech period. -/
def leechPeriod : Nat := 24

/-- The Bott residue (grade mod 8) of a natural number. -/
def bottGrade (n : Nat) : Nat := n % bottPeriod

/-- The Leech residue (grade mod 24) of a natural number. -/
def leechGrade (n : Nat) : Nat := n % leechPeriod

/-- The Leech clock refines the Bott clock: `24 = 3 · 8`. -/
theorem leech_refines_bott : leechPeriod = 3 * bottPeriod := by decide

/-- A Bott grade is always in `[0, 8)`. -/
theorem bottGrade_lt (n : Nat) : bottGrade n < 8 := by
  unfold bottGrade bottPeriod; omega

/-- A Leech grade is always in `[0, 24)`. -/
theorem leechGrade_lt (n : Nat) : leechGrade n < 24 := by
  unfold leechGrade leechPeriod; omega

/-- The Leech grade reduces to the Bott grade modulo `8` (clock coherence). -/
theorem leech_reduces_to_bott (n : Nat) : leechGrade n % 8 = bottGrade n := by
  unfold leechGrade bottGrade leechPeriod bottPeriod
  omega

/-- The Monster irrep dimension `196883` has Bott grade `3`. -/
theorem monster_bottGrade : bottGrade 196883 = 3 := by decide

/-- The Monster irrep dimension `196883` has Leech grade `11` (since
    `196883 = 8203·24 + 11`).  Note its Bott grade is `11 % 8 = 3`. -/
theorem monster_leechGrade : leechGrade 196883 = 11 := by decide

/-- Clock coherence for the Monster dimension: the Leech grade `11` reduces to
    the Bott grade `3` modulo `8`. -/
theorem monster_clock_coherent : leechGrade 196883 % 8 = bottGrade 196883 :=
  leech_reduces_to_bott 196883

end GradedClock
