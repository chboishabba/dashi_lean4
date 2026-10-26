import Mathlib

/-!
# Source-owned conformal embedding SU(2)_4 subset SU(3)_1

PRIOR PUBLICATION: J. Lacki & Ph. Zaugg, Physics Letters B 228
(1989) 223-227, DOI 10.1016/0370-2693(89)90662-X;
Cappelli--Itzykson--Zuber (1987) ADE modular invariant.

REPO OWNERS: Agda SU2Level4Spin1RepReceipt,
SU3FromAnyon3FoldReceipt, BulkBoundarySU3Receipt,
LevelRankDualityReceipt; Lean #84 WittenCSWZWMonsterChiralCut.
This is a source-written finite branching/fusion calculation only;
no affine VOA, local Q-system, 3D CS Hilbert space, 27-site graph
or physical SU(3)_colour action is constructed.
-/

namespace DASHIWittenD4Embedding

/-- Restriction of three SU(3)_1 integrable modules (vacuum, 3, 3bar)
onto the five SU(2)_4 doubled-spin modules (0,1,2,3,4).
The two distinct SU(3)_1 nonvacuum modules BOTH restrict to
the same SU(2)_4 sector 2. -/
def branching (a : Fin 3) (b : Fin 5) : ℕ :=
  if (a.val = 0 ∧ (b.val = 0 ∨ b.val = 4)) ∨
     (a.val ≠ 0 ∧ b.val = 2)
  then 1 else 0

/-- The nondiagonal SU(2)_4 D4 coupling is BᵀB. -/
def d4Coupling (a b : Fin 5) : ℕ :=
  ∑ x : Fin 3, branching x a * branching x b

theorem d4VacuumAndSimpleCurrent :
    d4Coupling 0 0 = 1 ∧
    d4Coupling 0 4 = 1 ∧
    d4Coupling 4 0 = 1 ∧
    d4Coupling 4 4 = 1 := by
  decide

/-- The fixed point SU(2)_4 doubled-spin 2 resolves into the
two distinct SU(3)_1 fundamental/antifundamental sectors. -/
theorem d4FixedPointSplits :
    d4Coupling 2 2 = 2 ∧
    branching 1 2 = 1 ∧
    branching 2 2 = 1 ∧
    branching 0 2 = 0 := by
  decide

theorem d4OtherEntriesZero :
    ∀ a b : Fin 5,
      (a.val = 1 ∨ a.val = 3 ∨ b.val = 1 ∨ b.val = 3) →
      d4Coupling a b = 0 := by
  decide

/-- In the extended SU(3)_1 modular category the three
simple-current charges fuse according to the group Z/3. -/
def extendedFusion (a b c : Fin 3) : ℕ :=
  if (a.val + b.val) % 3 = c.val then 1 else 0

theorem extendedFusionZ3 :
    ∀ a b c : Fin 3,
      extendedFusion a b c =
        if (a.val + b.val) % 3 = c.val then 1 else 0 := by
  intro a b c
  rfl

theorem extendedFusionAssociative :
    ∀ a b c d : Fin 3,
      (∑ x : Fin 3, extendedFusion a b x * extendedFusion x c d) =
        (∑ x : Fin 3, extendedFusion b c x * extendedFusion a x d) := by
  decide

theorem extendedChargeOneFusion :
    extendedFusion 1 1 2 = 1 ∧
    extendedFusion 1 2 0 = 1 ∧
    extendedFusion 2 2 1 = 1 := by
  decide

/-- This is the conformal embedding at k=4, NOT the already-recorded
candidate SU(2)_3 <-> SU(3)_1 "level-rank" identification.
Indeed strict SU(2)_3 central charge is 9/5, not 2. -/
theorem matchingChiralCentralCharge :
    (3 * (4 : ℚ) / (4 + 2)) = (8 * (1 : ℚ) / (1 + 3)) := by
  norm_num

theorem differentFromSU2LevelThree :
    (3 * (3 : ℚ) / (3 + 2)) ≠ (8 * (1 : ℚ) / (1 + 3)) := by
  norm_num

/-- A 27-charge cyclic label can project to a mod-3 charge, but
the reduction is not injective. Hence it cannot identify the
27 distinct Monster charge eigenspaces with these three sectors. -/
def chargeReduction (x : Fin 27) : Fin 3 :=
  ⟨x.val % 3, Nat.mod_lt _ (by omega)⟩

theorem chargeReductionNotInjective :
    chargeReduction 0 = chargeReduction 3 := by decide

end DASHIWittenD4Embedding
