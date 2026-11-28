import Mathlib
import Welds.PNPResidualGeometryBridgeExact
import Welds.PNPF3SyndromeBoundaryExact
import Welds.PNPHyperfabricActualEpochPackingExact
import Welds.PNPStackFiveLaneTransferExact
import Welds.PNPActualInstructionLedgerExact

namespace PNPSignedOrbitBoundary

-- Classical diagonal gauge, with the original noncommutative order.
def relativeGauge (G : Type*) [Group G] : G × G ≃ G × G where
  toFun p := (p.2⁻¹ * p.1,p.2)
  invFun p := (p.2 * p.1,p.2)
  left_inv p := by simp [mul_assoc]
  right_inv p := by simp [mul_assoc]

theorem diagonal_relative {G : Type*} [Group G] (g x y : G) :
    (relativeGauge G (g*x,g*y)).1 = (relativeGauge G (x,y)).1 := by
  change (g*y)⁻¹*(g*x) = y⁻¹*x
  group

-- Retain the anchor when the consumer is not invariant.
theorem gauge_factor_iff {G Y : Type*} [Group G] (f : G × G → Y) :
    (∃ q : G → Y, ∀ x y, f (x,y) = q (y⁻¹*x)) ↔
    (∀ g x y : G, f (g*x,g*y) = f (x,y)) := by
  constructor
  · rintro ⟨q,h⟩ g x y
    rw [h,h]
    congr 1
    group
  · intro h
    refine ⟨fun r => f (r,1),?_⟩
    intro x y
    have e := h y⁻¹ x y
    simpa using e.symm

-- C1a: an actual action commuting with the boundary projection and
-- preserving original validity gives a bijection between conditional lifts.
def transportFibre {X B : Type*} (valid : X → Prop) (key : X → B)
    (e : X ≃ X) (b c : B)
    (hv : ∀ x, valid (e x) ↔ valid x)
    (hk : ∀ x, key (e x) = c ↔ key x = b) :
    {x : X // valid x ∧ key x = b} ≃ {x : X // valid x ∧ key x = c} where
  toFun x := ⟨e x, (hv x).mpr x.2.1, (hk x).mpr x.2.2⟩
  invFun x := ⟨e.symm x,
    (hv (e.symm x)).mp (by simpa using x.2.1),
    (hk (e.symm x)).mp (by simpa using x.2.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem transportCard {X B : Type*} (valid : X → Prop) (key : X → B)
    (e : X ≃ X) (b c : B)
    (hv : ∀ x, valid (e x) ↔ valid x)
    (hk : ∀ x, key (e x) = c ↔ key x = b)
    [Fintype {x : X // valid x ∧ key x = b}]
    [Fintype {x : X // valid x ∧ key x = c}] :
    Fintype.card {x : X // valid x ∧ key x = b} =
      Fintype.card {x : X // valid x ∧ key x = c} :=
  Fintype.card_congr (transportFibre valid key e b c hv hk)

-- S1: orientation-only changes cannot supply a relevant event receipt.
theorem invariant_not_reachable {G X S Y : Type*} [Group G] [MulAction G X]
    (valid : Set X) (state : X → Nat → S) (f : X → Y)
    (h : ∀ g : G, ∀ x, f (g • x) = f x)
    (g : G) (x : X) (t : Nat) :
    g • x ∉ PNPHyperfabricOwnedEvents.ReachableDivergentSet valid state f x t := by
  intro hy
  exact hy.2.2 (h g x)

end PNPSignedOrbitBoundary

namespace PNPActualTransferCompose
open PNPStackEmittedList

-- Reuse the canonical five-lane run rather than silently substitute an
-- alternative group action or a compressed arithmetic clock.
theorem run_owner (P : List Edge) (n : Nat) (s : State) :
    PNPStackFiveLane.run P n s = PNPActualInstructionLedger.run P n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [PNPStackFiveLane.run,PNPActualInstructionLedger.run]
    cases h : step P s with
    | none => rfl
    | some t => simpa using ih t

-- Maximal transfer + actual selected exit, composing on one emitted list.
-- The selection itself remains to be produced from the actual digit table.
theorem maximal_then_exit (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data) (w : State)
    (hm : mainTag p ∈ inventory Q A) (hh : midTag p ∈ inventory Q A)
    (ht : transfer (max 2 A) table p = some t)
    (exitExact : step (compile Q A table)
      ⟨mainTag p,PNPStackFiveLane.moveData t (v t.x/t.a) v⟩ = some w) :
    PNPActualInstructionLedger.run (compile Q A table) (2*(v t.x/t.a)+1)
      ⟨mainTag p,v⟩ = some w := by
  have h := (PNPStackFiveLane.actualMaximal Q A table p t v hm hh ht).1
  rw [run_owner] at h
  apply PNPActualInstructionLedger.compose_phases _ _ 1 _ _ _ h
  simp [PNPActualInstructionLedger.run,exitExact]

end PNPActualTransferCompose
