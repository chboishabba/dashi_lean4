import Integration.Address
import Mathlib.Tactic

/-!
# Cantor ends as a literal projective limit of DASHI finite frontiers

REUSE the existing `Integration.Address.Addr n Bool` for every finite
binary boundary carrier, rather than creating a competing tree type.

The actual projective limit consists of a choice of stage-n address for
EVERY n, satisfying restriction/forget-the-last-digit compatibility.
This module constructs a TWO-SIDED EQUIVALENCE of this compatible
tower and the full Cantor binary sequence carrier (ℕ → Bool).

This closes the *symbolic inverse-limit* obstruction left by finite
counting alone. It does not produce the infinite 2-manifold, or prove
that its genuine Freudenthal/Richards topological end space is
homeomorphic to this inverse limit. Those topological same-object
proof obligations remain separate.

Source mathematics: classical inverse limits / Cantor space;
Ian Richards (1963) for actual classified surface end spaces.
DASHI attribution: reusable typed finite prefix bridge only.
-/

namespace Synthesis.ExoticTopology

abbrev CantorStage (n : ℕ) := Integration.Address.Addr n Bool

/-- Stage restriction: discard only the final boundary digit. -/
def forgetLast (n : ℕ) (s : CantorStage (n + 1)) : CantorStage n :=
  fun i => s i.castSucc

/-- Fully coherent tower of exact finite frontier addresses. -/
structure CompatibleCantorTower where
  stage : (n : ℕ) → CantorStage n
  compatible : ∀ n (i : Fin n),
    stage (n + 1) i.castSucc = stage n i

/-- The full binary stream representing an ideal Cantor address. -/
abbrev BinaryEndStream := ℕ → Bool

/-- A binary stream gives one prefix at every finite stage. -/
def streamToTower (s : BinaryEndStream) : CompatibleCantorTower where
  stage n := fun i => s i.val
  compatible := by intros; rfl

/-- A coherent stage tower determines each digit from its first
    appearance, at position k of stage k+1. -/
def towerToStream (t : CompatibleCantorTower) : BinaryEndStream :=
  fun k => t.stage (k + 1) (Fin.last k)

theorem streamTowerRoundTrip (s : BinaryEndStream) :
    towerToStream (streamToTower s) = s := by
  funext k
  rfl

private theorem stage_agrees_with_stream (t : CompatibleCantorTower) :
    ∀ n (i : Fin n), t.stage n i = towerToStream t i.val := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · exact (t.compatible n j).trans (ih j)

/-- Exact finite-stage equality is enough to identify all coherent
    towers; compatibility proofs themselves are proof-irrelevant. -/
private theorem tower_ext_of_stage
    (a b : CompatibleCantorTower)
    (h : a.stage = b.stage) : a = b := by
  cases a with
  | mk aStage aCompatible =>
    cases b with
    | mk bStage bCompatible =>
      cases h
      rfl

theorem towerStreamRoundTrip (t : CompatibleCantorTower) :
    streamToTower (towerToStream t) = t := by
  apply tower_ext_of_stage
  funext n i
  exact (stage_agrees_with_stream t n i).symm

/-- The exact full (not merely finite-stage) inverse-limit equivalence. -/
def cantorEndInverseLimitEquiv :
    CompatibleCantorTower ≃ BinaryEndStream where
  toFun := towerToStream
  invFun := streamToTower
  left_inv := towerStreamRoundTrip
  right_inv := streamTowerRoundTrip

/-- Direct compatibility check for an arbitrary reconstructed stream. -/
theorem allPrefixesRestrict (s : BinaryEndStream) (n : ℕ) :
    forgetLast n ((streamToTower s).stage (n + 1)) =
      (streamToTower s).stage n := by
  funext i
  rfl

end Synthesis.ExoticTopology
