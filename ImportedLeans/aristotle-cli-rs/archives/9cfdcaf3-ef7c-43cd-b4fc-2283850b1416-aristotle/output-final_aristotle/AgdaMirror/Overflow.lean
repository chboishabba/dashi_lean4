import Mathlib

/-!
# Lean mirror of `Overflow.agda` (genuine, fully proved)

Faithful transcription of `Overflow.agda`: a custom strict order `Prec` (`≺`) on
`ℕ`, voxel states with proof-carrying threshold guards (`VoxelGuard`), a total
comparison `compare`, the soundness lemmas relating `compare` tokens to `Prec`,
the deterministic `enforce` classifier, and its correctness
(`enforce_ascended_if`, `only_if`).  All genuine, fully proved by structural
recursion exactly as in the Agda original.
-/

namespace AgdaMirror.Overflow

/-- Custom strict order on `ℕ` (the Agda `_≺_`). -/
inductive Prec : Nat → Nat → Prop where
  | zs : ∀ {n}, Prec 0 (n + 1)
  | ss : ∀ {m n}, Prec m n → Prec (m + 1) (n + 1)

inductive Voxel | grounded | plateau | ascended
  deriving DecidableEq

/-- Threshold guard carrying the witness justifying its classification. -/
inductive VoxelGuard (threshold value : Nat) : Type where
  | stay : Prec value threshold → VoxelGuard threshold value
  | pivot : threshold = value → VoxelGuard threshold value
  | ascend : Prec threshold value → VoxelGuard threshold value

def state {t v : Nat} : VoxelGuard t v → Voxel
  | .stay _ => .grounded
  | .pivot _ => .plateau
  | .ascend _ => .ascended

inductive Order | below | equal | above

def compare : Nat → Nat → Order
  | 0, 0 => .equal
  | 0, _ + 1 => .below
  | _ + 1, 0 => .above
  | a + 1, b + 1 => compare a b

theorem compare_below_prec : ∀ {t v}, compare t v = .below → Prec t v
  | 0, _ + 1, _ => .zs
  | t + 1, v + 1, h => .ss (compare_below_prec (t := t) (v := v) h)

theorem compare_above_prec : ∀ {t v}, compare t v = .above → Prec v t
  | 0, 0, h => by simp [compare] at h
  | 0, _ + 1, h => by simp [compare] at h
  | _ + 1, 0, _ => .zs
  | t + 1, v + 1, h => .ss (compare_above_prec (t := t) (v := v) h)

theorem compare_equal_eq : ∀ {t v}, compare t v = .equal → t = v
  | 0, 0, _ => rfl
  | t + 1, v + 1, h => congrArg (· + 1) (compare_equal_eq (t := t) (v := v) h)

theorem compare_prec_below : ∀ {t v}, Prec t v → compare t v = .below
  | _, _, .zs => rfl
  | _, _, .ss p => by simpa [compare] using compare_prec_below p

/-- Deterministic guard chosen by structural comparison. -/
def enforce : (threshold value : Nat) → VoxelGuard threshold value
  | 0, 0 => .pivot rfl
  | 0, _ + 1 => .ascend .zs
  | _ + 1, 0 => .stay .zs
  | t + 1, v + 1 =>
    match enforce t v with
    | .stay p => .stay (.ss p)
    | .pivot p => .pivot (congrArg (· + 1) p)
    | .ascend p => .ascend (.ss p)

theorem enforce_ascended_if : ∀ {t v} (p : Prec t v), enforce t v = .ascend p
  | 0, _ + 1, .zs => rfl
  | t + 1, v + 1, .ss p => by
    simp only [enforce, enforce_ascended_if (t := t) (v := v) p]

/-- Correctness: an `ascended` classification really witnesses `threshold ≺ value`. -/
theorem only_if {t v : Nat} (h : state (enforce t v) = .ascended) : Prec t v := by
  cases hv : enforce t v with
  | stay p => rw [hv] at h; exact absurd h (by simp [state])
  | pivot p => rw [hv] at h; exact absurd h (by simp [state])
  | ascend p => exact p

end AgdaMirror.Overflow
