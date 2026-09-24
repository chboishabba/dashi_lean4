import Mathlib

/-!
# Lean mirror of `CRTPeriod.agda` (genuine, fully proved)

Faithful transcription of `CRTPeriod.agda`.  The "digit" function
`d N = ((N % 71) + (N % 59) + (N % 47)) % 10` is periodic with period
`196883 = 71 · 59 · 47` by elementary CRT/modular arithmetic.  The Agda module
proves this with stdlib `DivMod` lemmas; here we prove the same statement using
`Nat.add_mul_mod_self_right`.
-/

namespace AgdaMirror.CRTPeriod

/-- The repo-defined digit function. -/
def dig (N : Nat) : Nat := ((N % 71) + (N % 59) + (N % 47)) % 10

/-- The period `71 · 59 · 47 = 196883`. -/
def period : Nat := 71 * 59 * 47

theorem period_eq : period = 196883 := rfl

/-- `d (N + k·period) = d N` for all `N, k`. -/
theorem period_thm (N k : Nat) : dig (N + k * period) = dig N := by
  unfold dig period
  have h71 : (N + k * (71 * 59 * 47)) % 71 = N % 71 := by
    have : k * (71 * 59 * 47) = (k * (59 * 47)) * 71 := by ring
    rw [this, Nat.add_mul_mod_self_right]
  have h59 : (N + k * (71 * 59 * 47)) % 59 = N % 59 := by
    have : k * (71 * 59 * 47) = (k * (71 * 47)) * 59 := by ring
    rw [this, Nat.add_mul_mod_self_right]
  have h47 : (N + k * (71 * 59 * 47)) % 47 = N % 47 := by
    have : k * (71 * 59 * 47) = (k * (71 * 59)) * 47 := by ring
    rw [this, Nat.add_mul_mod_self_right]
  rw [h71, h59, h47]

end AgdaMirror.CRTPeriod
