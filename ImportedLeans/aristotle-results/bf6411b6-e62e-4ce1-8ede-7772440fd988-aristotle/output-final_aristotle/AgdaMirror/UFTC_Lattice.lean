import Mathlib

/-!
# Lean mirror of `UFTC_Lattice.agda` (genuine, fully proved)

Faithful transcription of `UFTC_Lattice.agda`: severity levels form a
join-semilattice under `max` ("max severity wins"), with idempotence,
commutativity, associativity, and monotonicity of the join, plus a minimal
`Code` model whose XOR propagation rule is monotone in severity.
-/

namespace AgdaMirror.UFTC

/-- Severity levels (`0..9` in intent; here any `Nat`). -/
abbrev Severity := Nat

/-- Join = max severity wins. -/
def joinSev (a b : Severity) : Severity := max a b

theorem joinSev_idem (a : Severity) : joinSev a a = a := max_self a
theorem joinSev_comm (a b : Severity) : joinSev a b = joinSev b a := max_comm a b
theorem joinSev_assoc (a b c : Severity) :
    joinSev (joinSev a b) c = joinSev a (joinSev b c) := max_assoc a b c

theorem joinSev_monoL {a a' b : Severity} (h : a ≤ a') : joinSev a b ≤ joinSev a' b := by
  unfold joinSev; exact max_le_max h le_rfl
theorem joinSev_monoR {a b b' : Severity} (h : b ≤ b') : joinSev a b ≤ joinSev a b' := by
  unfold joinSev; exact max_le_max le_rfl h

/-- A minimal "code" model: normal trit, or a special failure code with severity. -/
inductive Code where
  | normal : Nat → Code
  | special : Severity → Code

def severity : Code → Severity
  | .normal _ => 0
  | .special s => s

/-- Propagation rule: combine codes by max severity. -/
def cXor (x y : Code) : Code := .special (joinSev (severity x) (severity y))

/-- Rotation: does not reduce severity. -/
def cRot (x : Code) : Code := x

/-- `cXor` is monotone in severity (max severity cannot be masked). -/
theorem cXor_monotone (x x' y y' : Code)
    (hx : severity x ≤ severity x') (hy : severity y ≤ severity y') :
    severity (cXor x y) ≤ severity (cXor x' y') := by
  simpa [cXor, severity, joinSev] using max_le_max hx hy

theorem cRot_monotone (x x' : Code) (hx : severity x ≤ severity x') :
    severity (cRot x) ≤ severity (cRot x') := hx

end AgdaMirror.UFTC
