import AgdaMirror.DASHIAlgebra

/-!
# Lean mirror of `DASHI/Algebra/Trit/HalfTrit.agda` (genuine, fully proved)

Faithful transcription of the five-position *half-trit* carrier refining the
balanced-ternary `Trit`:

* the five signed half-step coordinates `HalfTrit`;
* the sign-flip `invHalfTrit` and its involution law `invHalfTrit_invol`;
* the forgetful embedding `embedTrit : HalfTrit → Trit`, which is *necessarily
  non-injective* — the two collapses (`negOne`/`negHalf` and `posHalf`/`posOne`)
  are genuine facts and are recorded as proved equalities, while the failure of
  injectivity is recorded as a genuine inequality of distinct preimages.

All proofs are by case analysis; no `sorry`, axiom-clean.
-/

namespace AgdaMirror.HalfTritMod

open AgdaMirror.DASHIAlgebra (Trit)

/-- Five signed half-step coordinates. -/
inductive HalfTrit
  | negOne | negHalf | zero | posHalf | posOne
  deriving DecidableEq, Repr

/-- Forgetful embedding into the balanced-ternary digit. -/
def embedTrit : HalfTrit → Trit
  | .negOne  => .neg
  | .negHalf => .neg
  | .zero    => .zer
  | .posHalf => .pos
  | .posOne  => .pos

/-- Sign flip on half-trits. -/
def invHalfTrit : HalfTrit → HalfTrit
  | .negOne  => .posOne
  | .negHalf => .posHalf
  | .zero    => .zero
  | .posHalf => .negHalf
  | .posOne  => .negOne

/-- The sign flip is an involution. -/
theorem invHalfTrit_invol (x : HalfTrit) : invHalfTrit (invHalfTrit x) = x := by
  cases x <;> rfl

/-- The embedding collapses `negOne` and `negHalf`. -/
theorem embedTrit_negOne_collapses :
    embedTrit .negOne = embedTrit .negHalf := rfl

/-- The embedding collapses `posHalf` and `posOne`. -/
theorem embedTrit_posHalf_collapses :
    embedTrit .posHalf = embedTrit .posOne := rfl

/-- The embedding is genuinely non-injective: distinct half-trits with equal
images exist. -/
theorem embedTrit_not_injective :
    ¬ Function.Injective embedTrit := by
  intro h
  have : (HalfTrit.negOne) = HalfTrit.negHalf := h embedTrit_negOne_collapses
  exact absurd this (by decide)

/-- The sign flip commutes with the embedding (`embedTrit` of a flip is the
balanced-ternary negation of the embedding). -/
theorem embedTrit_invHalfTrit (x : HalfTrit) :
    embedTrit (invHalfTrit x) = Trit.inv (embedTrit x) := by
  cases x <;> rfl

end AgdaMirror.HalfTritMod
