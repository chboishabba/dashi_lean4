import AgdaMirror.Base369
import AgdaMirror.DASHIAlgebra

/-!
# Lean mirror of `DASHI/Algebra/TritTriTruthBridge.agda` (genuine, fully proved)

Faithful transcription of the bridge between the balanced-ternary digit type
`Trit` (from `DASHI.Algebra.Trit`, mirrored in `AgdaMirror.DASHIAlgebra`) and the
ternary truth universe `TriTruth` (from `Base369`, mirrored in
`AgdaMirror.Base369`):

* the forward/back maps `toTriTruth`/`fromTriTruth` form an isomorphism
  (`toFrom`, `fromTo`);
* the ternary rotation `rotTrit` is intertwined with `Base369.rotateTri`
  (`rotTrit_equivariant_to`, `rotTrit_equivariant_from`);
* the induced `tritXor` is intertwined with `Base369.triXor` and inherits its
  left identity and associativity;
* the genuine **negation/rotation distinction** is preserved as a disproof
  (`inv_not_rotation_at_neg`, `inv_not_xor_hom_at_neg`) — these are real
  obstructions, faithfully kept as inequalities rather than fudged.

All proofs are by case analysis / reuse of the `Base369` laws; no `sorry`,
axiom-clean.
-/

namespace AgdaMirror.TritBridge

open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Trit)

/-- Forward map: balanced-ternary digit to ternary truth. -/
def toTriTruth : Trit → TriTruth
  | .neg => .low
  | .zer => .mid
  | .pos => .high

/-- Back map. -/
def fromTriTruth : TriTruth → Trit
  | .low => .neg
  | .mid => .zer
  | .high => .pos

theorem toFrom (t : TriTruth) : toTriTruth (fromTriTruth t) = t := by cases t <;> rfl
theorem fromTo (t : Trit) : fromTriTruth (toTriTruth t) = t := by cases t <;> rfl

/-- Cyclic rotation on the balanced-ternary carrier. -/
def rotTrit : Trit → Trit
  | .neg => .zer
  | .zer => .pos
  | .pos => .neg

theorem rotTrit_equivariant_to (t : Trit) :
    toTriTruth (rotTrit t) = rotateTri (toTriTruth t) := by cases t <;> rfl

theorem rotTrit_equivariant_from (t : TriTruth) :
    fromTriTruth (rotateTri t) = rotTrit (fromTriTruth t) := by cases t <;> rfl

/-- The genuine reflection-vs-rotation distinction: digit negation is *not* the
cyclic rotation (witnessed at `neg`). Faithfully preserved as a real inequality. -/
theorem inv_not_rotation_at_neg : Trit.inv .neg ≠ rotTrit .neg := by decide

/-- Induced ternary XOR transported through the bridge. -/
def tritXor (a b : Trit) : Trit :=
  fromTriTruth (triXor (toTriTruth a) (toTriTruth b))

theorem triXor_equivariant (a b : Trit) :
    toTriTruth (tritXor a b) = triXor (toTriTruth a) (toTriTruth b) := by
  cases a <;> cases b <;> rfl

theorem tritXor_idL (t : Trit) : tritXor .neg t = t := by
  cases t <;> rfl

theorem tritXor_assoc (a b c : Trit) :
    tritXor a (tritXor b c) = tritXor (tritXor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem inv_invol (t : Trit) : Trit.inv (Trit.inv t) = t := Trit.inv_invol t

/-- Negation is not an XOR-homomorphism (witnessed at `neg`); a genuine
obstruction, kept faithfully. -/
theorem inv_not_xor_hom_at_neg :
    Trit.inv (tritXor .neg .neg) ≠ tritXor (Trit.inv .neg) (Trit.inv .neg) := by decide

/-- The `Trit ↔ TriTruth` isomorphism surface (mirrors `TritTriTruthIso`). -/
structure TritTriTruthIso where
  toTri : Trit → TriTruth
  fromTri : TriTruth → Trit
  to_from : ∀ t, toTri (fromTri t) = t
  from_to : ∀ t, fromTri (toTri t) = t
  rotation_equivariant : ∀ t, toTri (rotTrit t) = rotateTri (toTri t)
  xor_equivariant : ∀ a b, toTri (tritXor a b) = triXor (toTri a) (toTri b)
  xor_idL : ∀ t, tritXor .neg t = t
  xor_assoc : ∀ a b c, tritXor a (tritXor b c) = tritXor (tritXor a b) c
  reflection_invol : ∀ t, Trit.inv (Trit.inv t) = t
  reflection_not_rotation : Trit.inv .neg ≠ rotTrit .neg
  reflection_not_xor_hom :
    Trit.inv (tritXor .neg .neg) ≠ tritXor (Trit.inv .neg) (Trit.inv .neg)

/-- The canonical isomorphism surface. -/
def tritTriTruthIso : TritTriTruthIso where
  toTri := toTriTruth
  fromTri := fromTriTruth
  to_from := toFrom
  from_to := fromTo
  rotation_equivariant := rotTrit_equivariant_to
  xor_equivariant := triXor_equivariant
  xor_idL := tritXor_idL
  xor_assoc := tritXor_assoc
  reflection_invol := inv_invol
  reflection_not_rotation := inv_not_rotation_at_neg
  reflection_not_xor_hom := inv_not_xor_hom_at_neg

end AgdaMirror.TritBridge
