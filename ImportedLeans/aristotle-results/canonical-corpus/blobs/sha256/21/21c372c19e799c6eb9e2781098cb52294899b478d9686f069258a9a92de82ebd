import Mathlib
import AgdaMirror.GodelLattice

/-!
# Lean mirror of the `NormalizeAdd` carry-resolution cluster (genuine, fully proved)

Faithful transcription of:
* `DASHI/Arithmetic/NormalizeAddState.agda` — the carry-resolution state record
  and its agreement / canonical predicates;
* `DASHI/Arithmetic/NormalizeAdd.agda` — the one-step carry resolution
  `normalizeAdd` reaching the canonical form;
* `DASHI/Arithmetic/CanonicalResidueZero.agda` — the residue-budget proxy and the
  surface theorem that `normalizeAdd` lands in the zero residue-budget canonical
  form after one step.

This is a genuine (constructive, axiom-clean) state model, not a vacuous
interface.
-/

namespace AgdaMirror.NormalizeAdd

open AgdaMirror.GodelLattice

/-- The carry-resolution state. -/
structure NormalizeAddState where
  prime : Nat
  lhs : Nat
  rhs : Nat
  residueDepth : Nat
  carryDepth : Nat
  padicDepth : Nat
  carryBudget : Nat
  carryTrace : Nat
  primeProfile : Vec15 Nat

/-- `p`-adic agreement surface for the first landing. -/
def padicAgreement (x y : NormalizeAddState) (k : Nat) : Prop :=
  x.prime = y.prime ∧ x.padicDepth = y.padicDepth ∧
    k ≤ x.padicDepth ∧ k ≤ y.padicDepth

/-- The carry is resolved when its depth and trace are zero. -/
def carryResolved (s : NormalizeAddState) : Prop :=
  s.carryDepth = 0 ∧ s.carryTrace = 0

/-- The canonical form: residue depth equals `p`-adic depth and all carry
fields are zero. -/
def normalizeAddCanonical (s : NormalizeAddState) : Prop :=
  s.residueDepth = s.padicDepth ∧ s.carryDepth = 0 ∧
    s.carryBudget = 0 ∧ s.carryTrace = 0

/-- The all-zero prime profile. -/
def zeroPrimeProfile : Vec15 Nat := replicate 0

/-- One-step carry resolution. -/
def normalizeAdd (s : NormalizeAddState) : NormalizeAddState :=
  { s with
    residueDepth := s.padicDepth
    carryDepth := 0
    carryBudget := 0
    carryTrace := 0
    primeProfile := zeroPrimeProfile }

theorem normalizeAdd_primePreserved (s : NormalizeAddState) :
    (normalizeAdd s).prime = s.prime := rfl

theorem normalizeAdd_padicDepthPreserved (s : NormalizeAddState) :
    (normalizeAdd s).padicDepth = s.padicDepth := rfl

theorem normalizeAdd_residueDepthCanonical (s : NormalizeAddState) :
    (normalizeAdd s).residueDepth = s.padicDepth := rfl

theorem normalizeAdd_carryResolved (s : NormalizeAddState) :
    carryResolved (normalizeAdd s) := ⟨rfl, rfl⟩

theorem normalizeAdd_canonical (s : NormalizeAddState) :
    normalizeAddCanonical (normalizeAdd s) := ⟨rfl, rfl, rfl, rfl⟩

/-! ### `CanonicalResidueZero`: the residue-budget proxy -/

/-- The residue-budget proxy: the carry budget is zero. -/
def StateResidueBudget (s : NormalizeAddState) : Prop := s.carryBudget = 0

/-- Direct extraction from any canonical tuple. -/
theorem canonicalResidueBudget_fromCanonical (s : NormalizeAddState)
    (h : normalizeAddCanonical s) : StateResidueBudget s := h.2.2.1

/-- `normalizeAdd` lands in the zero residue-budget proxy after one step. -/
theorem normalizeAdd_zeroResidueBudget (s : NormalizeAddState) :
    StateResidueBudget (normalizeAdd s) :=
  canonicalResidueBudget_fromCanonical _ (normalizeAdd_canonical s)

end AgdaMirror.NormalizeAdd
