import Synthesis.MillenniumBSDRationalSquareBits
import Mathlib.Tactic

/-!
# Literal quotient type Q*/Q*^2 with descended bit invariants

The Agda lane owns the generated square-equivalence relation.  Here we construct
an actual quotient type in Lean and descend the postulate-free sign and 2-adic
valuation-parity invariants to quotient classes.

The equivalence relation is presented without division:
`a ~ b` iff `a*s^2 = b*t^2` for nonzero rational `s,t`.
-/

namespace Synthesis.Millennium.BSD

abbrev NonzeroRat := {q : ℚ // q ≠ 0}

def SquareRel (a b : NonzeroRat) : Prop :=
  ∃ s t : NonzeroRat, (a : ℚ) * (s : ℚ) ^ 2 = (b : ℚ) * (t : ℚ) ^ 2

theorem squareRel_refl (a : NonzeroRat) : SquareRel a a := by
  refine ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩, ?_⟩
  ring

theorem squareRel_symm {a b : NonzeroRat} :
    SquareRel a b → SquareRel b a := by
  rintro ⟨s, t, h⟩
  exact ⟨t, s, h.symm⟩

theorem squareRel_trans {a b c : NonzeroRat} :
    SquareRel a b → SquareRel b c → SquareRel a c := by
  rintro ⟨s₁, t₁, h₁⟩ ⟨s₂, t₂, h₂⟩
  let s : NonzeroRat :=
    ⟨(s₁ : ℚ) * (s₂ : ℚ), mul_ne_zero s₁.property s₂.property⟩
  let t : NonzeroRat :=
    ⟨(t₂ : ℚ) * (t₁ : ℚ), mul_ne_zero t₂.property t₁.property⟩
  refine ⟨s, t, ?_⟩
  dsimp [s, t]
  calc
    (a : ℚ) * ((s₁ : ℚ) * (s₂ : ℚ)) ^ 2
        = ((a : ℚ) * (s₁ : ℚ) ^ 2) * (s₂ : ℚ) ^ 2 := by ring
    _ = ((b : ℚ) * (t₁ : ℚ) ^ 2) * (s₂ : ℚ) ^ 2 := by rw [h₁]
    _ = ((b : ℚ) * (s₂ : ℚ) ^ 2) * (t₁ : ℚ) ^ 2 := by ring
    _ = ((c : ℚ) * (t₂ : ℚ) ^ 2) * (t₁ : ℚ) ^ 2 := by rw [h₂]
    _ = (c : ℚ) * ((t₂ : ℚ) * (t₁ : ℚ)) ^ 2 := by ring

def ratSquareSetoid : Setoid NonzeroRat where
  r := SquareRel
  iseqv := ⟨squareRel_refl, squareRel_symm, squareRel_trans⟩

abbrev RatSquareClass := Quotient ratSquareSetoid

def squareClassOf (q : NonzeroRat) : RatSquareClass :=
  Quotient.mk ratSquareSetoid q

theorem signBit_respects_squareRel {a b : NonzeroRat} :
    SquareRel a b → signBit (a : ℚ) = signBit (b : ℚ) := by
  rintro ⟨s, t, h⟩
  calc
    signBit (a : ℚ)
        = signBit ((a : ℚ) * (s : ℚ) ^ 2) :=
          (signBit_mul_sq (a : ℚ) (s : ℚ) s.property).symm
    _ = signBit ((b : ℚ) * (t : ℚ) ^ 2) := congrArg signBit h
    _ = signBit (b : ℚ) :=
          signBit_mul_sq (b : ℚ) (t : ℚ) t.property

theorem v2Parity_respects_squareRel {a b : NonzeroRat} :
    SquareRel a b → v2Parity (a : ℚ) = v2Parity (b : ℚ) := by
  rintro ⟨s, t, h⟩
  calc
    v2Parity (a : ℚ)
        = v2Parity ((a : ℚ) * (s : ℚ) ^ 2) :=
          (v2Parity_mul_sq
            (a : ℚ) (s : ℚ) a.property s.property).symm
    _ = v2Parity ((b : ℚ) * (t : ℚ) ^ 2) := congrArg v2Parity h
    _ = v2Parity (b : ℚ) :=
          v2Parity_mul_sq
            (b : ℚ) (t : ℚ) b.property t.property

def squareClassSignBit : RatSquareClass → Bool :=
  Quotient.lift
    (fun q : NonzeroRat => signBit (q : ℚ))
    (fun _ _ h => signBit_respects_squareRel h)

def squareClassV2Parity : RatSquareClass → ZMod 2 :=
  Quotient.lift
    (fun q : NonzeroRat => v2Parity (q : ℚ))
    (fun _ _ h => v2Parity_respects_squareRel h)

@[simp] theorem squareClassSignBit_mk (q : NonzeroRat) :
    squareClassSignBit (squareClassOf q) = signBit (q : ℚ) := rfl

@[simp] theorem squareClassV2Parity_mk (q : NonzeroRat) :
    squareClassV2Parity (squareClassOf q) = v2Parity (q : ℚ) := rfl

def oneNZ : NonzeroRat := ⟨1, by norm_num⟩
def negOneNZ : NonzeroRat := ⟨-1, by norm_num⟩
def twoNZ : NonzeroRat := ⟨2, by norm_num⟩
def negTwoNZ : NonzeroRat := ⟨-2, by norm_num⟩

theorem quotient_torsion_bits :
    (squareClassSignBit (squareClassOf oneNZ),
      squareClassV2Parity (squareClassOf oneNZ)) = (false, 0) ∧
    (squareClassSignBit (squareClassOf negOneNZ),
      squareClassV2Parity (squareClassOf negOneNZ)) = (true, 0) ∧
    (squareClassSignBit (squareClassOf oneNZ),
      squareClassV2Parity (squareClassOf twoNZ)) = (false, 1) ∧
    (squareClassSignBit (squareClassOf negOneNZ),
      squareClassV2Parity (squareClassOf negTwoNZ)) = (true, 1) := by
  simpa [oneNZ, negOneNZ, twoNZ, negTwoNZ] using torsion_dictionary_bits

end Synthesis.Millennium.BSD
