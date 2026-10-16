import Integration.EisensteinJZeroPrimaryNormalizationExact
import Integration.EisensteinJZeroInertPrimeEulerExact
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Dashi.EisensteinJZeroQuadraticCharacterTraceExact

open Finset
open Dashi.EisensteinJZeroInertPrimeEulerExact

/-- The finite square-root fibre over `a ∈ F_p`, represented by the literal
finset used by Mathlib's quadratic-character cardinality theorem. -/
def squareRootFinset (p : Nat) (a : ZMod p) : Finset (ZMod p) :=
  ({y : ZMod p | y ^ 2 = a} : Set (ZMod p)).toFinset

/-- The square-root fibre as a finite type. -/
def SquareFiber (p : Nat) (a : ZMod p) := ↥(squareRootFinset p a)

instance (p : Nat) (a : ZMod p) : Fintype (SquareFiber p a) := inferInstance

/-- Mathlib's standard quadratic character gives the exact fibre cardinality
`# {y | y²=a} = 1 + χ₂(a)` in odd characteristic. -/
theorem squareFiberCard_eq_one_add_quadraticChar
    (p : Nat) [Fact p.Prime] (hp2 : p ≠ 2) (a : ZMod p) :
    (Fintype.card (SquareFiber p a) : Int)
      = quadraticChar (ZMod p) a + 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 :=
    ne_of_eq_of_ne (ringChar_zmod_n p) hp2
  have h := quadraticChar_card_sqrts (F := ZMod p) hchar a
  simpa [SquareFiber, squareRootFinset, Fintype.card_coe] using h

/-- Decompose the affine `j=0` point set by x-coordinate and its square-root
fibre. -/
noncomputable def affinePointSigmaEquiv
    (p : Nat) :
    JZeroAffinePoint p ≃ Sigma (fun x : ZMod p => SquareFiber p (x ^ 3 + 1)) where
  toFun P := by
    refine ⟨P.1.1, ⟨P.1.2, ?_⟩⟩
    simp [SquareFiber, squareRootFinset, P.2]
  invFun P := by
    refine ⟨(P.1, P.2.1), ?_⟩
    simpa [SquareFiber, squareRootFinset] using P.2.2
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv P := by
    cases P with
    | mk x y =>
      cases y
      rfl

/-- The standard quadratic-character sum controlling the affine point count. -/
def jZeroQuadraticCharacterSum (p : Nat) [Fintype (ZMod p)] : Int :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 1)

/-- Exact affine point-count identity on every odd prime field:
`#E_aff(F_p) = p + Σ_x χ₂(x³+1)`. -/
theorem affinePointCount_eq_card_add_characterSum
    (p : Nat) [Fact p.Prime] (hp2 : p ≠ 2) :
    (Fintype.card (JZeroAffinePoint p) : Int)
      = (p : Int) + jZeroQuadraticCharacterSum p := by
  letI : NeZero p := ⟨Fact.out.ne_zero⟩
  have hsigma :
      Fintype.card (JZeroAffinePoint p)
        = ∑ x : ZMod p, Fintype.card (SquareFiber p (x ^ 3 + 1)) := by
    calc
      Fintype.card (JZeroAffinePoint p)
          = Fintype.card (Sigma (fun x : ZMod p => SquareFiber p (x ^ 3 + 1))) :=
            Fintype.card_congr (affinePointSigmaEquiv p)
      _ = ∑ x : ZMod p, Fintype.card (SquareFiber p (x ^ 3 + 1)) :=
            Fintype.card_sigma
  exact_mod_cast hsigma at hsigma
  rw [hsigma]
  simp_rw [squareFiberCard_eq_one_add_quadraticChar p hp2]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
    ZMod.card, jZeroQuadraticCharacterSum]
  ring

/-- Consequently the Frobenius trace of the same curve is exactly the negative
quadratic-character sum.  This is the finite-field bridge consumed by the
remaining cubic/Jacobi-sum CM evaluation. -/
theorem frobeniusTrace_eq_neg_characterSum
    (p : Nat) [Fact p.Prime] (hp2 : p ≠ 2) :
    jZeroFrobeniusTrace p = -jZeroQuadraticCharacterSum p := by
  letI : NeZero p := ⟨Fact.out.ne_zero⟩
  rw [jZeroFrobeniusTrace, jZeroProjectivePointCount,
    affinePointCount_eq_card_add_characterSum p hp2]
  push_cast
  ring

/-- The inert-family theorem forces the same character sum to vanish. -/
theorem quadraticCharacterSum_inert
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 2) :
    jZeroQuadraticCharacterSum p = 0 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hmod
  have htrace := frobeniusTrace_eq_neg_characterSum p hp2
  rw [frobeniusTrace_inert p hmod] at htrace
  linarith

/-- Literal regressions retained as same-object checks of the general formula. -/
theorem quadraticCharacterSum_five : jZeroQuadraticCharacterSum 5 = 0 := by
  native_decide

theorem quadraticCharacterSum_seven : jZeroQuadraticCharacterSum 7 = 4 := by
  native_decide

/-- Claim-strength boundary after moving the elliptic point count into the
standard quadratic-character channel.  The remaining split-prime theorem is
now specifically a cubic/Jacobi-sum evaluation identifying this character sum
with the trace of the unique primary Eisenstein generator. -/
structure QuadraticCharacterTraceBoundary where
  standardQuadraticCharacterUsed : Bool := true
  squareRootFibreCardinalityPaid : Bool := true
  affinePointSigmaDecompositionPaid : Bool := true
  frobeniusTraceCharacterSumPaid : Bool := true
  inertCharacterSumVanishingPaid : Bool := true
  cubicJacobiSumEvaluationPaid : Bool := false
  primaryTraceFrobeniusIdentificationPaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticHeckeLSeriesIdentityPaid : Bool := false

/-- Exact current character-sum frontier. -/
def canonicalBoundary : QuadraticCharacterTraceBoundary := {}

end Dashi.EisensteinJZeroQuadraticCharacterTraceExact
