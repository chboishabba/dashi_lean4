import Synthesis.MillenniumBSDCMAllPrimeLocalFirstParityExact
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# BSD: good-prime second x-T local Kummer parity at p != 2

On E:y²=x(x-1)(x+1), the first coordinate x has even valuation
at all primes. For p != 2, the *second* coordinate x-1 has even
valuation too, since the two other factors differ from x-1 by 1
and 2, both p-adic units.

This file proves the actual local arithmetic on the original
Q_[p] affine curve, then the original OrdinaryPadicKummerPoint p.
The total local-Kummer image must additionally handle the
three exceptional branches, all with first/second classes of
1,-1,2; p != 2 makes 2 a unit.

No full global Selmer group order or Sha is claimed.
Source-written / local Lean kernel pending.
-/

namespace Synthesis.Millennium.BSD

variable {p : ℕ} [Fact p.Prime]

/-- At an odd prime, 2 is a genuine p-adic unit. -/
theorem cmQpOddValuation_two_zero
    (hne : p ≠ 2) :
    ((2 : ℚ_[p]).valuation) = 0 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : padicValNat p 2 = 0 :=
    padicValNat_primes (p := p) (q := 2) hne
  rw [show (2 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) from rfl,
    Padic.valuation_natCast]
  exact_mod_cast h

theorem cmQpOddValuation_negTwo_zero
    (hne : p ≠ 2) :
    ((-2 : ℚ_[p]).valuation) = 0 := by
  calc
    ((-2 : ℚ_[p]).valuation) =
        (((-1 : ℚ_[p]) * (2 : ℚ_[p])).valuation) := by
          congr 1
          ring
    _ = ((-1 : ℚ_[p]).valuation) + ((2 : ℚ_[p]).valuation) :=
      Padic.valuation_mul (by norm_num) (by norm_num)
    _ = 0 := by
      rw [cmQpValuation_negOne, cmQpOddValuation_two_zero hne]
      omega

/-- On ordinary local Qp points at odd p, v_p(x-1) is even.
The case y=0, x=-1 is handled explicitly. -/
theorem cmQpOddOrdinarySecondValuationEven
    (hne : p ≠ 2)
    (P : OrdinaryPadicKummerPoint p) :
    Even (P.x - 1).valuation := by
  by_cases hy : P.y = 0
  · have hf := cmQpAffine_factorization P.x P.y P.onCurve
    have hprod : P.x * (P.x - 1) * (P.x + 1) = 0 := by
      calc
        P.x * (P.x - 1) * (P.x + 1) = P.y ^ 2 := hf.symm
        _ = 0 := by rw [hy]; ring
    have hxplus : P.x + 1 = 0 := by
      rcases mul_eq_zero.mp hprod with hleft | hright
      · rcases mul_eq_zero.mp hleft with hz | ho
        · exact False.elim (P.x_ne_zero hz)
        · exact False.elim (P.x_ne_one (sub_eq_zero.mp ho))
      · exact hright
    have hx : P.x = -1 := by
      calc
        P.x = (P.x + 1) - 1 := by ring
        _ = -1 := by rw [hxplus]; ring
    have hsub : P.x - 1 = (-2 : ℚ_[p]) := by
      rw [hx]
      ring
    rw [hsub, cmQpOddValuation_negTwo_zero hne]
    exact even_zero
  · obtain ⟨hx, hm, hp⟩ :=
      cmQpAffine_nonzero_factors P.x P.y P.onCurve hy
    have hcurve :=
      cmQpValuationCurveIdentity P.x P.y P.onCurve hy
    let z : ℚ_[p] := P.x - 1
    have hz : z ≠ 0 := hm
    have hxone : (1 : ℚ_[p]) + z = P.x := by
      dsimp [z]
      ring
    have hxtwo : (2 : ℚ_[p]) + z = P.x + 1 := by
      dsimp [z]
      ring
    have htwo : ((2 : ℚ_[p]).valuation) = 0 :=
      cmQpOddValuation_two_zero hne
    rcases lt_trichotomy z.valuation 0 with hneg | hzero | hpos
    · have hvx : P.x.valuation = z.valuation := by
        have h := cmQpValuation_add_of_lt
          z (1 : ℚ_[p]) hz (by norm_num)
          (by rw [add_comm, hxone]; exact hx)
          (by simpa [Padic.valuation_one] using hneg)
        simpa [add_comm, hxone] using h
      have hvplus : (P.x + 1).valuation = z.valuation := by
        have h := cmQpValuation_add_of_lt
          z (2 : ℚ_[p]) hz (by norm_num)
          (by rw [add_comm, hxtwo]; exact hp)
          (by simpa [htwo] using hneg)
        simpa [add_comm, hxtwo] using h
      refine ⟨P.y.valuation - z.valuation, ?_⟩
      dsimp [z] at *
      omega
    · rw [hzero]
      exact even_zero
    · have hvx : P.x.valuation = 0 := by
        have h := cmQpValuation_add_of_lt
          (1 : ℚ_[p]) z (by norm_num) hz
          (by rw [hxone]; exact hx)
          (by simpa [Padic.valuation_one] using hpos)
        simpa [hxone, Padic.valuation_one] using h
      have hvplus : (P.x + 1).valuation = 0 := by
        have h := cmQpValuation_add_of_lt
          (2 : ℚ_[p]) z (by norm_num) hz
          (by rw [hxtwo]; exact hp)
          (by simpa [htwo] using hpos)
        simpa [hxtwo, htwo] using h
      refine ⟨P.y.valuation, ?_⟩
      dsimp [z] at *
      omega

theorem cmQpOddOrdinarySecondKummerParity_zero
    (hne : p ≠ 2)
    (P : OrdinaryPadicKummerPoint p) :
    cmQpSquareClassValuationParity p (ordinaryPadicKummer P).2 = 0 := by
  change cmQpSquareClassValuationParity p
    (padicSquareClassOf p
      (⟨P.x - 1, sub_ne_zero.mpr P.x_ne_one⟩ : NonzeroPadic p)) = 0
  rw [cmQpSquareClassValuationParity_rep]
  rcases cmQpOddOrdinarySecondValuationEven hne P with ⟨k, hk⟩
  omega

/-- All actual total-local Kummer branches at odd primes
have even valuation in their SECOND x-T coordinate. -/
theorem cmQpOddTotalLocalKummer_secondParity_zero
    (hne : p ≠ 2)
    (P : PadicProjectivePoint p) :
    cmQpSquareClassValuationParity p (totalLocalKummer p P).2 = 0 := by
  cases P with
  | infinity =>
      exact cmQpLocalClassOne_firstParity_zero
  | affine x y hcurve =>
      by_cases hxzero : x = 0
      · simpa [totalLocalKummer, hxzero] using
          (cmQpLocalClassNegOne_firstParity_zero (p := p))
      · by_cases hxone : x = 1
        · have htwo :
              cmQpSquareClassValuationParity p
                (localRationalClass p twoNZ) = 0 := by
            change cmQpSquareClassValuationParity p
              (localizeSquareClass p (squareClassOf twoNZ)) = 0
            rw [localizeSquareClass_mk,
              cmQpSquareClassValuationParity_rep]
            simp [localizeNonzeroRat, twoNZ,
              cmQpOddValuation_two_zero hne]
          simpa [totalLocalKummer, hxzero, hxone] using htwo
        · let Q : OrdinaryPadicKummerPoint p :=
            { x := x, y := y, onCurve := hcurve
            , x_ne_zero := hxzero, x_ne_one := hxone }
          have h := cmQpOddOrdinarySecondKummerParity_zero hne Q
          simpa [totalLocalKummer, hxzero, hxone, Q] using h

theorem cmQpOddLocalKummerImage_secondParity_zero
    (hne : p ≠ 2)
    (c : PadicSquareClass p × PadicSquareClass p)
    (hc : c ∈ LocalKummerImage p) :
    cmQpSquareClassValuationParity p c.2 = 0 := by
  rcases hc with ⟨P, rfl⟩
  exact cmQpOddTotalLocalKummer_secondParity_zero hne P

end Synthesis.Millennium.BSD
