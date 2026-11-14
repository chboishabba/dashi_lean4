import Synthesis.MillenniumBSDCMTwoAdicValuationArithmeticExact
import Synthesis.MillenniumBSDTotalLocalKummer
import Synthesis.MillenniumBSDExplicitSelmerSubgroup
import Synthesis.MillenniumBSDCMAllPrimeRationalSquareSupportExact
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# BSD selected curve: first x-T square-class support at every prime

The integer trichotomy does NOT depend on p=2: for any prime p and
y²=x(x-1)(x+1), the first-coordinate valuation v_p(x) is even,
except the zero x value where the total Kummer map uses [-1].

This module proves that result on the original Q_[p] point carrier,
the original PadicSquareClass p, the original totalLocalKummer p,
and the original LocalKummerImage p.

The global rational support conclusion is then routed through the
original all-place explicitTwoSelmerSubgroup, with the actual
Rat.isSquare_iff_even_factorization theorem.

No new elliptic model, no artificial Selmer subgroup, no conditional
source-record inhabitant. Current exact-head local Lean kernel pending.
-/

namespace Synthesis.Millennium.BSD

variable {p : ℕ} [Fact p.Prime]

theorem cmQpValuation_negOne :
    ((-1 : ℚ_[p]).valuation) = 0 := by
  have h : (2 : ℤ) * ((-1 : ℚ_[p]).valuation) = 0 := by
    calc
      (2 : ℤ) * ((-1 : ℚ_[p]).valuation) =
          (((-1 : ℚ_[p]) ^ 2).valuation) := by
            rw [Padic.valuation_pow]
            ring
      _ = 0 := by norm_num [Padic.valuation_one]
  omega

theorem cmQpValuation_neg (x : ℚ_[p]) (hx : x ≠ 0) :
    (-x).valuation = x.valuation := by
  calc
    (-x).valuation = ((-1 : ℚ_[p]) * x).valuation := by
      congr 1
      ring
    _ = ((-1 : ℚ_[p]).valuation) + x.valuation :=
      Padic.valuation_mul (by norm_num) hx
    _ = x.valuation := by rw [cmQpValuation_negOne]; omega

/-- Strict minimum law derived from the actual p-adic triangle inequality. -/
theorem cmQpValuation_add_of_lt
    (a b : ℚ_[p])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0)
    (hlt : a.valuation < b.valuation) :
    (a + b).valuation = a.valuation := by
  have hforward : a.valuation ≤ (a + b).valuation := by
    have h := Padic.le_valuation_add hab
    simpa [min_eq_left (le_of_lt hlt)] using h
  have hback : min (a + b).valuation b.valuation ≤ a.valuation := by
    have h : (a + b) + (-b) ≠ 0 := by
      simpa [add_assoc] using ha
    have hh := Padic.le_valuation_add h
    rw [cmQpValuation_neg b hb] at hh
    simpa [add_assoc] using hh
  have hreverse : (a + b).valuation ≤ a.valuation := by
    by_contra hcontra
    have hg : a.valuation < (a + b).valuation :=
      lt_of_not_ge hcontra
    have hmin : a.valuation <
        min (a + b).valuation b.valuation := lt_min hg hlt
    omega
  exact le_antisymm hreverse hforward

/-- All ordinary affine x-T points use the literal selected cubic. -/
theorem cmQpAffine_factorization
    (x y : ℚ_[p]) (hcurve : y ^ 2 = x ^ 3 - x) :
    y ^ 2 = x * (x - 1) * (x + 1) := by
  calc
    y ^ 2 = x ^ 3 - x := hcurve
    _ = x * (x - 1) * (x + 1) := by ring

theorem cmQpAffine_nonzero_factors
    (x y : ℚ_[p]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 := by
  have hf := cmQpAffine_factorization x y hcurve
  have hprod : x * (x - 1) * (x + 1) ≠ 0 := by
    rw [← hf]
    exact pow_ne_zero 2 hy
  have hx : x ≠ 0 := by
    intro h; simp [h] at hprod
  have hm : x - 1 ≠ 0 := by
    intro h; rw [h] at hprod; simp at hprod
  have hp : x + 1 ≠ 0 := by
    intro h; rw [h] at hprod; simp at hprod
  exact ⟨hx, hm, hp⟩

theorem cmQpValuationCurveIdentity
    (x y : ℚ_[p]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    2 * y.valuation =
      x.valuation + (x - 1).valuation + (x + 1).valuation := by
  obtain ⟨hx, hm, hp⟩ := cmQpAffine_nonzero_factors x y hcurve hy
  have hf := cmQpAffine_factorization x y hcurve
  calc
    2 * y.valuation = (y ^ 2).valuation := by
      rw [Padic.valuation_pow]
      ring
    _ = (x * (x - 1) * (x + 1)).valuation := by rw [hf]
    _ = x.valuation + (x - 1).valuation + (x + 1).valuation := by
      rw [Padic.valuation_mul (mul_ne_zero hx hm) hp]
      rw [Padic.valuation_mul hx hm]

theorem cmQpShiftedValuationPositive
    (x : ℚ_[p]) (hx : 0 < x.valuation) :
    (x - 1).valuation = 0 ∧ (x + 1).valuation = 0 := by
  have hxne : x ≠ 0 := by
    intro h; simp [h, Padic.valuation_zero] at hx
  have hxone : x ≠ 1 := by
    intro h; simp [h, Padic.valuation_one] at hx
  have hxnegone : x ≠ -1 := by
    intro h; rw [h, cmQpValuation_negOne] at hx; omega
  have hxplus : x + 1 ≠ 0 := by
    intro heq
    apply hxnegone
    calc
      x = (x + 1) - 1 := by ring
      _ = -1 := by rw [heq]; ring
  constructor
  · have h := cmQpValuation_add_of_lt
      (-1 : ℚ_[p]) x (by norm_num) hxne
      (by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hxone)
      (by rw [cmQpValuation_negOne]; exact hx)
    simpa [sub_eq_add_neg, add_comm, cmQpValuation_negOne] using h
  · have h := cmQpValuation_add_of_lt
      (1 : ℚ_[p]) x (by norm_num) hxne
      (by simpa [add_comm] using hxplus)
      (by simpa [Padic.valuation_one] using hx)
    simpa [add_comm, Padic.valuation_one] using h

theorem cmQpShiftedValuationNegative
    (x : ℚ_[p]) (hx : x.valuation < 0) :
    (x - 1).valuation = x.valuation ∧
      (x + 1).valuation = x.valuation := by
  have hxne : x ≠ 0 := by
    intro h; simp [h, Padic.valuation_zero] at hx
  have hxone : x ≠ 1 := by
    intro h; simp [h, Padic.valuation_one] at hx
  have hxnegone : x ≠ -1 := by
    intro h; rw [h, cmQpValuation_negOne] at hx; omega
  have hxplus : x + 1 ≠ 0 := by
    intro heq
    apply hxnegone
    calc
      x = (x + 1) - 1 := by ring
      _ = -1 := by rw [heq]; ring
  constructor
  · have h := cmQpValuation_add_of_lt
      x (-1 : ℚ_[p]) hxne (by norm_num)
      (by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hxone)
      (by rw [cmQpValuation_negOne]; exact hx)
    simpa [sub_eq_add_neg] using h
  · have h := cmQpValuation_add_of_lt
      x (1 : ℚ_[p]) hxne (by norm_num)
      hxplus
      (by simpa [Padic.valuation_one] using hx)
    exact h

theorem cmQpNonexceptionalXValuationEven
    (x y : ℚ_[p]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    Even x.valuation := by
  exact cmTwoAdicValuationParity_even
    x.valuation y.valuation (x - 1).valuation (x + 1).valuation
    (cmQpValuationCurveIdentity x y hcurve hy)
    (cmQpShiftedValuationPositive x)
    (cmQpShiftedValuationNegative x)

/-- The ordinary local x-T branch includes x=-1, y=0,
whose x valuation is also zero at every prime. -/
theorem cmQpOrdinaryXValuationEven_all
    (P : OrdinaryPadicKummerPoint p) :
    Even P.x.valuation := by
  by_cases hy : P.y = 0
  · have hf := cmQpAffine_factorization P.x P.y P.onCurve
    have hprod : P.x * (P.x - 1) * (P.x + 1) = 0 := by
      calc
        P.x * (P.x - 1) * (P.x + 1) = P.y ^ 2 := hf.symm
        _ = 0 := by rw [hy]; ring
    have hxplus : P.x + 1 = 0 := by
      rcases mul_eq_zero.mp hprod with hleft | hright
      · rcases mul_eq_zero.mp hleft with hzero | hone
        · exact False.elim (P.x_ne_zero hzero)
        · exact False.elim (P.x_ne_one (sub_eq_zero.mp hone))
      · exact hright
    have hx : P.x = -1 := by
      calc
        P.x = (P.x + 1) - 1 := by ring
        _ = -1 := by rw [hxplus]; ring
    simp [hx, cmQpValuation_negOne]
  · exact cmQpNonexceptionalXValuationEven
      P.x P.y P.onCurve hy

theorem cmQpSquareRel_preservesValuationParity
    (a b : NonzeroPadic p)
    (h : PadicSquareRel p a b) :
    ((a : ℚ_[p]).valuation % 2) =
      ((b : ℚ_[p]).valuation % 2) := by
  rcases h with ⟨s, t, hst⟩
  have hval :
      (a : ℚ_[p]).valuation + 2 * (s : ℚ_[p]).valuation =
        (b : ℚ_[p]).valuation + 2 * (t : ℚ_[p]).valuation := by
    calc
      (a : ℚ_[p]).valuation + 2 * (s : ℚ_[p]).valuation =
          ((a : ℚ_[p]) * (s : ℚ_[p]) ^ 2).valuation := by
            rw [Padic.valuation_mul a.property (pow_ne_zero 2 s.property)]
            rw [Padic.valuation_pow]
            ring
      _ = ((b : ℚ_[p]) * (t : ℚ_[p]) ^ 2).valuation :=
        congrArg Padic.valuation hst
      _ = (b : ℚ_[p]).valuation + 2 * (t : ℚ_[p]).valuation := by
            rw [Padic.valuation_mul b.property (pow_ne_zero 2 t.property)]
            rw [Padic.valuation_pow]
            ring
  omega

/-- Valuation parity on the ACTUAL original local square-class quotient
for an arbitrary prime p. -/
noncomputable def cmQpSquareClassValuationParity
    (p : ℕ) [Fact p.Prime] : PadicSquareClass p → ℤ :=
  Quotient.lift
    (fun a : NonzeroPadic p => (a : ℚ_[p]).valuation % 2)
    (fun a b h => cmQpSquareRel_preservesValuationParity a b h)

theorem cmQpSquareClassValuationParity_rep
    (a : NonzeroPadic p) :
    cmQpSquareClassValuationParity p (padicSquareClassOf p a) =
      (a : ℚ_[p]).valuation % 2 := rfl

theorem cmQpOrdinaryKummer_firstParity_zero
    (P : OrdinaryPadicKummerPoint p) :
    cmQpSquareClassValuationParity p (ordinaryPadicKummer P).1 = 0 := by
  change cmQpSquareClassValuationParity p
    (padicSquareClassOf p (⟨P.x, P.x_ne_zero⟩ : NonzeroPadic p)) = 0
  rw [cmQpSquareClassValuationParity_rep]
  rcases cmQpOrdinaryXValuationEven_all P with ⟨k, hk⟩
  omega

theorem cmQpLocalClassOne_firstParity_zero :
    cmQpSquareClassValuationParity p
      (localRationalClass p oneNZ) = 0 := by
  change cmQpSquareClassValuationParity p
    (localizeSquareClass p (squareClassOf oneNZ)) = 0
  rw [localizeSquareClass_mk, cmQpSquareClassValuationParity_rep]
  simp [localizeNonzeroRat, oneNZ, Padic.valuation_one]

theorem cmQpLocalClassNegOne_firstParity_zero :
    cmQpSquareClassValuationParity p
      (localRationalClass p negOneNZ) = 0 := by
  change cmQpSquareClassValuationParity p
    (localizeSquareClass p (squareClassOf negOneNZ)) = 0
  rw [localizeSquareClass_mk, cmQpSquareClassValuationParity_rep]
  simp [localizeNonzeroRat, negOneNZ, cmQpValuation_negOne]

/-- Original total local Kummer image has first-coordinate parity
zero at EVERY prime, not only p=2. -/
theorem cmQpTotalLocalKummer_firstParity_zero
    (P : PadicProjectivePoint p) :
    cmQpSquareClassValuationParity p (totalLocalKummer p P).1 = 0 := by
  cases P with
  | infinity =>
      exact cmQpLocalClassOne_firstParity_zero
  | affine x y hcurve =>
      by_cases hxzero : x = 0
      · simpa [totalLocalKummer, hxzero] using
          (cmQpLocalClassNegOne_firstParity_zero (p := p))
      · by_cases hxone : x = 1
        · simpa [totalLocalKummer, hxzero, hxone] using
            (cmQpLocalClassOne_firstParity_zero (p := p))
        · let Q : OrdinaryPadicKummerPoint p :=
            { x := x, y := y, onCurve := hcurve
            , x_ne_zero := hxzero, x_ne_one := hxone }
          have h := cmQpOrdinaryKummer_firstParity_zero Q
          simpa [totalLocalKummer, hxzero, hxone, Q] using h

theorem cmQpLocalKummerImage_firstParity_zero
    (c : PadicSquareClass p × PadicSquareClass p)
    (hc : c ∈ LocalKummerImage p) :
    cmQpSquareClassValuationParity p c.1 = 0 := by
  rcases hc with ⟨P, rfl⟩
  exact cmQpTotalLocalKummer_firstParity_zero P

/-- Actual rational-to-Q_p valuation parity commuting square on the
original quotient REPRESENTATIVES. This is enough for the all-prime
support theorem via induction on the original RatSquareClass quotient. -/
theorem cmQpSquareClassParity_localize_rational_rep
    (a : NonzeroRat) :
    ((cmQpSquareClassValuationParity p
      (localizeSquareClass p (squareClassOf a)) : ℤ) : ZMod 2) =
        (padicValRat p (a : ℚ) : ZMod 2) := by
  rw [localizeSquareClass_mk, cmQpSquareClassValuationParity_rep]
  change
    (((((a : ℚ) : ℚ_[p]).valuation % 2 : ℤ) : ZMod 2) =
      (padicValRat p (a : ℚ) : ZMod 2)
  rw [Padic.valuation_ratCast]
  exact ZMod.intCast_mod _ _


/-- A literal all-place local Kummer condition forces the ORIGINAL
first rational square class to be one of [1] and [-1].
This theorem uses all primes and Rat.isSquare_iff_even_factorization;
no finite-code surjectivity or Selmer-cohomology equivalence is assumed. -/
theorem cmRationalFirstSquareClass_unitSupport_of_allLocalImages
    (c : RatSquareClass × RatSquareClass)
    (hloc :
      ∀ pv : Nat.Primes,
        letI : Fact pv.1.Prime := ⟨pv.2⟩
        localizeKummerPair pv.1 c ∈ LocalKummerImage pv.1) :
    c.1 = squareClassOf oneNZ ∨
      c.1 = squareClassOf negOneNZ := by
  rcases c with ⟨first, second⟩
  revert hloc
  refine Quotient.inductionOn first ?_
  intro a hloc
  apply cmRationalSquareClass_one_or_negOne_of_allPrimeEven a
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hmem :
      localizeKummerPair p (squareClassOf a, second) ∈
        LocalKummerImage p :=
    hloc (⟨p, hp⟩ : Nat.Primes)
  have hval :=
    cmQpLocalKummerImage_firstParity_zero
      (p := p) (localizeKummerPair p (squareClassOf a, second))
      hmem
  change
    cmQpSquareClassValuationParity p
      (localizeSquareClass p (squareClassOf a)) = 0 at hval
  have hcomm :=
    cmQpSquareClassParity_localize_rational_rep (p := p) a
  rw [hval] at hcomm
  have hcast :
      (padicValRat p (a : ℚ) : ZMod 2) = 0 := by
    simpa using hcomm.symm
  exact ZMod.intCast_eq_zero_iff_even.mp hcast

/-- Global same-object BSD corollary:
every member of the original explicitTwoSelmerSubgroup has
first x-T coordinate [1] or [-1]. This is stronger than the
previous p=2-only parity theorem. -/
theorem cmExplicitTwoSelmer_firstSquareClass_unitSupport
    (s : explicitTwoSelmerSubgroup) :
    ((s : RatSquareClass × RatSquareClass).1) =
        squareClassOf oneNZ ∨
      ((s : RatSquareClass × RatSquareClass).1) =
        squareClassOf negOneNZ := by
  have hloc :
      ∀ pv : Nat.Primes,
        letI : Fact pv.1.Prime := ⟨pv.2⟩
        localizeKummerPair pv.1
          (s : RatSquareClass × RatSquareClass) ∈
            LocalKummerImage pv.1 := s.property.2
  exact cmRationalFirstSquareClass_unitSupport_of_allLocalImages
    (s : RatSquareClass × RatSquareClass) hloc

end Synthesis.Millennium.BSD
