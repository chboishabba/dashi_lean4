import Synthesis.MillenniumBSDLocalSquareClass
import Mathlib.Tactic

/-!
# Total local Kummer map for y² = x³ - x over Q_p

The local point carrier is literal: the point at infinity or an affine pair
(x,y) satisfying y²=x³-x in Q_p.  The Kummer map is total:

* O       ↦ ([1],[1])
* (0,0)   ↦ ([-1],[-1])
* (1,0)   ↦ ([1],[2])
* otherwise ↦ ([x],[x-1]).

The exceptional branches are forced by the curve equation: an affine point
with x=0 or x=1 has y=0.

The range of this map is the literal local Kummer image used by the 2-Selmer
local condition.  No claim about the Mordell-Weil group quotient is made yet.
-/

namespace Synthesis.Millennium.BSD

def localRationalClass
    (p : ℕ) [Fact p.Prime]
    (q : NonzeroRat) :
    PadicSquareClass p :=
  localizeSquareClass p (squareClassOf q)

inductive PadicProjectivePoint (p : ℕ) [Fact p.Prime] : Type where
  | infinity
  | affine (x y : ℚ_[p]) (onCurve : y ^ 2 = x ^ 3 - x)

def localInfinityKummer
    (p : ℕ) [Fact p.Prime] :
    PadicSquareClass p × PadicSquareClass p :=
  (localRationalClass p oneNZ,
   localRationalClass p oneNZ)

def localZeroKummer
    (p : ℕ) [Fact p.Prime] :
    PadicSquareClass p × PadicSquareClass p :=
  (localRationalClass p negOneNZ,
   localRationalClass p negOneNZ)

def localOneKummer
    (p : ℕ) [Fact p.Prime] :
    PadicSquareClass p × PadicSquareClass p :=
  (localRationalClass p oneNZ,
   localRationalClass p twoNZ)

theorem y_eq_zero_of_x_eq_zero
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (onCurve : y ^ 2 = x ^ 3 - x)
    (hx : x = 0) :
    y = 0 := by
  subst x
  simp at onCurve
  exact sq_eq_zero_iff.mp onCurve

theorem y_eq_zero_of_x_eq_one
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (onCurve : y ^ 2 = x ^ 3 - x)
    (hx : x = 1) :
    y = 0 := by
  subst x
  simp at onCurve
  exact sq_eq_zero_iff.mp onCurve

def totalLocalKummer
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p →
      PadicSquareClass p × PadicSquareClass p
  | .infinity =>
      localInfinityKummer p
  | .affine x y onCurve =>
      if hx0 : x = 0 then
        localZeroKummer p
      else if hx1 : x = 1 then
        localOneKummer p
      else
        ordinaryPadicKummer
          { x := x
          , y := y
          , onCurve := onCurve
          , x_ne_zero := hx0
          , x_ne_one := hx1 }

theorem totalLocalKummer_infinity
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p (.infinity) =
      localInfinityKummer p :=
  rfl

theorem totalLocalKummer_zero
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p
      (.affine 0 0 (by norm_num)) =
      localZeroKummer p := by
  simp [totalLocalKummer]

theorem totalLocalKummer_one
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p
      (.affine 1 0 (by norm_num)) =
      localOneKummer p := by
  simp [totalLocalKummer]

theorem totalLocalKummer_ordinary
    {p : ℕ} [Fact p.Prime]
    (P : OrdinaryPadicKummerPoint p) :
    totalLocalKummer p
      (.affine P.x P.y P.onCurve) =
      ordinaryPadicKummer P := by
  simp [totalLocalKummer, P.x_ne_zero, P.x_ne_one]

def LocalKummerImage
    (p : ℕ) [Fact p.Prime] :
    Set (PadicSquareClass p × PadicSquareClass p) :=
  Set.range (totalLocalKummer p)

theorem localInfinity_mem_KummerImage
    (p : ℕ) [Fact p.Prime] :
    localInfinityKummer p ∈ LocalKummerImage p :=
  ⟨.infinity, rfl⟩

theorem localZero_mem_KummerImage
    (p : ℕ) [Fact p.Prime] :
    localZeroKummer p ∈ LocalKummerImage p :=
  ⟨.affine 0 0 (by norm_num), by
    simp [totalLocalKummer]⟩

theorem localOne_mem_KummerImage
    (p : ℕ) [Fact p.Prime] :
    localOneKummer p ∈ LocalKummerImage p :=
  ⟨.affine 1 0 (by norm_num), by
    simp [totalLocalKummer]⟩

theorem localizedOrdinaryGlobalKummer_mem_localImage
    (p : ℕ) [Fact p.Prime]
    (P : OrdinaryKummerPoint) :
    localizeKummerPair p (ordinaryKummer P) ∈
      LocalKummerImage p := by
  refine ⟨.affine
    (localizeOrdinaryRationalPoint p P).x
    (localizeOrdinaryRationalPoint p P).y
    (localizeOrdinaryRationalPoint p P).onCurve, ?_⟩
  rw [totalLocalKummer_ordinary
    (localizeOrdinaryRationalPoint p P)]
  exact (ordinaryKummer_localizes p P).symm

end Synthesis.Millennium.BSD
