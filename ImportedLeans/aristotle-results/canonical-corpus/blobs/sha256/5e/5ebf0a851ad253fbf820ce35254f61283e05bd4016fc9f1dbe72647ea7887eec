import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.DASHIValuation

/-!
# Lean mirror of `DASHI/Arithmetic/ArithmeticIntegerEmbedding.agda` (genuine core)

A minimal concrete integer / valuation carrier over the 15 tracked primes.
`IntCarrier = Nat`, `vp` is the bounded-depth `p`-adic valuation (from
`AgdaMirror.DASHIValuation`), and the lanewise observations `alphaAt`, `betaAt`,
`gammaAt`, `deltaAt` feed the 15-lane carrier `Vec15`.

This mirrors the carrier-level arithmetic faithfully and concretely.  The Agda
module also exposes bridges into the `NormalizeAddState` pressure tower, whose
key step (`primeIndexedPressure-factor`) is an Agda `postulate`; those bridges
are intentionally **not** transcribed here, so that everything below is a fully
proved, axiom-clean carrier theory.
-/

namespace AgdaMirror.ArithmeticIntegerEmbedding

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.DASHIValuation
open SSP

/-- The concrete integer carrier. -/
abbrev IntCarrier : Type := Nat

/-- Addition on the carrier. -/
def add : IntCarrier → IntCarrier → IntCarrier := (· + ·)

/-- Fuel budget for the bounded valuation. -/
def valuationFuel : Nat := 8

/-- The bounded-depth valuation used by the embedding. -/
def vp (p n : Nat) : Nat := vpDepth valuationFuel p n

/-- Build a `Vec15` from a function on the 15 primes, in prime order. -/
def mapPrimes15 (f : SSP → Nat) : Vec15 Nat :=
  ⟨f p2, f p3, f p5, f p7, f p11, f p13, f p17, f p19, f p23, f p29,
   f p31, f p41, f p47, f p59, f p71⟩

/-- Valuation of `x` at lane `p`. -/
def alphaAt (p : SSP) (x _y : IntCarrier) : Nat := vp (toNat p) x

/-- Valuation of `y` at lane `p`. -/
def betaAt (p : SSP) (_x y : IntCarrier) : Nat := vp (toNat p) y

/-- Valuation of `x + y` at lane `p`. -/
def gammaAt (p : SSP) (x y : IntCarrier) : Nat := vp (toNat p) (add x y)

/-- Local cancellation lift: `gamma − min(alpha, beta)`. -/
def deltaAt (p : SSP) (x y : IntCarrier) : Nat :=
  gammaAt p x y - minNat (alphaAt p x y) (betaAt p x y)

/-- The 15-lane alpha vector. -/
def alpha15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => alphaAt p x y)
/-- The 15-lane beta vector. -/
def beta15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => betaAt p x y)
/-- The 15-lane gamma vector. -/
def gamma15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => gammaAt p x y)
/-- The 15-lane delta vector. -/
def delta15 (x y : IntCarrier) : Vec15 Nat := mapPrimes15 (fun p => deltaAt p x y)

/-- Total alpha mass. -/
def alphaSum (x y : IntCarrier) : Nat := sum (alpha15 x y)
/-- Total beta mass. -/
def betaSum (x y : IntCarrier) : Nat := sum (beta15 x y)
/-- Total gamma mass. -/
def gammaSum (x y : IntCarrier) : Nat := sum (gamma15 x y)
/-- Total delta mass. -/
def deltaSum (x y : IntCarrier) : Nat := sum (delta15 x y)

/-- Total tracked pressure (mirror of `GlobalPressure.totalPressure`). -/
def totalPressure (x y : IntCarrier) : Nat := sum (delta15 x y)

/-- The decomposition is definitional. -/
theorem deltaAt_decomposition (p : SSP) (x y : IntCarrier) :
    deltaAt p x y = gammaAt p x y - minNat (alphaAt p x y) (betaAt p x y) := rfl

/-- `totalPressure` equals the delta mass. -/
theorem totalPressure_eq_deltaSum (x y : IntCarrier) : totalPressure x y = deltaSum x y := rfl

/-! ### Generic monotonicity of the 15-lane sum (Agda's `sum15≤`) -/

/-- Componentwise monotonicity of `sum` over the 15-lane carrier. -/
theorem sum_mono {u v : Vec15 Nat}
    (h2 : u.e2 ≤ v.e2) (h3 : u.e3 ≤ v.e3) (h5 : u.e5 ≤ v.e5) (h7 : u.e7 ≤ v.e7)
    (h11 : u.e11 ≤ v.e11) (h13 : u.e13 ≤ v.e13) (h17 : u.e17 ≤ v.e17)
    (h19 : u.e19 ≤ v.e19) (h23 : u.e23 ≤ v.e23) (h29 : u.e29 ≤ v.e29)
    (h31 : u.e31 ≤ v.e31) (h41 : u.e41 ≤ v.e41) (h47 : u.e47 ≤ v.e47)
    (h59 : u.e59 ≤ v.e59) (h71 : u.e71 ≤ v.e71) :
    sum u ≤ sum v := by
  simp only [sum]; omega

/-- Monotonicity of the 15-prime sum built from a function on the primes. -/
theorem sum_mapPrimes15_mono {f g : SSP → Nat} (h : ∀ p, f p ≤ g p) :
    sum (mapPrimes15 f) ≤ sum (mapPrimes15 g) := by
  simp only [mapPrimes15, sum]
  have := h p2; have := h p3; have := h p5; have := h p7; have := h p11
  have := h p13; have := h p17; have := h p19; have := h p23; have := h p29
  have := h p31; have := h p41; have := h p47; have := h p59; have := h p71
  omega

end AgdaMirror.ArithmeticIntegerEmbedding
