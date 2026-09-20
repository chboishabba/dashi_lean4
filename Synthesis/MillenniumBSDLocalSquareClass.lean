import Synthesis.MillenniumBSDRationalKummerQuotient
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# Literal local square classes and Kummer coordinates over Q_p

For every prime p, construct the actual quotient Q_p^*/Q_p^{*2} and prove that
the rational square-class quotient localizes into it.  The ordinary local
Kummer map for y² = x³ - x is then the pair ([x],[x-1]) in this quotient.

This pays the local square-class carrier and the global-to-local square-class
map.  The Selmer *image condition* still requires the elliptic-curve group law
and the full local Kummer image, including exceptional 2-torsion points.
-/

namespace Synthesis.Millennium.BSD

abbrev NonzeroPadic (p : ℕ) [Fact p.Prime] :=
  {q : ℚ_[p] // q ≠ 0}

def PadicSquareRel
    (p : ℕ) [Fact p.Prime]
    (a b : NonzeroPadic p) : Prop :=
  ∃ s t : NonzeroPadic p,
    (a : ℚ_[p]) * (s : ℚ_[p]) ^ 2 =
      (b : ℚ_[p]) * (t : ℚ_[p]) ^ 2

theorem padicSquareRel_refl
    (p : ℕ) [Fact p.Prime]
    (a : NonzeroPadic p) :
    PadicSquareRel p a a := by
  refine ⟨⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩, ?_⟩
  ring

theorem padicSquareRel_symm
    {p : ℕ} [Fact p.Prime]
    {a b : NonzeroPadic p} :
    PadicSquareRel p a b →
    PadicSquareRel p b a := by
  rintro ⟨s, t, h⟩
  exact ⟨t, s, h.symm⟩

theorem padicSquareRel_trans
    {p : ℕ} [Fact p.Prime]
    {a b c : NonzeroPadic p} :
    PadicSquareRel p a b →
    PadicSquareRel p b c →
    PadicSquareRel p a c := by
  rintro ⟨s₁, t₁, h₁⟩ ⟨s₂, t₂, h₂⟩
  let s : NonzeroPadic p :=
    ⟨(s₁ : ℚ_[p]) * (s₂ : ℚ_[p]), mul_ne_zero s₁.property s₂.property⟩
  let t : NonzeroPadic p :=
    ⟨(t₂ : ℚ_[p]) * (t₁ : ℚ_[p]), mul_ne_zero t₂.property t₁.property⟩
  refine ⟨s, t, ?_⟩
  dsimp [s, t]
  calc
    (a : ℚ_[p]) * ((s₁ : ℚ_[p]) * (s₂ : ℚ_[p])) ^ 2
        = ((a : ℚ_[p]) * (s₁ : ℚ_[p]) ^ 2) * (s₂ : ℚ_[p]) ^ 2 := by ring
    _ = ((b : ℚ_[p]) * (t₁ : ℚ_[p]) ^ 2) * (s₂ : ℚ_[p]) ^ 2 := by rw [h₁]
    _ = ((b : ℚ_[p]) * (s₂ : ℚ_[p]) ^ 2) * (t₁ : ℚ_[p]) ^ 2 := by ring
    _ = ((c : ℚ_[p]) * (t₂ : ℚ_[p]) ^ 2) * (t₁ : ℚ_[p]) ^ 2 := by rw [h₂]
    _ = (c : ℚ_[p]) * ((t₂ : ℚ_[p]) * (t₁ : ℚ_[p])) ^ 2 := by ring

def padicSquareSetoid (p : ℕ) [Fact p.Prime] :
    Setoid (NonzeroPadic p) where
  r := PadicSquareRel p
  iseqv :=
    ⟨padicSquareRel_refl p,
      padicSquareRel_symm,
      padicSquareRel_trans⟩

abbrev PadicSquareClass (p : ℕ) [Fact p.Prime] :=
  Quotient (padicSquareSetoid p)

def padicSquareClassOf
    (p : ℕ) [Fact p.Prime]
    (q : NonzeroPadic p) :
    PadicSquareClass p :=
  Quotient.mk (padicSquareSetoid p) q

def localizeNonzeroRat
    (p : ℕ) [Fact p.Prime]
    (q : NonzeroRat) :
    NonzeroPadic p :=
  ⟨(q : ℚ_[p]), Rat.cast_ne_zero.mpr q.property⟩

theorem squareRel_localizes
    {p : ℕ} [Fact p.Prime]
    {a b : NonzeroRat} :
    SquareRel a b →
    PadicSquareRel p
      (localizeNonzeroRat p a)
      (localizeNonzeroRat p b) := by
  rintro ⟨s, t, h⟩
  refine ⟨localizeNonzeroRat p s,
    localizeNonzeroRat p t, ?_⟩
  exact_mod_cast h

def localizeSquareClass
    (p : ℕ) [Fact p.Prime] :
    RatSquareClass → PadicSquareClass p :=
  Quotient.lift
    (fun q => padicSquareClassOf p (localizeNonzeroRat p q))
    (fun _ _ h => Quotient.sound (squareRel_localizes h))

@[simp] theorem localizeSquareClass_mk
    (p : ℕ) [Fact p.Prime]
    (q : NonzeroRat) :
    localizeSquareClass p (squareClassOf q) =
      padicSquareClassOf p (localizeNonzeroRat p q) :=
  rfl

def localizeKummerPair
    (p : ℕ) [Fact p.Prime] :
    RatSquareClass × RatSquareClass →
      PadicSquareClass p × PadicSquareClass p :=
  fun pair =>
    (localizeSquareClass p pair.1,
      localizeSquareClass p pair.2)

structure OrdinaryPadicKummerPoint
    (p : ℕ) [Fact p.Prime] where
  x : ℚ_[p]
  y : ℚ_[p]
  onCurve : y ^ 2 = x ^ 3 - x
  x_ne_zero : x ≠ 0
  x_ne_one : x ≠ 1

def ordinaryPadicKummer
    {p : ℕ} [Fact p.Prime]
    (P : OrdinaryPadicKummerPoint p) :
    PadicSquareClass p × PadicSquareClass p :=
  ( padicSquareClassOf p ⟨P.x, P.x_ne_zero⟩
  , padicSquareClassOf p
      ⟨P.x - 1, sub_ne_zero.mpr P.x_ne_one⟩ )

def localizeOrdinaryRationalPoint
    (p : ℕ) [Fact p.Prime]
    (P : OrdinaryKummerPoint) :
    OrdinaryPadicKummerPoint p where
  x := P.x
  y := P.y
  onCurve := by exact_mod_cast P.onCurve
  x_ne_zero := Rat.cast_ne_zero.mpr P.x_ne_zero
  x_ne_one := by
    exact sub_ne_zero.mpr
      (by exact_mod_cast P.x_ne_one)

theorem ordinaryKummer_localizes
    (p : ℕ) [Fact p.Prime]
    (P : OrdinaryKummerPoint) :
    localizeKummerPair p (ordinaryKummer P) =
      ordinaryPadicKummer
        (localizeOrdinaryRationalPoint p P) := by
  rfl

end Synthesis.Millennium.BSD
