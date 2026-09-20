import Synthesis.MillenniumBSDExplicitSelmerIntersection
import Mathlib.Tactic

/-!
# Actual group structures on global and local square classes

The previous BSD files construct the quotient types Q*/Q*² and Q_p*/Q_p*².
For descent exactness these cannot remain bare quotient carriers: they must be
actual abelian groups, and global-to-local localization must be a homomorphism.

This file descends multiplication and inversion through the square relations,
proves the commutative group laws on both quotients, and packages
localization as a multiplicative homomorphism.  Pair-valued Kummer classes
therefore live in an actual abelian group rather than a product of opaque
sets.
-/

namespace Synthesis.Millennium.BSD

def nzRatMul (a b : NonzeroRat) : NonzeroRat :=
  ⟨(a : ℚ) * (b : ℚ), mul_ne_zero a.property b.property⟩

def nzRatInv (a : NonzeroRat) : NonzeroRat :=
  ⟨((a : ℚ)⁻¹), inv_ne_zero a.property⟩

def nzRatOne : NonzeroRat :=
  ⟨1, one_ne_zero⟩

theorem squareRel_of_eq {a b : NonzeroRat} (h : a = b) :
    SquareRel a b := by
  subst b
  exact squareRel_refl a

theorem squareRel_mul
    {a a' b b' : NonzeroRat}
    (ha : SquareRel a a')
    (hb : SquareRel b b') :
    SquareRel (nzRatMul a b) (nzRatMul a' b') := by
  rcases ha with ⟨sa, ta, ha⟩
  rcases hb with ⟨sb, tb, hb⟩
  refine ⟨nzRatMul sa sb, nzRatMul ta tb, ?_⟩
  dsimp [nzRatMul] at *
  calc
    ((a : ℚ) * (b : ℚ)) * (((sa : ℚ) * (sb : ℚ)) ^ 2)
        = ((a : ℚ) * (sa : ℚ) ^ 2) *
            ((b : ℚ) * (sb : ℚ) ^ 2) := by ring
    _ = ((a' : ℚ) * (ta : ℚ) ^ 2) *
          ((b' : ℚ) * (tb : ℚ) ^ 2) := by rw [ha, hb]
    _ = ((a' : ℚ) * (b' : ℚ)) *
          (((ta : ℚ) * (tb : ℚ)) ^ 2) := by ring

theorem squareRel_inv
    {a b : NonzeroRat}
    (h : SquareRel a b) :
    SquareRel (nzRatInv a) (nzRatInv b) := by
  rcases h with ⟨s, t, hst⟩
  refine ⟨t, s, ?_⟩
  dsimp [nzRatInv]
  field_simp [a.property, b.property]
  simpa [mul_comm] using hst.symm

instance ratSquareClassOne : One RatSquareClass where
  one := squareClassOf nzRatOne

instance ratSquareClassMul : Mul RatSquareClass where
  mul :=
    Quotient.map₂ nzRatMul
      (fun _ _ ha _ _ hb => squareRel_mul ha hb)

instance ratSquareClassInv : Inv RatSquareClass where
  inv :=
    Quotient.map nzRatInv
      (fun _ _ h => squareRel_inv h)

@[simp] theorem squareClassOf_mul
    (a b : NonzeroRat) :
    squareClassOf (nzRatMul a b) =
      squareClassOf a * squareClassOf b :=
  rfl

@[simp] theorem squareClassOf_inv
    (a : NonzeroRat) :
    squareClassOf (nzRatInv a) =
      (squareClassOf a)⁻¹ :=
  rfl

instance ratSquareClassCommGroup : CommGroup RatSquareClass where
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    simp [nzRatMul, mul_assoc]
  one_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    simp [nzRatMul, nzRatOne]
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    simp [nzRatMul, nzRatOne]
  inv_mul_cancel := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    simp [nzRatMul, nzRatInv, nzRatOne, a.property]
  mul_comm := by
    rintro ⟨a⟩ ⟨b⟩
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    simp [nzRatMul, mul_comm]

def nzPadicMul
    (p : ℕ) [Fact p.Prime]
    (a b : NonzeroPadic p) :
    NonzeroPadic p :=
  ⟨(a : ℚ_[p]) * (b : ℚ_[p]),
    mul_ne_zero a.property b.property⟩

def nzPadicInv
    (p : ℕ) [Fact p.Prime]
    (a : NonzeroPadic p) :
    NonzeroPadic p :=
  ⟨((a : ℚ_[p])⁻¹), inv_ne_zero a.property⟩

def nzPadicOne
    (p : ℕ) [Fact p.Prime] :
    NonzeroPadic p :=
  ⟨1, one_ne_zero⟩

theorem padicSquareRel_of_eq
    {p : ℕ} [Fact p.Prime]
    {a b : NonzeroPadic p}
    (h : a = b) :
    PadicSquareRel p a b := by
  subst b
  exact padicSquareRel_refl p a

theorem padicSquareRel_mul
    {p : ℕ} [Fact p.Prime]
    {a a' b b' : NonzeroPadic p}
    (ha : PadicSquareRel p a a')
    (hb : PadicSquareRel p b b') :
    PadicSquareRel p
      (nzPadicMul p a b)
      (nzPadicMul p a' b') := by
  rcases ha with ⟨sa, ta, ha⟩
  rcases hb with ⟨sb, tb, hb⟩
  refine ⟨nzPadicMul p sa sb, nzPadicMul p ta tb, ?_⟩
  dsimp [nzPadicMul] at *
  calc
    ((a : ℚ_[p]) * (b : ℚ_[p])) *
        (((sa : ℚ_[p]) * (sb : ℚ_[p])) ^ 2)
        =
      ((a : ℚ_[p]) * (sa : ℚ_[p]) ^ 2) *
        ((b : ℚ_[p]) * (sb : ℚ_[p]) ^ 2) := by ring
    _ =
      ((a' : ℚ_[p]) * (ta : ℚ_[p]) ^ 2) *
        ((b' : ℚ_[p]) * (tb : ℚ_[p]) ^ 2) := by rw [ha, hb]
    _ =
      ((a' : ℚ_[p]) * (b' : ℚ_[p])) *
        (((ta : ℚ_[p]) * (tb : ℚ_[p])) ^ 2) := by ring

theorem padicSquareRel_inv
    {p : ℕ} [Fact p.Prime]
    {a b : NonzeroPadic p}
    (h : PadicSquareRel p a b) :
    PadicSquareRel p
      (nzPadicInv p a)
      (nzPadicInv p b) := by
  rcases h with ⟨s, t, hst⟩
  refine ⟨t, s, ?_⟩
  dsimp [nzPadicInv]
  field_simp [a.property, b.property]
  simpa [mul_comm] using hst.symm

instance padicSquareClassOne
    (p : ℕ) [Fact p.Prime] :
    One (PadicSquareClass p) where
  one := padicSquareClassOf p (nzPadicOne p)

instance padicSquareClassMul
    (p : ℕ) [Fact p.Prime] :
    Mul (PadicSquareClass p) where
  mul :=
    Quotient.map₂ (nzPadicMul p)
      (fun _ _ ha _ _ hb => padicSquareRel_mul ha hb)

instance padicSquareClassInv
    (p : ℕ) [Fact p.Prime] :
    Inv (PadicSquareClass p) where
  inv :=
    Quotient.map (nzPadicInv p)
      (fun _ _ h => padicSquareRel_inv h)

instance padicSquareClassCommGroup
    (p : ℕ) [Fact p.Prime] :
    CommGroup (PadicSquareClass p) where
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    apply Subtype.ext
    simp [nzPadicMul, mul_assoc]
  one_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    apply Subtype.ext
    simp [nzPadicMul, nzPadicOne]
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    apply Subtype.ext
    simp [nzPadicMul, nzPadicOne]
  inv_mul_cancel₀ := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    apply Subtype.ext
    simp [nzPadicMul, nzPadicInv, nzPadicOne, a.property]
  mul_comm := by
    rintro ⟨a⟩ ⟨b⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    apply Subtype.ext
    simp [nzPadicMul, mul_comm]

theorem localizeNonzeroRat_mul
    (p : ℕ) [Fact p.Prime]
    (a b : NonzeroRat) :
    localizeNonzeroRat p (nzRatMul a b) =
      nzPadicMul p
        (localizeNonzeroRat p a)
        (localizeNonzeroRat p b) := by
  apply Subtype.ext
  rfl

def localizeSquareClassHom
    (p : ℕ) [Fact p.Prime] :
    RatSquareClass →* PadicSquareClass p where
  toFun := localizeSquareClass p
  map_one' := by
    rfl
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    apply Quotient.sound
    apply padicSquareRel_of_eq
    exact localizeNonzeroRat_mul p a b

def localizeKummerPairHom
    (p : ℕ) [Fact p.Prime] :
    (RatSquareClass × RatSquareClass) →*
      (PadicSquareClass p × PadicSquareClass p) where
  toFun := localizeKummerPair p
  map_one' := by
    rfl
  map_mul' := by
    intro a b
    apply Prod.ext <;>
      simp [localizeKummerPair, localizeSquareClassHom]

theorem localizeKummerPair_eq_hom
    (p : ℕ) [Fact p.Prime]
    (c : RatSquareClass × RatSquareClass) :
    localizeKummerPair p c =
      localizeKummerPairHom p c :=
  rfl

end Synthesis.Millennium.BSD
