import Synthesis.MillenniumBSDRationalQuadraticKummerDescent
import Mathlib.Tactic

/-!
# Multiplicative square-class Kummer character

The descended representative map is upgraded to the prize-facing algebraic
object: a multiplicative homomorphism

  Qˣ/(Qˣ)^2 → continuous quadratic characters of G_Q.

This is the scalar Kummer map before passing from continuous characters to
continuous H¹.  No generic cohomology machinery is introduced.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

/-- The sign of a product root is the sum of the two signs in Z/2. -/
theorem rationalKummerBitOfRoot_mul
    {ra rb : AlgebraicClosure ℚ}
    (ha : ∀ σ : RationalAbsoluteGalois, σ ra = ra ∨ σ ra = -ra)
    (hb : ∀ σ : RationalAbsoluteGalois, σ rb = rb ∨ σ rb = -rb)
    (hra : ra ≠ 0) (hrb : rb ≠ 0)
    (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot (ra * rb) σ =
      rationalKummerBitOfRoot ra σ + rationalKummerBitOfRoot rb σ := by
  rcases ha σ with hA | hA <;> rcases hb σ with hB | hB
  · simp [rationalKummerBitOfRoot, map_mul, hA, hB]
  · have hBn : σ rb ≠ rb := by
      rw [hB]
      intro h
      exact hrb (CharZero.neg_eq_self_iff.mp h)
    have hProd : σ (ra * rb) = -(ra * rb) := by
      simp [map_mul, hA, hB]
    have hProdNe : σ (ra * rb) ≠ ra * rb := by
      rw [hProd]
      intro h
      have hz : ra * rb = 0 := CharZero.neg_eq_self_iff.mp h
      exact (mul_ne_zero hra hrb) hz
    simp [rationalKummerBitOfRoot, hA, hBn, hProdNe]
  · have hAn : σ ra ≠ ra := by
      rw [hA]
      intro h
      exact hra (CharZero.neg_eq_self_iff.mp h)
    have hProd : σ (ra * rb) = -(ra * rb) := by
      simp [map_mul, hA, hB]
    have hProdNe : σ (ra * rb) ≠ ra * rb := by
      rw [hProd]
      intro h
      have hz : ra * rb = 0 := CharZero.neg_eq_self_iff.mp h
      exact (mul_ne_zero hra hrb) hz
    simp [rationalKummerBitOfRoot, hAn, hB, hProdNe]
  · have hAn : σ ra ≠ ra := by
      rw [hA]
      intro h
      exact hra (CharZero.neg_eq_self_iff.mp h)
    have hBn : σ rb ≠ rb := by
      rw [hB]
      intro h
      exact hrb (CharZero.neg_eq_self_iff.mp h)
    have hProd : σ (ra * rb) = ra * rb := by
      simp [map_mul, hA, hB]
    simp [rationalKummerBitOfRoot, hAn, hBn, hProd]

theorem rationalQuadraticKummerCharacter_mul
    (a b : NonzeroRat) :
    rationalQuadraticKummerCharacter (nzRatMul a b) =
      rationalQuadraticKummerCharacter a *
        rationalQuadraticKummerCharacter b := by
  let rab : AlgebraicClosure ℚ := rationalKummerRoot a * rationalKummerRoot b
  have hrab :
      rab * rab =
        algebraMap ℚ (AlgebraicClosure ℚ) ((a : ℚ) * (b : ℚ)) := by
    dsimp [rab]
    rw [mul_mul_mul_comm, rationalKummerRoot_spec a, rationalKummerRoot_spec b]
    simp [map_mul]
  have hcanon :
      rationalKummerRoot (nzRatMul a b) * rationalKummerRoot (nzRatMul a b) =
        rab * rab := by
    rw [rationalKummerRoot_spec]
    exact hrab.symm
  ext σ
  apply Multiplicative.toAdd_injective
  change rationalKummerBit (nzRatMul a b) σ =
    rationalKummerBit a σ + rationalKummerBit b σ
  rw [rationalKummerBit_eq_ofRoot, rationalKummerBit_eq_ofRoot,
      rationalKummerBit_eq_ofRoot]
  calc
    rationalKummerBitOfRoot (rationalKummerRoot (nzRatMul a b)) σ
        = rationalKummerBitOfRoot rab σ :=
      rationalKummerBitOfRoot_independent hcanon σ
    _ = rationalKummerBitOfRoot (rationalKummerRoot a) σ +
          rationalKummerBitOfRoot (rationalKummerRoot b) σ := by
      apply rationalKummerBitOfRoot_mul
      · exact fun τ => galois_kummerRoot_eq_or_neg a τ
      · exact fun τ => galois_kummerRoot_eq_or_neg b τ
      · exact rationalKummerRoot_ne_zero a
      · exact rationalKummerRoot_ne_zero b

theorem rationalQuadraticKummerCharacter_one :
    rationalQuadraticKummerCharacter nzRatOne = 1 := by
  have hsquare : SquareRel nzRatOne (nzRatMul nzRatOne nzRatOne) := by
    apply squareRel_of_eq
    apply Subtype.ext
    norm_num [nzRatMul,nzRatOne]
  have hmul := rationalQuadraticKummerCharacter_mul nzRatOne nzRatOne
  have heq := rationalQuadraticKummerCharacter_respects_squareRel hsquare
  rw [heq] at hmul
  exact idempotent_iff_eq_one.mp hmul

/-- The scalar continuous Kummer map on the repo square-class quotient. -/
noncomputable def ratSquareClassKummerHom :
    RatSquareClass →*
      (RationalAbsoluteGalois →ₜ* RationalQuadraticSign) where
  toFun := ratSquareClassKummerCharacter
  map_one' := by
    change rationalQuadraticKummerCharacter nzRatOne = 1
    exact rationalQuadraticKummerCharacter_one
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    exact rationalQuadraticKummerCharacter_mul a b

/-- The same homomorphism on mathlib's canonical Qˣ/(Qˣ)^2 carrier. -/
noncomputable def rationalSquareClassKummerHom :
    MathlibRatSquareClass →*
      (RationalAbsoluteGalois →ₜ* RationalQuadraticSign) :=
  ratSquareClassKummerHom.comp mathlibSquareClassToRat

@[simp] theorem rationalSquareClassKummerHom_mk (a : NonzeroRat) :
    rationalSquareClassKummerHom (mathlibSquareClassOf a) =
      rationalQuadraticKummerCharacter a := by
  simp [rationalSquareClassKummerHom, ratSquareClassKummerHom]

/--
The remaining scalar BA4 theorem is now exactly bijectivity after identifying
continuous quadratic characters with continuous H¹ of the trivial μ₂ module.
-/
def RationalQuadraticKummerCharacterBijection : Prop :=
  Function.Bijective rationalSquareClassKummerHom

end Synthesis.Millennium.BSD
