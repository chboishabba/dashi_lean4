import Synthesis.MillenniumBSDRationalQuadraticKummerCharacter
import Mathlib.Tactic

/-!
# Descend the continuous quadratic Kummer character to rational square classes

The fixed-representative character used a chosen algebraic square root.
This file pays exactly the representative-invariance needed for BSD:

* changing the chosen square root does not change the Galois sign;
* multiplying the rational representative by a nonzero rational square does
  not change the character;
* therefore the existing continuous character descends to the literal
  `RatSquareClass`, and via the already-proved same-object equivalence to
  mathlib's `Qˣ/(Qˣ)^2`.

No general Kummer/Hilbert-90 machinery is introduced here.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

noncomputable def rationalKummerBitOfRoot
    (r : AlgebraicClosure ℚ) (σ : RationalAbsoluteGalois) : ZMod 2 :=
  if σ r = r then 0 else 1

@[simp] theorem rationalKummerBitOfRoot_neg
    (r : AlgebraicClosure ℚ) (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot (-r) σ = rationalKummerBitOfRoot r σ := by
  simp [rationalKummerBitOfRoot]

theorem rationalKummerBit_eq_ofRoot
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    rationalKummerBit a σ =
      rationalKummerBitOfRoot (rationalKummerRoot a) σ := by
  rfl

/-- Any two square roots of the same element give the same sign bit. -/
theorem rationalKummerBitOfRoot_independent
    {r r' : AlgebraicClosure ℚ}
    (hr : r * r = r' * r')
    (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot r σ = rationalKummerBitOfRoot r' σ := by
  rcases (mul_self_eq_mul_self_iff.mp hr) with h | h
  · subst r'
    rfl
  · have hr' : r' = -r := by
      simpa [eq_comm] using h.symm
    subst r'
    exact (rationalKummerBitOfRoot_neg r σ).symm

/-- Scaling a root by a nonzero rational leaves its Galois sign unchanged. -/
theorem rationalKummerBitOfRoot_rat_smul
    (q : ℚ) (hq : q ≠ 0)
    (r : AlgebraicClosure ℚ)
    (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot
        (algebraMap ℚ (AlgebraicClosure ℚ) q * r) σ
      = rationalKummerBitOfRoot r σ := by
  unfold rationalKummerBitOfRoot
  have hq' : algebraMap ℚ (AlgebraicClosure ℚ) q ≠ 0 := by
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.ne hq
  simp only [map_mul, AlgEquiv.commutes]
  by_cases h : σ r = r
  · simp [h]
  · have hs :
      algebraMap ℚ (AlgebraicClosure ℚ) q * σ r ≠
        algebraMap ℚ (AlgebraicClosure ℚ) q * r := by
      exact fun heq => h (mul_left_cancel₀ hq' heq)
    simp [h, hs]

/--
`SquareRel a b` says `a*s²=b*t²`; hence `(s/t)√a` is a square root of `b`.
Root-choice invariance and rational-scalar invariance then identify the two
continuous quadratic characters.
-/
theorem rationalQuadraticKummerCharacter_respects_squareRel
    {a b : NonzeroRat} (h : SquareRel a b) :
    rationalQuadraticKummerCharacter a =
      rationalQuadraticKummerCharacter b := by
  rcases h with ⟨s,t,hst⟩
  let q : ℚ := (s : ℚ) / (t : ℚ)
  have hq : q ≠ 0 := div_ne_zero s.property t.property
  let r : AlgebraicClosure ℚ :=
    algebraMap ℚ (AlgebraicClosure ℚ) q * rationalKummerRoot a
  have hrsq : r * r = algebraMap ℚ (AlgebraicClosure ℚ) b.1 := by
    dsimp [r,q]
    rw [rationalKummerRoot_spec a]
    have hm := congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) hst
    push_cast at hm ⊢
    field_simp [s.property,t.property] at hm ⊢
    nlinarith [hm]
  have hroot :
      r * r = rationalKummerRoot b * rationalKummerRoot b := by
    rw [hrsq, rationalKummerRoot_spec b]
  ext σ
  apply Multiplicative.toAdd_injective
  change rationalKummerBit a σ = rationalKummerBit b σ
  rw [rationalKummerBit_eq_ofRoot, rationalKummerBit_eq_ofRoot]
  calc
    rationalKummerBitOfRoot (rationalKummerRoot a) σ
        = rationalKummerBitOfRoot r σ := by
            exact (rationalKummerBitOfRoot_rat_smul
              q hq (rationalKummerRoot a) σ).symm
    _ = rationalKummerBitOfRoot (rationalKummerRoot b) σ :=
      rationalKummerBitOfRoot_independent hroot σ

/-- Character descended to the repo's literal rational square-class quotient. -/
noncomputable def ratSquareClassKummerCharacter :
    RatSquareClass → (RationalAbsoluteGalois →ₜ* RationalQuadraticSign) :=
  Quotient.lift
    rationalQuadraticKummerCharacter
    (fun _ _ h => rationalQuadraticKummerCharacter_respects_squareRel h)

@[simp] theorem ratSquareClassKummerCharacter_mk (a : NonzeroRat) :
    ratSquareClassKummerCharacter (squareClassOf a) =
      rationalQuadraticKummerCharacter a := rfl

/-- Same descended character on mathlib's canonical `Qˣ/(Qˣ)^2`. -/
noncomputable def rationalSquareClassKummerCharacter :
    MathlibRatSquareClass →
      (RationalAbsoluteGalois →ₜ* RationalQuadraticSign) :=
  fun c => ratSquareClassKummerCharacter (mathlibSquareClassToRat c)

@[simp] theorem rationalSquareClassKummerCharacter_mk (a : NonzeroRat) :
    rationalSquareClassKummerCharacter (mathlibSquareClassOf a) =
      rationalQuadraticKummerCharacter a := by
  rw [rationalSquareClassKummerCharacter,
    mathlibSquareClassToRat_leftInverse]
  rfl

theorem rationalQuadraticKummerCharacterDescent_paid :
    RationalQuadraticKummerCharacterDescent := by
  refine ⟨rationalSquareClassKummerCharacter, ?_⟩
  intro a
  exact rationalSquareClassKummerCharacter_mk a

end Synthesis.Millennium.BSD
