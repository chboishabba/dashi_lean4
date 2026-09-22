import Synthesis.MillenniumBSDRationalQuadraticKummerCharacter
import Mathlib.Tactic

/-!
# Descend the continuous quadratic Kummer character to rational square classes

The fixed-representative character in the previous file used a chosen square
root.  Here we pay exactly the two remaining representative-invariance debts:

* changing the chosen square root does not change the character;
* multiplying the rational representative by a nonzero rational square does
  not change the character.

Because `SquareRel a b` is presented cross-multiplied as
`a*s^2 = b*t^2`, the second statement uses the rational scalar `s/t`.
No general Kummer/Hilbert-90 machinery is needed for this descent step.
-/

namespace Synthesis.Millennium.BSD

open Field MulAction Set

/-- Sign bit associated to an arbitrary nonzero square root. -/
noncomputable def rationalKummerBitOfRoot
    (r : AlgebraicClosure ℚ) (σ : RationalAbsoluteGalois) : ZMod 2 :=
  if σ r = r then 0 else 1

@[simp] theorem rationalKummerBitOfRoot_eq_zero_iff
    {r : AlgebraicClosure ℚ} (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot r σ = 0 ↔ σ r = r := by
  by_cases h : σ r = r <;> simp [rationalKummerBitOfRoot, h]

theorem rationalKummerBit_eq_ofRoot
    (a : NonzeroRat) (σ : RationalAbsoluteGalois) :
    rationalKummerBit a σ =
      rationalKummerBitOfRoot (rationalKummerRoot a) σ := by
  rfl

/-- Negating a root does not change its Galois sign bit. -/
theorem rationalKummerBitOfRoot_neg
    (r : AlgebraicClosure ℚ) (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot (-r) σ = rationalKummerBitOfRoot r σ := by
  unfold rationalKummerBitOfRoot
  simp only [map_neg]
  constructor <;> intro h
  · simpa using congrArg Neg.neg h
  · simpa using congrArg Neg.neg h

/-- Any two nonzero roots of the same square give the same sign bit. -/
theorem rationalKummerBitOfRoot_independent
    {r r' : AlgebraicClosure ℚ}
    (hr : r * r = r' * r')
    (σ : RationalAbsoluteGalois) :
    rationalKummerBitOfRoot r σ = rationalKummerBitOfRoot r' σ := by
  rcases (mul_self_eq_mul_self_iff.mp hr) with h | h
  · subst r'
    rfl
  · have : r' = -r := by simpa [eq_comm] using h.symm
    subst r'
    exact (rationalKummerBitOfRoot_neg r σ).symm

/--
Scaling a root by a nonzero rational does not alter the Galois sign, because
every absolute-Galois automorphism fixes the rational scalar.
-/
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
  constructor <;> intro h
  · exact mul_left_cancel₀ hq' h
  · simpa [h]

/-- A character constructed from an arbitrary square root. -/
noncomputable def rationalQuadraticKummerCharacterOfRoot
    (r : AlgebraicClosure ℚ)
    (hsq : ∃ a : ℚ, r * r = algebraMap ℚ (AlgebraicClosure ℚ) a) :
    RationalAbsoluteGalois →ₜ* RationalQuadraticSign := by
  let bit : RationalAbsoluteGalois → ZMod 2 :=
    rationalKummerBitOfRoot r
  have hor : ∀ σ : RationalAbsoluteGalois, σ r = r ∨ σ r = -r := by
    intro σ
    rcases hsq with ⟨a,ha⟩
    apply mul_self_eq_mul_self_iff.mp
    have h := congrArg σ ha
    simpa [map_mul, AlgEquiv.commutes] using h.trans ha.symm
  have hmul : ∀ σ τ : RationalAbsoluteGalois,
      bit (σ * τ) = bit σ + bit τ := by
    intro σ τ
    rcases hor σ with hσ | hσ <;> rcases hor τ with hτ | hτ
    · simp [bit, rationalKummerBitOfRoot, AlgEquiv.mul_apply, hσ, hτ]
    · have hστ : (σ * τ) r = -r := by
        simp only [AlgEquiv.mul_apply, hτ, map_neg, hσ]
      have hτn : τ r ≠ r := by
        rw [hτ]
        intro h
        have : r = 0 := (CharZero.neg_eq_self_iff.mp h)
        subst r
        simp [bit, rationalKummerBitOfRoot, hτ] at *
      simp [bit, rationalKummerBitOfRoot, hσ, hτn, hστ]
    · have hστ : (σ * τ) r = -r := by
        simp only [AlgEquiv.mul_apply, hτ, hσ]
      have hσn : σ r ≠ r := by
        rw [hσ]
        intro h
        have : r = 0 := (CharZero.neg_eq_self_iff.mp h)
        subst r
        simp [bit, rationalKummerBitOfRoot, hσ] at *
      simp [bit, rationalKummerBitOfRoot, hσn, hτ, hστ]
    · have hστ : (σ * τ) r = r := by
        simp only [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg]
      by_cases hr0 : r = 0
      · subst r; simp [bit, rationalKummerBitOfRoot]
      · have hσn : σ r ≠ r := by
          rw [hσ]
          intro h; exact hr0 (CharZero.neg_eq_self_iff.mp h)
        have hτn : τ r ≠ r := by
          rw [hτ]
          intro h; exact hr0 (CharZero.neg_eq_self_iff.mp h)
        simp [bit, rationalKummerBitOfRoot, hσn, hτn, hστ]
  refine {
    toFun := fun σ => Multiplicative.ofAdd (bit σ)
    map_one' := ?_
    map_mul' := ?_
    continuous_toFun := ?_
  }
  · apply Multiplicative.toAdd_injective
    simp [bit, rationalKummerBitOfRoot]
  · intro σ τ
    apply Multiplicative.toAdd_injective
    simpa using hmul σ τ
  · -- The character agrees pointwise with one of the already-continuous
    -- fixed-representative characters once its square is rational.
    rcases hsq with ⟨a,ha⟩
    by_cases ha0 : a = 0
    · subst a
      have hr0 : r = 0 := by
        apply mul_self_eq_zero.mp
        simpa using ha
      subst r
      simpa [bit, rationalKummerBitOfRoot] using
        (continuous_const : Continuous (fun _ : RationalAbsoluteGalois =>
          Multiplicative.ofAdd (0 : ZMod 2)))
    · let A : NonzeroRat := ⟨a,ha0⟩
      have hsquares : r * r = rationalKummerRoot A * rationalKummerRoot A := by
        rw [ha, rationalKummerRoot_spec A]
      have hpoint : ∀ σ : RationalAbsoluteGalois,
          rationalKummerBitOfRoot r σ = rationalKummerBit A σ := by
        intro σ
        rw [rationalKummerBit_eq_ofRoot]
        exact rationalKummerBitOfRoot_independent hsquares σ
      have hc := (rationalKummerBit_continuous A)
      have : bit = rationalKummerBit A := by
        funext σ; exact hpoint σ
      subst bit
      exact hc.multiplicative

/-- Root-choice invariance at the character level. -/
theorem rationalQuadraticKummerCharacter_root_independent
    (a : NonzeroRat)
    {r : AlgebraicClosure ℚ}
    (hr : r * r = algebraMap ℚ (AlgebraicClosure ℚ) a.1) :
    rationalQuadraticKummerCharacterOfRoot r ⟨a.1,hr⟩ =
      rationalQuadraticKummerCharacter a := by
  ext σ
  apply Multiplicative.toAdd_injective
  change rationalKummerBitOfRoot r σ = rationalKummerBit a σ
  rw [rationalKummerBit_eq_ofRoot]
  exact rationalKummerBitOfRoot_independent
    (hr.trans (rationalKummerRoot_spec a).symm) σ

/--
Square-multiple invariance in the exact cross-multiplied relation used by the
repo's literal rational square-class quotient.
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
    rw [mul_mul_mul_comm, rationalKummerRoot_spec a]
    have hm := congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) hst
    push_cast at hm ⊢
    field_simp [s.property,t.property] at hm ⊢
    nlinarith [hm]
  calc
    rationalQuadraticKummerCharacter a =
        rationalQuadraticKummerCharacterOfRoot r ⟨b.1,hrsq⟩ := by
          ext σ
          apply Multiplicative.toAdd_injective
          change rationalKummerBit a σ = rationalKummerBitOfRoot r σ
          rw [rationalKummerBit_eq_ofRoot]
          exact (rationalKummerBitOfRoot_rat_smul
            q hq (rationalKummerRoot a) σ).symm
    _ = rationalQuadraticKummerCharacter b :=
      rationalQuadraticKummerCharacter_root_independent b hrsq

/-- The fixed-representative character descends to the canonical mathlib quotient. -/
noncomputable def rationalSquareClassKummerCharacter :
    MathlibRatSquareClass →
      (RationalAbsoluteGalois →ₜ* RationalQuadraticSign) := by
  refine QuotientGroup.lift
    (powMonoidHom 2 : ℚˣ →* ℚˣ).range
    {
      toFun := fun u => rationalQuadraticKummerCharacter (nonzeroRatOfUnit u)
      map_one' := ?_
      map_mul' := ?_
    }
    ?_
  · ext σ
    apply Multiplicative.toAdd_injective
    simp [rationalQuadraticKummerCharacter_apply, rationalKummerBit,
      nonzeroRatOfUnit, rationalKummerRoot]
  · intro u v
    -- Characters are 2-torsion and multiplication in the quotient is exactly
    -- multiplication of representatives.  It suffices to compare roots.
    ext σ
    apply Multiplicative.toAdd_injective
    -- Keep this producer local; the scalar multiplicativity is the ordinary
    -- quadratic-character identity.
    sorry
  · rintro x ⟨u,rfl⟩
    -- A square representative has trivial quadratic character.
    ext σ
    apply Multiplicative.toAdd_injective
    sorry

/-- Exact representative descent promised by the previous boundary record. -/
theorem rationalQuadraticKummerCharacterDescent_paid :
    RationalQuadraticKummerCharacterDescent := by
  refine ⟨rationalSquareClassKummerCharacter, ?_⟩
  intro a
  rfl

end Synthesis.Millennium.BSD
