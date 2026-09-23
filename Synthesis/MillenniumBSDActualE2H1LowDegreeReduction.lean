import Synthesis.MillenniumBSDActualE2H1SameObject
import Synthesis.MillenniumBSDQuadraticKummerPair
import Mathlib.Tactic

/-!
# BA4: reduce the remaining H¹ theorem to the canonical low-degree statement

The previous boundary asked directly for

  H¹_cont(G_Q,(C₂)^2_triv) ≃ Hom_cont(G_Q,C₂) × Hom_cont(G_Q,C₂).

The product decomposition on the right is not cohomological mathematics: a
continuous homomorphism into the product `(C₂)^2` is literally the same thing
as a pair of continuous quadratic characters.  This file pays that product
decomposition and leaves exactly the textbook low-degree theorem

  H¹_cont(G,A_triv) ≃ Hom_cont(G,A)

for the single coefficient object `A = (C₂)^2`.
-/

namespace Synthesis.Millennium.BSD

/-- Continuous characters with values in the literal two-torsion carrier. -/
abbrev CMTwoTorsionContinuousCharacter :=
  RationalAbsoluteGalois →ₜ* Multiplicative CMTwoTorsionCarrier

noncomputable def cmTwoTorsionCharacterFst
    (χ : CMTwoTorsionContinuousCharacter) :
    RationalQuadraticCharacter where
  toFun σ := Multiplicative.ofAdd (Multiplicative.toAdd (χ σ)).1
  map_one' := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd χ.map_one
    exact congrArg Prod.fst h
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd (χ.map_mul σ τ)
    exact congrArg Prod.fst h
  continuous_toFun := by
    change Continuous (fun σ => (Multiplicative.toAdd (χ σ)).1)
    exact continuous_fst.comp χ.continuous_toFun

noncomputable def cmTwoTorsionCharacterSnd
    (χ : CMTwoTorsionContinuousCharacter) :
    RationalQuadraticCharacter where
  toFun σ := Multiplicative.ofAdd (Multiplicative.toAdd (χ σ)).2
  map_one' := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd χ.map_one
    exact congrArg Prod.snd h
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd (χ.map_mul σ τ)
    exact congrArg Prod.snd h
  continuous_toFun := by
    change Continuous (fun σ => (Multiplicative.toAdd (χ σ)).2)
    exact continuous_snd.comp χ.continuous_toFun

noncomputable def quadraticCharacterPairToTwoTorsion
    (χ : RationalQuadraticCharacter × RationalQuadraticCharacter) :
    CMTwoTorsionContinuousCharacter where
  toFun σ :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd (χ.1 σ), Multiplicative.toAdd (χ.2 σ))
  map_one' := by
    apply Multiplicative.toAdd_injective
    ext <;> simp
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    ext <;> simp
  continuous_toFun := by
    change Continuous (fun σ =>
      (Multiplicative.toAdd (χ.1 σ), Multiplicative.toAdd (χ.2 σ)))
    exact χ.1.continuous_toFun.prod_mk χ.2.continuous_toFun

/-- Product-valued continuous characters are exactly pairs of the scalar
quadratic characters already used by the Kummer lane. -/
noncomputable def cmTwoTorsionContinuousCharacterEquivPair :
    CMTwoTorsionContinuousCharacter ≃
      (RationalQuadraticCharacter × RationalQuadraticCharacter) where
  toFun χ := (cmTwoTorsionCharacterFst χ, cmTwoTorsionCharacterSnd χ)
  invFun := quadraticCharacterPairToTwoTorsion
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro σ
    apply Multiplicative.toAdd_injective
    ext <;> rfl
  right_inv χ := by
    rcases χ with ⟨χ₁,χ₂⟩
    apply Prod.ext
    · apply ContinuousMonoidHom.ext
      intro σ
      apply Multiplicative.toAdd_injective
      rfl
    · apply ContinuousMonoidHom.ext
      intro σ
      apply Multiplicative.toAdd_injective
      rfl

/-- Canonical remaining low-degree theorem: for this literal trivial
coefficient module, continuous H¹ is continuous homomorphisms into the
underlying additive group. -/
def TrivialE2H1ContinuousHomProducer : Prop :=
  Nonempty
    ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
      CMTwoTorsionContinuousCharacter)

/-- The canonical low-degree theorem immediately supplies the older
pair-of-quadratic-characters boundary. -/
noncomputable theorem trivialE2H1QuadraticCharacterPairProducer_of_continuousHom
    (h : TrivialE2H1ContinuousHomProducer) :
    Nonempty
      ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
        (RationalQuadraticCharacter × RationalQuadraticCharacter)) := by
  rcases h with ⟨e⟩
  exact ⟨e.trans cmTwoTorsionContinuousCharacterEquivPair⟩

end Synthesis.Millennium.BSD
