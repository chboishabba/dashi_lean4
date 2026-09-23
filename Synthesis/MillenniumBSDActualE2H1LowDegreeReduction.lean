import Synthesis.MillenniumBSDActualE2H1SameObject
import Synthesis.MillenniumBSDQuadraticKummerPair
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.CompactOpen
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

open CategoryTheory ContRepresentation
open ContinuousCohomology TopRep

/-- Literal kernel model for continuous homogeneous 1-cocycles. -/
noncomputable abbrev CMTwoTorsionContinuousOneCocycle :=
  ↧(((TopRep.homogeneousCochains cmTwoTorsionRepresentation).d 1 2).hom.ker)

/-- Homogeneous 1-cocycle relation, extracted directly from the continuous
cochain differential. -/
theorem cmContinuousOneCocycle_relation
    (σ : CMTwoTorsionContinuousOneCocycle)
    (x y z : RationalAbsoluteGalois) :
    σ.1.1 y z = σ.1.1 x z - σ.1.1 x y := by
  have hσ := σ.2
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, TopRep.homogeneousCochains.d_apply] at hσ
  replace hσ :=
    DFunLike.ext_iff.1
      (DFunLike.ext_iff.1
        (DFunLike.ext_iff.1 hσ x) y) z
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ZeroMemClass.coe_zero] at hσ
  simpa only [sub_eq_zero] using hσ

/-- Homogeneous cochains are diagonally G-invariant; for the literal
two-torsion representation the coefficient action disappears. -/
theorem cmContinuousOneCocycle_leftInvariant
    (σ : CMTwoTorsionContinuousOneCocycle)
    (g x y : RationalAbsoluteGalois) :
    σ.1.1 (g * x) (g * y) = σ.1.1 x y := by
  have hσ := σ.1.2 g
  replace hσ :=
    DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ (g * x)) (g * y)
  simp only [coind₁_apply_apply, cmTwoTorsionRepresentation_action] at hσ
  simpa [mul_assoc] using hσ.symm


/-- Continuous characters with values in the literal two-torsion carrier. -/
abbrev CMTwoTorsionContinuousCharacter :=
  RationalAbsoluteGalois →ₜ* Multiplicative CMTwoTorsionCarrier

/-- Normalize a continuous homogeneous 1-cocycle at its first coordinate.
The cocycle relation plus diagonal invariance makes this a continuous
character. -/
noncomputable def cmContinuousOneCocycleToCharacter
    (σ : CMTwoTorsionContinuousOneCocycle) :
    CMTwoTorsionContinuousCharacter where
  toFun g := Multiplicative.ofAdd (σ.1.1 1 g)
  map_one' := by
    apply Multiplicative.toAdd_injective
    change σ.1.1 1 1 = 0
    have h := cmContinuousOneCocycle_relation σ 1 1 1
    simpa using h
  map_mul' g h := by
    apply Multiplicative.toAdd_injective
    change σ.1.1 1 (g * h) =
      σ.1.1 1 g + σ.1.1 1 h
    have hc := cmContinuousOneCocycle_relation σ 1 g (g * h)
    have hi := cmContinuousOneCocycle_leftInvariant σ g 1 h
    simp only [one_mul] at hi
    rw [hi] at hc
    have hr :
        σ.1.1 1 (g * h) - σ.1.1 1 g =
          σ.1.1 1 h := hc.symm
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hr)
  continuous_toFun := by
    exact (σ.1.1 1).continuous


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
