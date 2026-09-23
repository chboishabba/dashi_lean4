import Synthesis.MillenniumBSDActualE2H1SameObject
import Synthesis.MillenniumBSDQuadraticKummerPair
import Synthesis.MillenniumBSDTrivialTwoTorsionH1Generic
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.Group.Equiv.TypeTags
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

/-- A degree-zero homogeneous cochain for the literal trivial
two-torsion representation is constant. -/
theorem cmHomogeneousZeroCochain_eq_at_one
    (σ : (TopRep.homogeneousCochains cmTwoTorsionRepresentation).X 0)
    (g : RationalAbsoluteGalois) :
    σ.1 g = σ.1 1 := by
  have hσ := DFunLike.ext_iff.1 (σ.2 g) g
  simp only [coind₁_apply_apply, cmTwoTorsionRepresentation_action] at hσ
  simpa using hσ.symm

/-- For the trivial coefficient action the incoming differential to degree
one vanishes, so degree-one coboundaries are zero. -/
theorem cmHomogeneousCochains_d_zero_one :
    (TopRep.homogeneousCochains cmTwoTorsionRepresentation).d 0 1 = 0 := by
  ext σ
  apply Subtype.ext
  ext x y
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ZeroMemClass.coe_zero]
  rw [cmHomogeneousZeroCochain_eq_at_one σ x,
    cmHomogeneousZeroCochain_eq_at_one σ y]
  simp

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


/-- Jointly continuous homogeneous cochain attached to a continuous
character: σχ(x,y)=χ(x⁻¹y). -/
noncomputable def cmCharacterHomogeneousRaw
    (χ : CMTwoTorsionContinuousCharacter) :
    C(RationalAbsoluteGalois × RationalAbsoluteGalois,
      CMTwoTorsionCarrier) where
  toFun p := Multiplicative.toAdd (χ (p.1⁻¹ * p.2))
  continuous_toFun := by
    change Continuous (fun p : RationalAbsoluteGalois × RationalAbsoluteGalois =>
      Multiplicative.toAdd (χ (p.1⁻¹ * p.2)))
    exact χ.continuous_toFun.comp
      (continuous_fst.inv.mul continuous_snd)

noncomputable def cmCharacterHomogeneousCochain
    (χ : CMTwoTorsionContinuousCharacter) :
    C(RationalAbsoluteGalois,
      C(RationalAbsoluteGalois, CMTwoTorsionCarrier)) :=
  (cmCharacterHomogeneousRaw χ).curry

@[simp] theorem cmCharacterHomogeneousCochain_apply
    (χ : CMTwoTorsionContinuousCharacter)
    (x y : RationalAbsoluteGalois) :
    cmCharacterHomogeneousCochain χ x y =
      Multiplicative.toAdd (χ (x⁻¹ * y)) := rfl

theorem cmCharacterHomogeneousCochain_invariant
    (χ : CMTwoTorsionContinuousCharacter) :
    cmCharacterHomogeneousCochain χ ∈
      ((TopRep.resolution' cmTwoTorsionRepresentation).X 1).ρ.invariants := by
  intro g
  ext x y
  simp only [coind₁_apply_apply, cmTwoTorsionRepresentation_action,
    cmCharacterHomogeneousCochain_apply]
  congr 2
  group

theorem cmCharacterHomogeneousRaw_relation
    (χ : CMTwoTorsionContinuousCharacter)
    (x y z : RationalAbsoluteGalois) :
    cmCharacterHomogeneousCochain χ y z =
      cmCharacterHomogeneousCochain χ x z -
        cmCharacterHomogeneousCochain χ x y := by
  have hmul :=
    congrArg Multiplicative.toAdd
      (χ.map_mul (x⁻¹ * y) (y⁻¹ * z))
  have hgroup :
      (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z := by
    group
  rw [hgroup] at hmul
  simp only [map_mul, Multiplicative.toAdd_mul] at hmul
  simp only [cmCharacterHomogeneousCochain_apply]
  rw [← sub_eq_iff_eq_add]
  simpa [add_comm] using hmul.symm

/-- A continuous character produces a literal element of the homogeneous
one-cocycle kernel. -/
noncomputable def cmCharacterToContinuousOneCocycle
    (χ : CMTwoTorsionContinuousCharacter) :
    CMTwoTorsionContinuousOneCocycle := by
  let σ :
      (TopRep.homogeneousCochains cmTwoTorsionRepresentation).X 1 :=
    ⟨cmCharacterHomogeneousCochain χ,
      cmCharacterHomogeneousCochain_invariant χ⟩
  refine ⟨σ, ?_⟩
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  ext x y z
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ZeroMemClass.coe_zero]
  change cmCharacterHomogeneousCochain χ y z -
      (cmCharacterHomogeneousCochain χ x z -
        cmCharacterHomogeneousCochain χ x y) = 0
  rw [cmCharacterHomogeneousRaw_relation]
  abel

theorem cmContinuousOneCocycleToCharacter_leftInverse
    (χ : CMTwoTorsionContinuousCharacter) :
    cmContinuousOneCocycleToCharacter
      (cmCharacterToContinuousOneCocycle χ) = χ := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Multiplicative.toAdd_injective
  simp [cmContinuousOneCocycleToCharacter,
    cmCharacterToContinuousOneCocycle,
    cmCharacterHomogeneousCochain]

theorem cmContinuousOneCocycleToCharacter_rightInverse
    (σ : CMTwoTorsionContinuousOneCocycle) :
    cmCharacterToContinuousOneCocycle
      (cmContinuousOneCocycleToCharacter σ) = σ := by
  apply Subtype.ext
  apply Subtype.ext
  ext x y
  change σ.1.1 1 (x⁻¹ * y) = σ.1.1 x y
  have h := cmContinuousOneCocycle_leftInvariant σ x 1 (x⁻¹ * y)
  simpa using h

/-- Concrete low-degree equivalence before quotienting by coboundaries. -/
noncomputable def cmContinuousOneCocycleEquivCharacter :
    CMTwoTorsionContinuousOneCocycle ≃
      CMTwoTorsionContinuousCharacter where
  toFun := cmContinuousOneCocycleToCharacter
  invFun := cmCharacterToContinuousOneCocycle
  left_inv := cmContinuousOneCocycleToCharacter_rightInverse
  right_inv := cmContinuousOneCocycleToCharacter_leftInverse

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

/-- Multiplicative strengthening of the cocycle/character normalization.
The additive law on cocycles is exactly pointwise multiplication of the
corresponding multiplicative characters. -/
noncomputable def cmContinuousOneCocycleMulEquivCharacter :
    Multiplicative CMTwoTorsionContinuousOneCocycle ≃*
      CMTwoTorsionContinuousCharacter where
  toFun σ := cmContinuousOneCocycleToCharacter σ.toAdd
  invFun χ := Multiplicative.ofAdd (cmCharacterToContinuousOneCocycle χ)
  left_inv σ := by
    apply Multiplicative.toAdd_injective
    exact cmContinuousOneCocycleToCharacter_rightInverse σ.toAdd
  right_inv χ :=
    cmContinuousOneCocycleToCharacter_leftInverse χ
  map_mul' σ τ := by
    apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd_injective
    rfl

/-- Product-valued characters split multiplicatively into their two scalar
quadratic-character coordinates. -/
noncomputable def cmTwoTorsionContinuousCharacterMulEquivPair :
    CMTwoTorsionContinuousCharacter ≃*
      (RationalQuadraticCharacter × RationalQuadraticCharacter) where
  toEquiv := cmTwoTorsionContinuousCharacterEquivPair
  map_mul' χ ψ := by
    apply Prod.ext
    · apply ContinuousMonoidHom.ext
      intro g
      apply Multiplicative.toAdd_injective
      rfl
    · apply ContinuousMonoidHom.ext
      intro g
      apply Multiplicative.toAdd_injective
      rfl

/-- The categorical cycles object in degree one is the literal kernel used
above. -/
noncomputable abbrev cmContinuousCocyclesOneIso :
    ContinuousCohomology.cocycles cmTwoTorsionRepresentation 1 ≅
      CMTwoTorsionContinuousOneCocycle :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((TopRep.homogeneousCochains cmTwoTorsionRepresentation).cyclesIsKernel
      1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

/-- Since the incoming differential is zero, degree-one continuous cohomology
is literally the degree-one cycles object. -/
noncomputable def cmContinuousH1IsoCocyclesOne :
    continuousCohomology 1 cmTwoTorsionRepresentation ≅
      ContinuousCohomology.cocycles cmTwoTorsionRepresentation 1 :=
  (HomologicalComplex.isoHomologyπ
    (TopRep.homogeneousCochains cmTwoTorsionRepresentation)
    0 1 (CochainComplex.prev_nat_succ 0)
    cmHomogeneousCochains_d_zero_one).symm

/-- Every literal continuous degree-one cocycle with values in (C₂)²
has exponent two, pointwise. -/
theorem cmContinuousOneCocycle_exponent_two
    (σ : CMTwoTorsionContinuousOneCocycle) :
    (2 : ℕ) • σ = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  ext x y
  exact cmTwoTorsion_exponent_two (σ.1.1 x y)

/-- Consequently continuous H¹ for the literal trivial E[2] module is
itself killed by two. -/
theorem cmTwoTorsionContinuousH1_exponent_two
    (x : continuousCohomology 1 cmTwoTorsionRepresentation) :
    (2 : ℕ) • x = 0 := by
  apply cmContinuousH1IsoCocyclesOne.toContinuousLinearEquiv.injective
  simp only [map_nsmul, map_zero]
  apply cmContinuousCocyclesOneIso.toContinuousLinearEquiv.injective
  simp only [map_nsmul, map_zero]
  exact cmContinuousOneCocycle_exponent_two _

/-- Transporting across the actual-E[2] same-object isomorphism preserves the
exponent-two property. -/
theorem cmActualE2ContinuousH1_exponent_two
    (x : continuousCohomology 1 cmActualE2Representation) :
    (2 : ℕ) • x = 0 := by
  apply cmActualE2H1IsoTrivial.toContinuousLinearEquiv.injective
  simp only [map_nsmul, map_zero]
  exact cmTwoTorsionContinuousH1_exponent_two _

/-- Additive low-degree equivalence from continuous H¹ to the literal
homogeneous one-cocycle kernel. -/
noncomputable def cmContinuousH1AddEquivOneCocycle :
    continuousCohomology 1 cmTwoTorsionRepresentation ≃+
      CMTwoTorsionContinuousOneCocycle :=
  cmContinuousH1IsoCocyclesOne.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv.trans
    cmContinuousCocyclesOneIso.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv

/-- Multiplicative form of the full low-degree H¹/character theorem. -/
noncomputable def cmTrivialE2H1ContinuousHomMulEquiv :
    Multiplicative (continuousCohomology 1 cmTwoTorsionRepresentation) ≃*
      CMTwoTorsionContinuousCharacter :=
  (AddEquiv.toMultiplicative cmContinuousH1AddEquivOneCocycle).trans
    cmContinuousOneCocycleMulEquivCharacter

/-- Full continuous low-degree theorem for the literal trivial two-torsion
coefficient object. -/
noncomputable def cmTrivialE2H1ContinuousHomEquiv :
    (continuousCohomology 1 cmTwoTorsionRepresentation) ≃
      CMTwoTorsionContinuousCharacter :=
  cmContinuousH1IsoCocyclesOne.toContinuousLinearEquiv.toEquiv.trans
    (cmContinuousCocyclesOneIso.toContinuousLinearEquiv.toEquiv.trans
      cmContinuousOneCocycleEquivCharacter)

/-- Canonical remaining low-degree theorem: for this literal trivial
coefficient module, continuous H¹ is continuous homomorphisms into the
underlying additive group. -/
def TrivialE2H1ContinuousHomProducer : Prop :=
  Nonempty
    ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
      CMTwoTorsionContinuousCharacter)

/-- The continuous trivial-action H¹ theorem is paid internally for the
literal E[2] coefficient object. -/
theorem trivialE2H1ContinuousHomProducer_paid :
    TrivialE2H1ContinuousHomProducer :=
  ⟨cmTrivialE2H1ContinuousHomEquiv⟩


/-- The older pair-of-quadratic-characters boundary is now paid. -/
noncomputable theorem trivialE2H1QuadraticCharacterPairProducer_paid :
    Nonempty
      ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
        (RationalQuadraticCharacter × RationalQuadraticCharacter)) :=
  trivialE2H1QuadraticCharacterPairProducer_of_continuousHom
    trivialE2H1ContinuousHomProducer_paid

/-- The global rational quadratic continuous Kummer boundary is therefore
paid by composing the continuous H¹ theorem with the already-paid scalar
quadratic Kummer equivalence. -/
noncomputable theorem rationalQuadraticContinuousKummerProducer_paid :
    RationalQuadraticContinuousKummerProducer := by
  refine ⟨?_⟩
  exact cmTrivialE2H1ContinuousHomEquiv.trans
    (cmTwoTorsionContinuousCharacterEquivPair.trans
      quadraticCharacterPairEquivRatSquareClasses)

/-- The specialized and generic low-degree normalizations agree at the
literal two-torsion character level.  Both are the canonical homogeneous
one-cocycle normalization σ ↦ (g ↦ σ(1,g)). -/
theorem cmGenericTrivialE2H1Character_coherence
    (x : continuousCohomology 1 cmTwoTorsionRepresentation) :
    cmTrivialE2H1ContinuousHomMulEquiv (Multiplicative.ofAdd x)
      =
    genericTrivialTwoTorsionH1CharacterMulEquiv RationalAbsoluteGalois
      (Multiplicative.ofAdd x) := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Multiplicative.toAdd_injective
  rfl

/-- The specialized and generic decompositions of a two-torsion-valued
character into its two scalar quadratic characters are the same. -/
theorem cmGenericTwoTorsionCharacterPair_coherence
    (χ : CMTwoTorsionContinuousCharacter) :
    cmTwoTorsionContinuousCharacterMulEquivPair χ
      =
    genericTwoTorsionCharacterMulEquivPair RationalAbsoluteGalois χ := by
  apply Prod.ext
  · apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd_injective
    rfl
  · apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd_injective
    rfl

/-- Consequently the specialized and field-generic rational H¹-to-square-
class comparisons agree pointwise. -/
theorem cmGenericTrivialE2H1SquareClass_coherence
    (x : continuousCohomology 1 cmTwoTorsionRepresentation) :
    (cmTrivialE2H1ContinuousHomMulEquiv.trans
      (cmTwoTorsionContinuousCharacterMulEquivPair.trans
        quadraticCharacterPairMulEquivRatSquareClasses))
      (Multiplicative.ofAdd x)
      =
    ((absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv ℚ).trans
      quadraticCharacterPairMulEquivRatSquareClasses)
      (Multiplicative.ofAdd x) := by
  change
    quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmTrivialE2H1ContinuousHomMulEquiv (Multiplicative.ofAdd x)))
      =
    quadraticCharacterPairMulEquivRatSquareClasses
      (genericTwoTorsionCharacterMulEquivPair RationalAbsoluteGalois
        (genericTrivialTwoTorsionH1CharacterMulEquiv RationalAbsoluteGalois
          (Multiplicative.ofAdd x)))
  rw [cmGenericTrivialE2H1Character_coherence x,
    cmGenericTwoTorsionCharacterPair_coherence]

/-- The actual geometric E[2] H¹ comparison with the literal square-class
pair, retaining the full group law. -/
noncomputable def cmActualE2H1MulEquivRatSquareClasses_paid :
    Multiplicative (continuousCohomology 1 cmActualE2Representation) ≃*
      (RatSquareClass × RatSquareClass) :=
  (AddEquiv.toMultiplicative
      cmActualE2H1IsoTrivial.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv).trans
    (cmTrivialE2H1ContinuousHomMulEquiv.trans
      (cmTwoTorsionContinuousCharacterMulEquivPair.trans
        quadraticCharacterPairMulEquivRatSquareClasses))

/-- The actual geometric E[2] H¹ is now identified with the literal
square-class pair used by the explicit descent lane. -/
noncomputable def cmActualE2H1EquivRatSquareClasses_paid :
    (continuousCohomology 1 cmActualE2Representation) ≃
      (RatSquareClass × RatSquareClass) :=
  cmActualE2H1EquivRatSquareClasses
    rationalQuadraticContinuousKummerProducer_paid

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
