import Synthesis.MillenniumBSDCMTwoTorsionGaloisModule
import Synthesis.MillenniumBSDRationalQuadraticKummerHom
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic

/-!
# Generic continuous H¹ for the trivial two-torsion module

The global BA4 proof only uses the acting group through its group topology and
compact-open currying.  This file factors that mathematics out of
`G_Q` entirely.

For every locally compact topological group `G`, with the literal
`(Z/2)^2` coefficient object carrying the trivial action, we construct

  H¹_cont(G,(Z/2)^2_triv) ≃ Hom_cont(G,(Z/2)^2),

and retain the additive/multiplicative group law.  This is the
representation-theoretic half of every local quadratic Kummer comparison;
local arithmetic and localization compatibility remain separate.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory ContRepresentation
open ContinuousCohomology TopRep

variable (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The literal `(C₂)^2` module with trivial action by an arbitrary group. -/
noncomputable def genericTwoTorsionRepresentation :
    TopRep ℤ G :=
  TopRep.of
    (ContRepresentation.trivial ℤ G CMTwoTorsionCarrier)

@[simp] theorem genericTwoTorsionRepresentation_action
    (g : G) (x : CMTwoTorsionCarrier) :
    (genericTwoTorsionRepresentation G).ρ g x = x := rfl

/-- Degree-zero invariant homogeneous cochains are constant for the trivial
coefficient action. -/
theorem genericHomogeneousZeroCochain_eq_at_one
    (σ : (TopRep.homogeneousCochains
      (genericTwoTorsionRepresentation G)).X 0)
    (g : G) :
    σ.1 g = σ.1 1 := by
  have hσ := DFunLike.ext_iff.1 (σ.2 g) g
  simp only [coind₁_apply_apply,
    genericTwoTorsionRepresentation_action] at hσ
  simpa using hσ.symm

/-- For trivial coefficients the incoming differential into degree one is
zero. -/
theorem genericHomogeneousCochains_d_zero_one :
    (TopRep.homogeneousCochains
      (genericTwoTorsionRepresentation G)).d 0 1 = 0 := by
  ext σ
  apply Subtype.ext
  ext x y
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ZeroMemClass.coe_zero]
  rw [genericHomogeneousZeroCochain_eq_at_one G σ x,
    genericHomogeneousZeroCochain_eq_at_one G σ y]
  simp

/-- Literal kernel model for homogeneous continuous one-cocycles. -/
noncomputable abbrev GenericTwoTorsionContinuousOneCocycle :=
  ↧(((TopRep.homogeneousCochains
    (genericTwoTorsionRepresentation G)).d 1 2).hom.ker)

theorem genericContinuousOneCocycle_relation
    (σ : GenericTwoTorsionContinuousOneCocycle G)
    (x y z : G) :
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

theorem genericContinuousOneCocycle_leftInvariant
    (σ : GenericTwoTorsionContinuousOneCocycle G)
    (g x y : G) :
    σ.1.1 (g * x) (g * y) = σ.1.1 x y := by
  have hσ := σ.1.2 g
  replace hσ :=
    DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ (g * x)) (g * y)
  simp only [coind₁_apply_apply,
    genericTwoTorsionRepresentation_action] at hσ
  simpa [mul_assoc] using hσ.symm

/-- Continuous characters into the literal two-torsion carrier. -/
abbrev GenericTwoTorsionContinuousCharacter :=
  G →ₜ* Multiplicative CMTwoTorsionCarrier

noncomputable def genericContinuousOneCocycleToCharacter
    (σ : GenericTwoTorsionContinuousOneCocycle G) :
    GenericTwoTorsionContinuousCharacter G where
  toFun g := Multiplicative.ofAdd (σ.1.1 1 g)
  map_one' := by
    apply Multiplicative.toAdd_injective
    change σ.1.1 1 1 = 0
    have h := genericContinuousOneCocycle_relation G σ 1 1 1
    simpa using h
  map_mul' g h := by
    apply Multiplicative.toAdd_injective
    change σ.1.1 1 (g * h) =
      σ.1.1 1 g + σ.1.1 1 h
    have hc := genericContinuousOneCocycle_relation G σ 1 g (g * h)
    have hi := genericContinuousOneCocycle_leftInvariant G σ g 1 h
    simp only [one_mul] at hi
    rw [hi] at hc
    have hr :
        σ.1.1 1 (g * h) - σ.1.1 1 g =
          σ.1.1 1 h := hc.symm
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hr)
  continuous_toFun := (σ.1.1 1).continuous

/-- Jointly continuous cochain attached to a character:
`σχ(x,y)=χ(x⁻¹y)`. -/
noncomputable def genericCharacterHomogeneousRaw
    (χ : GenericTwoTorsionContinuousCharacter G) :
    C(G × G, CMTwoTorsionCarrier) where
  toFun p := Multiplicative.toAdd (χ (p.1⁻¹ * p.2))
  continuous_toFun := by
    change Continuous (fun p : G × G =>
      Multiplicative.toAdd (χ (p.1⁻¹ * p.2)))
    exact χ.continuous_toFun.comp
      (continuous_fst.inv.mul continuous_snd)

noncomputable def genericCharacterHomogeneousCochain
    (χ : GenericTwoTorsionContinuousCharacter G) :
    C(G, C(G, CMTwoTorsionCarrier)) :=
  (genericCharacterHomogeneousRaw G χ).curry

@[simp] theorem genericCharacterHomogeneousCochain_apply
    (χ : GenericTwoTorsionContinuousCharacter G)
    (x y : G) :
    genericCharacterHomogeneousCochain G χ x y =
      Multiplicative.toAdd (χ (x⁻¹ * y)) := rfl

theorem genericCharacterHomogeneousCochain_invariant
    (χ : GenericTwoTorsionContinuousCharacter G) :
    genericCharacterHomogeneousCochain G χ ∈
      ((TopRep.resolution'
        (genericTwoTorsionRepresentation G)).X 1).ρ.invariants := by
  intro g
  ext x y
  simp only [coind₁_apply_apply,
    genericTwoTorsionRepresentation_action,
    genericCharacterHomogeneousCochain_apply]
  congr 2
  group

theorem genericCharacterHomogeneousRaw_relation
    (χ : GenericTwoTorsionContinuousCharacter G)
    (x y z : G) :
    genericCharacterHomogeneousCochain G χ y z =
      genericCharacterHomogeneousCochain G χ x z -
        genericCharacterHomogeneousCochain G χ x y := by
  have hmul :=
    congrArg Multiplicative.toAdd
      (χ.map_mul (x⁻¹ * y) (y⁻¹ * z))
  have hgroup :
      (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z := by
    group
  rw [hgroup] at hmul
  simp only [map_mul, Multiplicative.toAdd_mul] at hmul
  simp only [genericCharacterHomogeneousCochain_apply]
  rw [← sub_eq_iff_eq_add]
  simpa [add_comm] using hmul.symm

noncomputable def genericCharacterToContinuousOneCocycle
    (χ : GenericTwoTorsionContinuousCharacter G) :
    GenericTwoTorsionContinuousOneCocycle G := by
  let σ :
      (TopRep.homogeneousCochains
        (genericTwoTorsionRepresentation G)).X 1 :=
    ⟨genericCharacterHomogeneousCochain G χ,
      genericCharacterHomogeneousCochain_invariant G χ⟩
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
  change genericCharacterHomogeneousCochain G χ y z -
      (genericCharacterHomogeneousCochain G χ x z -
        genericCharacterHomogeneousCochain G χ x y) = 0
  rw [genericCharacterHomogeneousRaw_relation]
  abel

theorem genericContinuousOneCocycleToCharacter_leftInverse
    (χ : GenericTwoTorsionContinuousCharacter G) :
    genericContinuousOneCocycleToCharacter G
      (genericCharacterToContinuousOneCocycle G χ) = χ := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Multiplicative.toAdd_injective
  simp [genericContinuousOneCocycleToCharacter,
    genericCharacterToContinuousOneCocycle,
    genericCharacterHomogeneousCochain]

theorem genericContinuousOneCocycleToCharacter_rightInverse
    (σ : GenericTwoTorsionContinuousOneCocycle G) :
    genericCharacterToContinuousOneCocycle G
      (genericContinuousOneCocycleToCharacter G σ) = σ := by
  apply Subtype.ext
  apply Subtype.ext
  ext x y
  change σ.1.1 1 (x⁻¹ * y) = σ.1.1 x y
  have h :=
    genericContinuousOneCocycle_leftInvariant G σ x 1 (x⁻¹ * y)
  simpa using h

noncomputable def genericContinuousOneCocycleEquivCharacter :
    GenericTwoTorsionContinuousOneCocycle G ≃
      GenericTwoTorsionContinuousCharacter G where
  toFun := genericContinuousOneCocycleToCharacter G
  invFun := genericCharacterToContinuousOneCocycle G
  left_inv := genericContinuousOneCocycleToCharacter_rightInverse G
  right_inv := genericContinuousOneCocycleToCharacter_leftInverse G

/-- The cocycle/character equivalence retains the full group law. -/
/-- Scalar continuous quadratic characters for an arbitrary acting group. -/
abbrev GenericQuadraticCharacter :=
  G →ₜ* RationalQuadraticSign

noncomputable def genericTwoTorsionCharacterFst
    (χ : GenericTwoTorsionContinuousCharacter G) :
    GenericQuadraticCharacter G where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd (χ g)).1
  map_one' := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd χ.map_one
    exact congrArg Prod.fst h
  map_mul' g h := by
    apply Multiplicative.toAdd_injective
    have hm := congrArg Multiplicative.toAdd (χ.map_mul g h)
    exact congrArg Prod.fst hm
  continuous_toFun := by
    change Continuous (fun g => (Multiplicative.toAdd (χ g)).1)
    exact continuous_fst.comp χ.continuous_toFun

noncomputable def genericTwoTorsionCharacterSnd
    (χ : GenericTwoTorsionContinuousCharacter G) :
    GenericQuadraticCharacter G where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd (χ g)).2
  map_one' := by
    apply Multiplicative.toAdd_injective
    have h := congrArg Multiplicative.toAdd χ.map_one
    exact congrArg Prod.snd h
  map_mul' g h := by
    apply Multiplicative.toAdd_injective
    have hm := congrArg Multiplicative.toAdd (χ.map_mul g h)
    exact congrArg Prod.snd hm
  continuous_toFun := by
    change Continuous (fun g => (Multiplicative.toAdd (χ g)).2)
    exact continuous_snd.comp χ.continuous_toFun

noncomputable def genericQuadraticCharacterPairToTwoTorsion
    (χ : GenericQuadraticCharacter G × GenericQuadraticCharacter G) :
    GenericTwoTorsionContinuousCharacter G where
  toFun g :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd (χ.1 g), Multiplicative.toAdd (χ.2 g))
  map_one' := by
    apply Multiplicative.toAdd_injective
    ext <;> simp
  map_mul' g h := by
    apply Multiplicative.toAdd_injective
    ext <;> simp
  continuous_toFun := by
    change Continuous (fun g =>
      (Multiplicative.toAdd (χ.1 g), Multiplicative.toAdd (χ.2 g)))
    exact χ.1.continuous_toFun.prod_mk χ.2.continuous_toFun

/-- Product-valued continuous characters split into two scalar quadratic
characters for every acting group. -/
noncomputable def genericTwoTorsionCharacterMulEquivPair :
    GenericTwoTorsionContinuousCharacter G ≃*
      (GenericQuadraticCharacter G × GenericQuadraticCharacter G) where
  toFun χ :=
    (genericTwoTorsionCharacterFst G χ,
      genericTwoTorsionCharacterSnd G χ)
  invFun := genericQuadraticCharacterPairToTwoTorsion G
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd_injective
    ext <;> rfl
  right_inv χ := by
    rcases χ with ⟨χ₁, χ₂⟩
    apply Prod.ext
    · apply ContinuousMonoidHom.ext
      intro g
      apply Multiplicative.toAdd_injective
      rfl
    · apply ContinuousMonoidHom.ext
      intro g
      apply Multiplicative.toAdd_injective
      rfl
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

noncomputable def genericContinuousOneCocycleMulEquivCharacter :
    Multiplicative (GenericTwoTorsionContinuousOneCocycle G) ≃*
      GenericTwoTorsionContinuousCharacter G where
  toFun σ := genericContinuousOneCocycleToCharacter G σ.toAdd
  invFun χ :=
    Multiplicative.ofAdd
      (genericCharacterToContinuousOneCocycle G χ)
  left_inv σ := by
    apply Multiplicative.toAdd_injective
    exact genericContinuousOneCocycleToCharacter_rightInverse G σ.toAdd
  right_inv χ :=
    genericContinuousOneCocycleToCharacter_leftInverse G χ
  map_mul' σ τ := by
    apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd_injective
    rfl

/-- The categorical degree-one cycles object is the literal kernel above. -/
noncomputable abbrev genericContinuousCocyclesOneIso :
    ContinuousCohomology.cocycles
        (genericTwoTorsionRepresentation G) 1 ≅
      GenericTwoTorsionContinuousOneCocycle G :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((TopRep.homogeneousCochains
      (genericTwoTorsionRepresentation G)).cyclesIsKernel
        1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

/-- With the incoming differential zero, H¹ is literally the cycles object. -/
noncomputable def genericContinuousH1IsoCocyclesOne :
    continuousCohomology 1 (genericTwoTorsionRepresentation G) ≅
      ContinuousCohomology.cocycles
        (genericTwoTorsionRepresentation G) 1 :=
  (HomologicalComplex.isoHomologyπ
    (TopRep.homogeneousCochains
      (genericTwoTorsionRepresentation G))
    0 1 (CochainComplex.prev_nat_succ 0)
    (genericHomogeneousCochains_d_zero_one G)).symm

noncomputable def genericContinuousH1AddEquivOneCocycle :
    continuousCohomology 1 (genericTwoTorsionRepresentation G) ≃+
      GenericTwoTorsionContinuousOneCocycle G :=
  (genericContinuousH1IsoCocyclesOne G).toContinuousLinearEquiv
      .toLinearEquiv.toAddEquiv.trans
    (genericContinuousCocyclesOneIso G).toContinuousLinearEquiv
      .toLinearEquiv.toAddEquiv

/-- Generic locally-compact trivial-action continuous H¹ theorem, retaining
the group law. -/
noncomputable def genericTrivialTwoTorsionH1CharacterMulEquiv :
    Multiplicative
      (continuousCohomology 1 (genericTwoTorsionRepresentation G)) ≃*
      GenericTwoTorsionContinuousCharacter G :=
  (AddEquiv.toMultiplicative
      (genericContinuousH1AddEquivOneCocycle G)).trans
    (genericContinuousOneCocycleMulEquivCharacter G)

/-- Generic H¹ theorem already split into the two scalar quadratic-character
coordinates used by two-descent. -/
noncomputable def genericTrivialTwoTorsionH1QuadraticPairMulEquiv :
    Multiplicative
      (continuousCohomology 1 (genericTwoTorsionRepresentation G)) ≃*
      (GenericQuadraticCharacter G × GenericQuadraticCharacter G) :=
  (genericTrivialTwoTorsionH1CharacterMulEquiv G).trans
    (genericTwoTorsionCharacterMulEquivPair G)

/-- Plain-equivalence view for consumers that do not need the group law. -/
noncomputable def genericTrivialTwoTorsionH1CharacterEquiv :
    continuousCohomology 1 (genericTwoTorsionRepresentation G) ≃
      GenericTwoTorsionContinuousCharacter G :=
  Multiplicative.ofAdd.trans
    (genericTrivialTwoTorsionH1CharacterMulEquiv G).toEquiv

/-! ### Naturality under restriction -/

variable {H : Type*} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- Identity coefficient morphism from the restriction of the trivial
G-representation to the trivial H-representation. -/
noncomputable def genericTwoTorsionRestrictionHom
    (φ : H →ₜ* G) :
    TopRep.res (φ : H →* G)
        (genericTwoTorsionRepresentation G) ⟶
      genericTwoTorsionRepresentation H :=
  TopRep.ofHom
  { __ := ContinuousLinearMap.id ℤ CMTwoTorsionCarrier
    isIntertwining' h := by
      ext x
      rfl }

/-- Mathlib's canonical continuous-H¹ restriction map for the generic
trivial two-torsion coefficient object. -/
noncomputable def genericTwoTorsionH1Restrict
    (φ : H →ₜ* G) :
    continuousCohomology 1 (genericTwoTorsionRepresentation G) ⟶
      continuousCohomology 1 (genericTwoTorsionRepresentation H) :=
  ContinuousCohomology.map φ
    (genericTwoTorsionRestrictionHom (G := G) φ) 1

/-- Naturality of the canonical H¹-to-cycles identification under
restriction.  Since the incoming differential is zero, the identification
is the inverse of the canonical projection π, so this follows directly from
mathlib's π_map square. -/
theorem genericContinuousH1IsoCocyclesOne_hom_naturality
    (φ : H →ₜ* G) :
    genericTwoTorsionH1Restrict (G := G) φ ≫
        (genericContinuousH1IsoCocyclesOne H).hom
      =
    (genericContinuousH1IsoCocyclesOne G).hom ≫
      ContinuousCohomology.cocyclesMap φ
        (genericTwoTorsionRestrictionHom (G := G) φ) 1 := by
  rw [← cancel_epi
    (ContinuousCohomology.π
      (genericTwoTorsionRepresentation G) 1)]
  rw [Category.assoc, ContinuousCohomology.π_map]
  simp [genericContinuousH1IsoCocyclesOne]


/-- Restriction of scalar quadratic characters is ordinary precomposition. -/
noncomputable def genericQuadraticCharacterRestrict
    (φ : H →ₜ* G) :
    GenericQuadraticCharacter G →*
      GenericQuadraticCharacter H where
  toFun χ := χ.comp φ
  map_one' := by
    apply ContinuousMonoidHom.ext
    intro h
    rfl
  map_mul' χ ψ := by
    apply ContinuousMonoidHom.ext
    intro h
    rfl

/-- Componentwise restriction for the pair of scalar characters. -/
noncomputable def genericQuadraticCharacterPairRestrict
    (φ : H →ₜ* G) :
    (GenericQuadraticCharacter G × GenericQuadraticCharacter G) →*
      (GenericQuadraticCharacter H × GenericQuadraticCharacter H) where
  toFun χ :=
    (genericQuadraticCharacterRestrict (G := G) φ χ.1,
      genericQuadraticCharacterRestrict (G := G) φ χ.2)
  map_one' := by
    apply Prod.ext <;>
      simp [genericQuadraticCharacterRestrict]
  map_mul' χ ψ := by
    apply Prod.ext <;>
      simp [genericQuadraticCharacterRestrict]

/-- Single generic naturality seam for the low-degree theorem.

This replaces a separate representation-theoretic localization theorem at
every place.  Once paid, H¹ restriction under any continuous H -> G is
literally precomposition of the two scalar quadratic characters. -/
def GenericTrivialTwoTorsionH1RestrictionNaturality
    (φ : H →ₜ* G) : Prop :=
  ∀ x :
      continuousCohomology 1 (genericTwoTorsionRepresentation G),
    genericTrivialTwoTorsionH1QuadraticPairMulEquiv H
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict (G := G) φ x))
      =
    genericQuadraticCharacterPairRestrict (G := G) φ
      (genericTrivialTwoTorsionH1QuadraticPairMulEquiv G
        (Multiplicative.ofAdd x))

/-! ### Absolute Galois specialization -/

variable (K : Type*) [Field K]

/-- The absolute Galois group of every field is a compact topological group
in the Krull topology, hence the generic low-degree theorem applies without
any field-specific cohomological argument. -/
noncomputable def absoluteGaloisTrivialTwoTorsionH1CharacterMulEquiv :
    Multiplicative
      (continuousCohomology 1
        (genericTwoTorsionRepresentation
          (Field.absoluteGaloisGroup K))) ≃*
      GenericTwoTorsionContinuousCharacter
        (Field.absoluteGaloisGroup K) := by
  letI : CompactSpace (Field.absoluteGaloisGroup K) := inferInstance
  letI : LocallyCompactSpace (Field.absoluteGaloisGroup K) :=
    IsCompact.locallyCompactSpace_of_mem_nhds_of_group
      (K := Set.univ) isCompact_univ univ_mem
  exact genericTrivialTwoTorsionH1CharacterMulEquiv
    (Field.absoluteGaloisGroup K)

/-- Field-generic absolute-Galois H¹ theorem in the two scalar
quadratic-character coordinates used by two-descent. -/
noncomputable def absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv :
    Multiplicative
      (continuousCohomology 1
        (genericTwoTorsionRepresentation
          (Field.absoluteGaloisGroup K))) ≃*
      (GenericQuadraticCharacter (Field.absoluteGaloisGroup K) ×
        GenericQuadraticCharacter (Field.absoluteGaloisGroup K)) :=
  (absoluteGaloisTrivialTwoTorsionH1CharacterMulEquiv K).trans
    (genericTwoTorsionCharacterMulEquivPair
      (Field.absoluteGaloisGroup K))

/-- Plain equivalence form of the field-generic absolute-Galois theorem. -/
noncomputable def absoluteGaloisTrivialTwoTorsionH1CharacterEquiv :
    continuousCohomology 1
        (genericTwoTorsionRepresentation
          (Field.absoluteGaloisGroup K)) ≃
      GenericTwoTorsionContinuousCharacter
        (Field.absoluteGaloisGroup K) := by
  letI : CompactSpace (Field.absoluteGaloisGroup K) := inferInstance
  letI : LocallyCompactSpace (Field.absoluteGaloisGroup K) :=
    IsCompact.locallyCompactSpace_of_mem_nhds_of_group
      (K := Set.univ) isCompact_univ univ_mem
  exact genericTrivialTwoTorsionH1CharacterEquiv
    (Field.absoluteGaloisGroup K)


end Synthesis.Millennium.BSD
