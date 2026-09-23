import Synthesis.MillenniumBSDCMTwoTorsionGaloisModule
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.Group.Equiv.TypeTags
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

/-- Plain-equivalence view for consumers that do not need the group law. -/
noncomputable def genericTrivialTwoTorsionH1CharacterEquiv :
    continuousCohomology 1 (genericTwoTorsionRepresentation G) ≃
      GenericTwoTorsionContinuousCharacter G :=
  Multiplicative.ofAdd.trans
    (genericTrivialTwoTorsionH1CharacterMulEquiv G).toEquiv

end Synthesis.Millennium.BSD
