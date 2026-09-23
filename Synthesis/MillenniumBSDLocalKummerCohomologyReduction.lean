import Synthesis.MillenniumBSDTrivialTwoTorsionH1Generic
import Synthesis.MillenniumBSDSquareClassGroups
import Synthesis.MillenniumBSDRationalQuadraticKummerHom
import Synthesis.MillenniumBSDQuadraticKummerPair
import Synthesis.MillenniumBSDActualEllipticPointTopRep
import Synthesis.MillenniumBSDActualE2TopRepSameObject
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Tactic

/-!
# Local Kummer cohomology reduction

All representation-theoretic continuous H¹ work is now generic in the field.
For the explicit p-adic two-descent lane, the only remaining local arithmetic
owner is the scalar quadratic Kummer equivalence

  Q_p^*/Q_p^{*2} ≃ Hom_cont(G_{Q_p}, C₂).

Once this scalar equivalence is supplied, the pair-valued H¹ identification
used by E[2] is compiled automatically.
-/

namespace Synthesis.Millennium.BSD

/-- Absolute Galois group of Q_p. -/
abbrev PadicAbsoluteGalois (p : ℕ) [Fact p.Prime] :=
  Field.absoluteGaloisGroup ℚ_[p]

/-- Scalar continuous quadratic characters of G_{Q_p}. -/
abbrev PadicQuadraticCharacter (p : ℕ) [Fact p.Prime] :=
  GenericQuadraticCharacter (PadicAbsoluteGalois p)

/-- Continuous restriction homomorphism G_{Q_p} -> G_Q. -/
noncomputable def padicAbsoluteGaloisRestriction
    (p : ℕ) [Fact p.Prime] :
    PadicAbsoluteGalois p →ₜ* RationalAbsoluteGalois :=
  Field.absoluteGaloisGroup.map
    (algebraMap ℚ ℚ_[p])

/-- Exact scalar local arithmetic theorem still required at a p-adic place. -/
def PadicQuadraticKummerProducer (p : ℕ) [Fact p.Prime] : Prop :=
  Nonempty
    (PadicSquareClass p ≃*
      PadicQuadraticCharacter p)

/-- Restrict a global quadratic character along
G_{Q_p} -> G_Q induced by Q -> Q_p. -/
noncomputable def restrictQuadraticCharacterToPadic
    (p : ℕ) [Fact p.Prime]
    (χ : RationalQuadraticCharacter) :
    PadicQuadraticCharacter p :=
  χ.comp (padicAbsoluteGaloisRestriction p)

/-- The real local owner is not an arbitrary scalar bijection but the
naturality square: local square-class Kummer must agree with restriction of
the already-paid global Kummer character. -/
structure PadicQuadraticKummerCompatibility
    (p : ℕ) [Fact p.Prime] where
  kummerEquiv :
    PadicSquareClass p ≃*
      PadicQuadraticCharacter p
  localize_commutes :
    ∀ c : RatSquareClass,
      kummerEquiv (localizeSquareClassHom p c) =
        restrictQuadraticCharacterToPadic p
          (ratSquareClassKummerHom c)

/-- Compatibility data implies the weaker local scalar Kummer producer. -/
theorem padicQuadraticKummerProducer_of_compatibility
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) :
    PadicQuadraticKummerProducer p :=
  ⟨h.kummerEquiv⟩



/-- A paid scalar local Kummer equivalence automatically gives the pair-valued
square-class/character equivalence used by full rational two-descent. -/
noncomputable def padicSquareClassPairMulEquivQuadraticCharacters
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerProducer p) :
    (PadicSquareClass p × PadicSquareClass p) ≃*
      (PadicQuadraticCharacter p × PadicQuadraticCharacter p) := by
  rcases h with ⟨e⟩
  exact e.prodCongr e

/-- The representation-theoretic half is already paid for every field.
Thus scalar p-adic Kummer alone produces the full local H¹/square-class pair
identification. -/
noncomputable def padicTwoTorsionH1MulEquivSquareClassPair
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerProducer p) :
    Multiplicative
      (ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation
          (PadicAbsoluteGalois p))) ≃*
      (PadicSquareClass p × PadicSquareClass p) :=
  (absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv ℚ_[p]).trans
    (padicSquareClassPairMulEquivQuadraticCharacters p h).symm

/-- Global generic H¹ in the repo's literal rational square-class pair,
retaining the group law. -/
noncomputable def rationalGenericTwoTorsionH1MulEquivSquareClassPair :
    Multiplicative
      (ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois)) ≃*
      (RatSquareClass × RatSquareClass) :=
  (absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv ℚ).trans
    quadraticCharacterPairMulEquivRatSquareClasses

/-- Local generic H¹ in the literal p-adic square-class pair, using the
specified compatible scalar Kummer equivalence rather than an arbitrary
witness extracted from Nonempty. -/
noncomputable def padicCompatibleTwoTorsionH1MulEquivSquareClassPair
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) :
    Multiplicative
      (ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation (PadicAbsoluteGalois p))) ≃*
      (PadicSquareClass p × PadicSquareClass p) :=
  (absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv ℚ_[p]).trans
    (h.kummerEquiv.prodCongr h.kummerEquiv).symm

/-- Exact pair-valued H¹/square-class localization square. -/
def PadicH1SquareClassNaturality
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) : Prop :=
  ∀ x :
      ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois),
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h
      (Multiplicative.ofAdd
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p) x))
      =
    localizeKummerPairHom p
      (rationalGenericTwoTorsionH1MulEquivSquareClassPair
        (Multiplicative.ofAdd x))

/-- Componentwise local Kummer equivalence supplied by compatible scalar
Kummer data. -/
noncomputable def padicCompatibleSquareClassPairMulEquivCharacters
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) :
    (PadicSquareClass p × PadicSquareClass p) ≃*
      (PadicQuadraticCharacter p × PadicQuadraticCharacter p) :=
  h.kummerEquiv.prodCongr h.kummerEquiv

/-- The scalar naturality square compiles to the pair-valued localization
square used by explicit two-descent. -/
theorem padicKummerPair_localize_commutes
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p)
    (c : RatSquareClass × RatSquareClass) :
    padicCompatibleSquareClassPairMulEquivCharacters p h
        (localizeKummerPairHom p c) =
      (restrictQuadraticCharacterToPadic p
          (ratSquareClassKummerHom c.1),
       restrictQuadraticCharacterToPadic p
          (ratSquareClassKummerHom c.2)) := by
  apply Prod.ext
  · exact h.localize_commutes c.1
  · exact h.localize_commutes c.2

/-- The universal H¹ restriction naturality seam plus scalar local Kummer
naturality compile the full pair-valued H¹/square-class localization square. -/
theorem padicH1SquareClassNaturality_of_generic
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p)
    (hNat :
      GenericTrivialTwoTorsionH1RestrictionNaturality
        (padicAbsoluteGaloisRestriction p)) :
    PadicH1SquareClassNaturality p h := by
  intro x
  apply (h.kummerEquiv.prodCongr h.kummerEquiv).injective
  have hH1 := hNat x
  have hLoc :=
    padicKummerPair_localize_commutes p h
      (rationalGenericTwoTorsionH1MulEquivSquareClassPair
        (Multiplicative.ofAdd x))
  rw [hLoc]
  simpa [padicCompatibleTwoTorsionH1MulEquivSquareClassPair,
    rationalGenericTwoTorsionH1MulEquivSquareClassPair,
    restrictQuadraticCharacterToPadic,
    genericQuadraticCharacterPairRestrict,
    genericQuadraticCharacterRestrict,
    quadraticCharacterPairMulEquivRatSquareClasses,
    ratSquareClassPairMulEquivQuadraticCharacters,
    rationalQuadraticKummerCharacterPairMulEquiv,
    rationalQuadraticKummerCharacterMulEquiv] using hH1

/-- The p-adic H¹/square-class localization square no longer needs a
place-specific representation-theoretic hypothesis: generic H¹ restriction
naturality is paid uniformly. -/
theorem padicH1SquareClassNaturality_paid
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) :
    PadicH1SquareClassNaturality p h :=
  padicH1SquareClassNaturality_of_generic p h
    (genericTrivialTwoTorsionH1RestrictionNaturality_paid
      (G := RationalAbsoluteGalois)
      (padicAbsoluteGaloisRestriction p))


/-- Literal additive inclusion of actual E[2] into E(Qbar). -/
noncomputable def localActualE2InclusionAddHom :
    cmAlgClosureTwoTorsionSubgroup →+
      CMAlgClosureProjectivePoint where
  toFun P := P.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Literal inclusion of actual E[2] into E(Qbar), used locally after the
paid carrier equivalence from (C₂)² to the geometric two-torsion subgroup. -/
noncomputable def localActualE2InclusionCLM :
    cmAlgClosureTwoTorsionSubgroup →L[ℤ]
      CMAlgClosureProjectivePoint where
  toLinearMap := localActualE2InclusionAddHom.toIntLinearMap
  cont := continuous_of_discreteTopology

/-- Direct global coefficient morphism from the generic trivial (C₂)²
module to the actual E(Qbar) module.  This is the same carrier map used in
the local construction below. -/
noncomputable def globalGenericE2ToEllipticPoint :
    genericTwoTorsionRepresentation RationalAbsoluteGalois ⟶
      cmEllipticPointRepresentation :=
  TopRep.ofHom
  { __ :=
      localActualE2InclusionCLM.comp
        cmActualE2ContinuousLinearEquiv.toContinuousLinearMap
    isIntertwining' σ := by
      ext x
      change
        (cmActualE2ContinuousLinearEquiv x).1 =
          cmAlgClosureGaloisAction σ
            (cmActualE2ContinuousLinearEquiv x).1
      exact
        (cmAlgClosure_twoTorsionSubgroup_pointwise_fixed
          σ (cmActualE2ContinuousLinearEquiv x)).symm }

/-- Global H¹ arrow from the generic trivial E[2] presentation to the actual
elliptic-point coefficient module. -/
noncomputable def globalGenericE2H1ToEllipticPointH1 :
    ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois) ⟶
      ContinuousCohomology.continuousCohomology 1
        cmEllipticPointRepresentation :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    globalGenericE2ToEllipticPoint 1

/-- Prize-facing elliptic H¹ class attached directly to the generic global
E[2] class underlying an explicit Selmer class. -/
noncomputable def explicitSelmerGenericClassToEllipticH1
    (s : explicitTwoSelmerSubgroup) :
    ContinuousCohomology.continuousCohomology 1
      cmEllipticPointRepresentation :=
  globalGenericE2H1ToEllipticPointH1
    (explicitSelmerToGenericTwoTorsionH1 s)

/-- Restriction of the actual global E(Qbar) representation to G_{Q_p}. -/
noncomputable abbrev padicRestrictedEllipticPointRepresentation
    (p : ℕ) [Fact p.Prime] :
    TopRep ℤ (PadicAbsoluteGalois p) :=
  TopRep.res
    (padicAbsoluteGaloisRestriction p : PadicAbsoluteGalois p →*
      RationalAbsoluteGalois)
    cmEllipticPointRepresentation

/-- Direct local coefficient morphism from the generic trivial (C₂)² module
to the restriction of the actual E(Qbar) module. -/
noncomputable def padicGenericE2ToRestrictedEllipticPoint
    (p : ℕ) [Fact p.Prime] :
    genericTwoTorsionRepresentation (PadicAbsoluteGalois p) ⟶
      padicRestrictedEllipticPointRepresentation p :=
  TopRep.ofHom
  { __ :=
      localActualE2InclusionCLM.comp
        cmActualE2ContinuousLinearEquiv.toContinuousLinearMap
    isIntertwining' σ := by
      ext x
      change
        (cmActualE2ContinuousLinearEquiv x).1 =
          cmAlgClosureGaloisAction
            (padicAbsoluteGaloisRestriction p σ)
            (cmActualE2ContinuousLinearEquiv x).1
      exact
        (cmAlgClosure_twoTorsionSubgroup_pointwise_fixed
          (padicAbsoluteGaloisRestriction p σ)
          (cmActualE2ContinuousLinearEquiv x)).symm }

/-- The exact local cohomology arrow occurring in Kummer exactness. -/
noncomputable def padicGenericE2H1ToEllipticPointH1
    (p : ℕ) [Fact p.Prime] :
    ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation (PadicAbsoluteGalois p)) ⟶
      ContinuousCohomology.continuousCohomology 1
        (padicRestrictedEllipticPointRepresentation p) :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id (PadicAbsoluteGalois p))
    (padicGenericE2ToRestrictedEllipticPoint p) 1

/-- Local Kummer exactness stated against the repo's literal explicit Kummer
image.  This is the actual p-adic elliptic theorem still missing once scalar
quadratic Kummer and its global/local naturality are supplied. -/
structure PadicEllipticKummerExactness
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) where
  kernel_iff_explicitKummerImage :
    ∀ c : PadicSquareClass p × PadicSquareClass p,
      c ∈ localKummerImageSubgroup p ↔
        padicGenericE2H1ToEllipticPointH1 p
          ((padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h).symm c).toAdd =
            0

/-- Weaker finite-place theorem actually needed for Selmer localization:
classes coming from the explicit local Kummer image vanish after
E[2] -> E(Qbar).  The reverse kernel implication belongs to the later
exact-kernel lane, not to localization-zero. -/
structure PadicEllipticKummerImageVanishing
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerCompatibility p) where
  image_maps_to_zero :
    ∀ c : PadicSquareClass p × PadicSquareClass p,
      c ∈ localKummerImageSubgroup p →
        padicGenericE2H1ToEllipticPointH1 p
          ((padicCompatibleTwoTorsionH1MulEquivSquareClassPair p h).symm c).toAdd =
            0

/-- Full local Kummer exactness implies the weaker localization theorem. -/
noncomputable def padicEllipticKummerImageVanishing_of_exactness
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hExact : PadicEllipticKummerExactness p hCompat) :
    PadicEllipticKummerImageVanishing p hCompat where
  image_maps_to_zero c hc :=
    (hExact.kernel_iff_explicitKummerImage c).1 hc


/-- Immediate local-exactness consequence consumed by the global Selmer
localization compiler. -/
theorem padicLocalKummerImage_maps_to_zero
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hExact : PadicEllipticKummerExactness p hCompat)
    (c : PadicSquareClass p × PadicSquareClass p)
    (hc : c ∈ localKummerImageSubgroup p) :
    padicGenericE2H1ToEllipticPointH1 p
      ((padicCompatibleTwoTorsionH1MulEquivSquareClassPair p hCompat).symm c).toAdd =
        0 :=
  (hExact.kernel_iff_explicitKummerImage c).1 hc

/-- Same consequence from the weaker image-vanishing boundary. -/
theorem padicLocalKummerImage_maps_to_zero_of_imageVanishing
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hVan : PadicEllipticKummerImageVanishing p hCompat)
    (c : PadicSquareClass p × PadicSquareClass p)
    (hc : c ∈ localKummerImageSubgroup p) :
    padicGenericE2H1ToEllipticPointH1 p
      ((padicCompatibleTwoTorsionH1MulEquivSquareClassPair p hCompat).symm c).toAdd =
        0 :=
  hVan.image_maps_to_zero c hc


/-- A global generic E[2] H¹ class whose literal square-class localization
lies in the explicit local Kummer image maps to zero under the local
E[2] -> E(Qbar) H¹ arrow.  This is the finite-place Selmer-local-condition
compiler. -/
theorem padicRestrictedGenericH1_maps_to_zero_of_localCondition
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hNat :
      GenericTrivialTwoTorsionH1RestrictionNaturality
        (padicAbsoluteGaloisRestriction p))
    (hExact : PadicEllipticKummerExactness p hCompat)
    (x :
      ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois))
    (hLocal :
      localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x))
        ∈ localKummerImageSubgroup p) :
    padicGenericE2H1ToEllipticPointH1 p
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p) x) = 0 := by
  have hSq :
      padicCompatibleTwoTorsionH1MulEquivSquareClassPair p hCompat
        (Multiplicative.ofAdd
          (genericTwoTorsionH1Restrict
            (G := RationalAbsoluteGalois)
            (padicAbsoluteGaloisRestriction p) x))
        =
      localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x)) :=
    padicH1SquareClassNaturality_of_generic p hCompat hNat x
  let e :=
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p hCompat
  have hMul :
      Multiplicative.ofAdd
          (genericTwoTorsionH1Restrict
            (G := RationalAbsoluteGalois)
            (padicAbsoluteGaloisRestriction p) x)
        =
      e.symm
        (localizeKummerPairHom p
          (rationalGenericTwoTorsionH1MulEquivSquareClassPair
            (Multiplicative.ofAdd x))) := by
    apply e.injective
    simpa [e] using hSq
  have hAdd := congrArg Multiplicative.toAdd hMul
  have hZero :=
    padicLocalKummerImage_maps_to_zero p hCompat hExact
      (localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x)))
      hLocal
  rw [hAdd]
  exact hZero


/-- Paid finite-place compiler: explicit local Kummer membership implies
vanishing in local elliptic-point H¹ using the uniform generic H¹ naturality
theorem internally. -/
theorem padicRestrictedGenericH1_maps_to_zero_of_localCondition_paid
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hExact : PadicEllipticKummerExactness p hCompat)
    (x :
      ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois))
    (hLocal :
      localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x))
        ∈ localKummerImageSubgroup p) :
    padicGenericE2H1ToEllipticPointH1 p
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p) x) = 0 :=
  padicRestrictedGenericH1_maps_to_zero_of_localCondition
    p hCompat
    (genericTrivialTwoTorsionH1RestrictionNaturality_paid
      (G := RationalAbsoluteGalois)
      (padicAbsoluteGaloisRestriction p))
    hExact x hLocal


/-- Finite-place Selmer-local-condition compiler using only image-vanishing,
not the reverse local Kummer exactness implication. -/
theorem padicRestrictedGenericH1_maps_to_zero_of_localCondition_imageVanishing
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hVan : PadicEllipticKummerImageVanishing p hCompat)
    (x :
      ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois))
    (hLocal :
      localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x))
        ∈ localKummerImageSubgroup p) :
    padicGenericE2H1ToEllipticPointH1 p
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p) x) = 0 := by
  have hSq :=
    padicH1SquareClassNaturality_paid p hCompat x
  let e :=
    padicCompatibleTwoTorsionH1MulEquivSquareClassPair p hCompat
  have hMul :
      Multiplicative.ofAdd
          (genericTwoTorsionH1Restrict
            (G := RationalAbsoluteGalois)
            (padicAbsoluteGaloisRestriction p) x)
        =
      e.symm
        (localizeKummerPairHom p
          (rationalGenericTwoTorsionH1MulEquivSquareClassPair
            (Multiplicative.ofAdd x))) := by
    apply e.injective
    simpa [e] using hSq
  have hAdd := congrArg Multiplicative.toAdd hMul
  have hZero :=
    padicLocalKummerImage_maps_to_zero_of_imageVanishing
      p hCompat hVan
      (localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x)))
      hLocal
  rw [hAdd]
  exact hZero

/-- Minimal finite-place theorem actually consumed by classical-Sha
localization.  It is stated only for restrictions of global generic E[2]
classes, so no full local square-class/H¹ equivalence is required. -/
structure PadicRestrictedGlobalKummerImageVanishing
    (p : ℕ) [Fact p.Prime] where
  restricted_global_image_maps_to_zero :
    ∀ x :
      ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation RationalAbsoluteGalois),
      localizeKummerPairHom p
        (rationalGenericTwoTorsionH1MulEquivSquareClassPair
          (Multiplicative.ofAdd x))
        ∈ localKummerImageSubgroup p →
      padicGenericE2H1ToEllipticPointH1 p
        (genericTwoTorsionH1Restrict
          (G := RationalAbsoluteGalois)
          (padicAbsoluteGaloisRestriction p) x) = 0

/-- The stronger scalar-Kummer compatibility plus local image-vanishing
theorem compiles to the minimal restricted-global boundary. -/
noncomputable def padicRestrictedGlobalKummerImageVanishing_of_localKummer
    (p : ℕ) [Fact p.Prime]
    (hCompat : PadicQuadraticKummerCompatibility p)
    (hVan : PadicEllipticKummerImageVanishing p hCompat) :
    PadicRestrictedGlobalKummerImageVanishing p where
  restricted_global_image_maps_to_zero x hx :=
    padicRestrictedGenericH1_maps_to_zero_of_localCondition_imageVanishing
      p hCompat hVan x hx

/-- Generic global H¹ class represented by an explicit Selmer square-class
pair. -/
noncomputable def explicitSelmerToGenericTwoTorsionH1
    (s : explicitTwoSelmerSubgroup) :
    ContinuousCohomology.continuousCohomology 1
      (genericTwoTorsionRepresentation RationalAbsoluteGalois) :=
  (rationalGenericTwoTorsionH1MulEquivSquareClassPair.symm s.1).toAdd

@[simp] theorem explicitSelmerToGenericTwoTorsionH1_squareClass
    (s : explicitTwoSelmerSubgroup) :
    rationalGenericTwoTorsionH1MulEquivSquareClassPair
      (Multiplicative.ofAdd (explicitSelmerToGenericTwoTorsionH1 s)) =
        s.1 := by
  simp [explicitSelmerToGenericTwoTorsionH1]

/-- All finite explicit Selmer conditions compile simultaneously to vanishing
in the restricted elliptic-point H¹ groups, assuming the one generic H¹
restriction-naturality theorem and the scalar/local elliptic Kummer theorems
at each prime. -/
theorem explicitSelmer_finite_localizations_vanish
    (hNat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        GenericTrivialTwoTorsionH1RestrictionNaturality
          (padicAbsoluteGaloisRestriction p.1))
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hExact :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerExactness p.1 (hCompat p))
    (s : explicitTwoSelmerSubgroup)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    padicGenericE2H1ToEllipticPointH1 p.1
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p.1)
        (explicitSelmerToGenericTwoTorsionH1 s)) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  apply padicRestrictedGenericH1_maps_to_zero_of_localCondition
    p.1 (hCompat p) (hNat p) (hExact p)
  simpa [explicitSelmerToGenericTwoTorsionH1_squareClass] using s.2.2 p


/-- All finite explicit Selmer conditions compile simultaneously to local
elliptic-H¹ vanishing without any additional H¹ restriction hypothesis. -/
theorem explicitSelmer_finite_localizations_vanish_paid
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hExact :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerExactness p.1 (hCompat p))
    (s : explicitTwoSelmerSubgroup)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    padicGenericE2H1ToEllipticPointH1 p.1
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p.1)
        (explicitSelmerToGenericTwoTorsionH1 s)) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  apply padicRestrictedGenericH1_maps_to_zero_of_localCondition_paid
    p.1 (hCompat p) (hExact p)
  simpa [explicitSelmerToGenericTwoTorsionH1_squareClass] using s.2.2 p


/-- All finite explicit Selmer conditions vanish in local elliptic H¹ from
the weaker image-vanishing theorem at each prime. -/
theorem explicitSelmer_finite_localizations_vanish_imageVanishing
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (s : explicitTwoSelmerSubgroup)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    padicGenericE2H1ToEllipticPointH1 p.1
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p.1)
        (explicitSelmerToGenericTwoTorsionH1 s)) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  apply padicRestrictedGenericH1_maps_to_zero_of_localCondition_imageVanishing
    p.1 (hCompat p) (hVan p)
  simpa [explicitSelmerToGenericTwoTorsionH1_squareClass] using s.2.2 p

/-- All finite explicit Selmer localizations vanish from the minimal
restricted-global local Kummer theorem, with no scalar local Kummer
equivalence exposed to downstream callers. -/
theorem explicitSelmer_finite_localizations_vanish_restrictedGlobal
    (hLocal :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicRestrictedGlobalKummerImageVanishing p.1)
    (s : explicitTwoSelmerSubgroup)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    padicGenericE2H1ToEllipticPointH1 p.1
      (genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p.1)
        (explicitSelmerToGenericTwoTorsionH1 s)) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  apply (hLocal p).restricted_global_image_maps_to_zero
  simpa [explicitSelmerToGenericTwoTorsionH1_squareClass] using s.2.2 p

/-- Machine-readable local frontier: the continuous H¹ normalization and
pair decomposition are paid uniformly; scalar local Kummer and compatibility
with the explicit elliptic Kummer coordinates remain. -/
structure PadicKummerCohomologyBoundaryStatus where
  genericContinuousH1Paid : Bool
  quadraticCharacterPairSplitPaid : Bool
  explicitPadicSquareClassCarrierPaid : Bool
  explicitEllipticLocalKummerHomPaid : Bool
  scalarPadicKummerPaid : Bool
  scalarGlobalLocalNaturalityPaid : Bool
  pairGlobalLocalNaturalityCompilerPaid : Bool
  localE2ToEllipticH1ArrowPaid : Bool
  localEllipticKummerExactnessPaid : Bool
  explicitToCohomologicalCompatibilityPaid : Bool
  deriving DecidableEq, Repr

def padicKummerCohomologyBoundaryStatus :
    PadicKummerCohomologyBoundaryStatus :=
  ⟨true, true, true, true, false, false, true, true, false, false⟩

end Synthesis.Millennium.BSD
