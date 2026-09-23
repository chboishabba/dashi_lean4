import Synthesis.MillenniumBSDTrivialTwoTorsionH1Generic
import Synthesis.MillenniumBSDSquareClassGroups
import Synthesis.MillenniumBSDRationalQuadraticKummerHom
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
  χ.comp
    (Field.absoluteGaloisGroup.map
      (algebraMap ℚ ℚ_[p]))

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

/-- Continuous restriction homomorphism G_{Q_p} -> G_Q. -/
noncomputable def padicAbsoluteGaloisRestriction
    (p : ℕ) [Fact p.Prime] :
    PadicAbsoluteGalois p →ₜ* RationalAbsoluteGalois :=
  Field.absoluteGaloisGroup.map
    (algebraMap ℚ ℚ_[p])

/-- Restriction of the actual global E(Qbar) representation to G_{Q_p}. -/
noncomputable abbrev padicRestrictedEllipticPointRepresentation
    (p : ℕ) [Fact p.Prime] :
    TopRep ℤ (PadicAbsoluteGalois p) :=
  TopRep.res
    (padicAbsoluteGaloisRestriction p : PadicAbsoluteGalois p →*
      RationalAbsoluteGalois)
    cmEllipticPointRepresentation

/-- Literal inclusion of actual E[2] into E(Qbar), used locally after the
paid carrier equivalence from (C₂)² to the geometric two-torsion subgroup. -/
noncomputable def localActualE2InclusionCLM :
    cmAlgClosureTwoTorsionSubgroup →L[ℤ]
      CMAlgClosureProjectivePoint where
  toLinearMap :=
    { toFun := fun P => P.1
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro n P
        induction n using Int.induction_on with
        | ofNat n =>
            induction n with
            | zero => simp
            | succ n ih =>
                simp only [Int.ofNat_eq_coe, Int.ofNat_eq_coe,
                  Int.natCast_smul_eq_nsmul]
                simp [add_nsmul]
        | negSucc n =>
            simp }
  cont := continuous_of_discreteTopology

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
          ((padicTwoTorsionH1MulEquivSquareClassPair p
              (padicQuadraticKummerProducer_of_compatibility p h)).symm c).toAdd =
            0

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
