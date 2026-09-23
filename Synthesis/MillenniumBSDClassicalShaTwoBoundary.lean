import Synthesis.MillenniumBSDActualE2TopRepSameObject
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction
import Synthesis.MillenniumBSDActualEllipticPointTopRep
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Correct classical Sha[2] boundary for the CM curve

The finite Galois module `E[2]` is now completely identified in the repo, but
`Sha¹(E[2])` is not the classical Tate--Shafarevich group of the elliptic
curve.  The classical two-descent exact sequence is

  0 → E(Q)/2E(Q) → Sel₂(E/Q) → Sha(E/Q)[2] → 0,

and its right-hand term is the two-torsion in the localization kernel for the
*full elliptic point module* `E(Qbar)`, reached from `H¹(G_Q,E[2])` through
the Kummer long exact sequence.

This file records that prize-facing target correctly.  It deliberately does
not replace the missing continuous Kummer theorem by an E[2]-Sha surrogate.
-/

namespace Synthesis.Millennium.BSD

/-- The finite-module Sha target is useful cohomology, but is not classical Sha(E)[2]. -/
noncomputable abbrev cmE2FiniteModuleShaOne :=
  rationalTateShafarevichOne cmActualE2Representation

noncomputable abbrev cmE2FiniteModuleShaTwo :=
  rationalTateShafarevichTwoTorsion cmActualE2Representation

/--
For any actual continuous representation of the full elliptic point group,
this is the correct classical degree-one Sha localization kernel.
-/
noncomputable def classicalEllipticShaOne
    (Ebar : TopRep ℤ RationalAbsoluteGalois) :=
  rationalTateShafarevichOne Ebar

/-- The literal two-torsion subgroup of the classical elliptic Sha target. -/
noncomputable def classicalEllipticShaTwo
    (Ebar : TopRep ℤ RationalAbsoluteGalois) :=
  rationalTateShafarevichTwoTorsion Ebar

/-- Literal additive inclusion of the actual E[2] subgroup into the full
algebraic-closure elliptic point group. -/
noncomputable def cmActualE2InclusionAddHom :
    cmAlgClosureTwoTorsionSubgroup →+
      CMAlgClosureProjectivePoint where
  toFun P := P.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The E[2] inclusion as a continuous Z-linear map; both carriers use the
discrete topology already installed in the repo. -/
noncomputable def cmActualE2InclusionCLM :
    cmAlgClosureTwoTorsionSubgroup →L[ℤ]
      CMAlgClosureProjectivePoint where
  toLinearMap := cmActualE2InclusionAddHom.toIntLinearMap
  cont := continuous_of_discreteTopology

@[simp] theorem cmActualE2InclusionCLM_apply
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2InclusionCLM P = P.1 := rfl

/-- The literal subgroup inclusion is Galois-equivariant. -/
noncomputable def cmActualE2InclusionIntertwining :
    cmActualE2Representation.ρ →ⁱL
      cmEllipticPointRepresentation.ρ where
  __ := cmActualE2InclusionCLM
  isIntertwining' σ := by
    ext P
    change P.1 = cmAlgClosureGaloisAction σ P.1
    exact cmActualE2GaloisAction_eq_coordinate σ P

/-- Actual E[2] -> E(Qbar) as a morphism of topological representations. -/
noncomputable def cmActualE2TopRepInclusion :
    cmActualE2Representation ⟶ cmEllipticPointRepresentation :=
  TopRep.ofHom cmActualE2InclusionIntertwining

/-- The global degree-one cohomology arrow induced by E[2] -> E(Qbar).
This is the canonical right-hand Kummer map whose kernel is the global
connecting-image E(Q)/2E(Q). -/
noncomputable def cmActualE2H1ToEllipticPointH1 :
    ContinuousCohomology.continuousCohomology 1 cmActualE2Representation ⟶
      ContinuousCohomology.continuousCohomology 1
        cmEllipticPointRepresentation :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id RationalAbsoluteGalois)
    cmActualE2TopRepInclusion 1

/-- Canonical actual-E[2] H¹ class attached to an explicit Selmer class,
using the paid multiplicative H¹/square-class equivalence. -/
noncomputable def cmExplicitSelmerClassToActualE2H1
    (s : explicitTwoSelmerSubgroup) :
    ContinuousCohomology.continuousCohomology 1
      cmActualE2Representation :=
  (cmActualE2H1MulEquivRatSquareClasses_paid.symm s.1).toAdd

@[simp] theorem cmExplicitSelmerClassToActualE2H1_one :
    cmExplicitSelmerClassToActualE2H1 1 = 0 := by
  change (cmActualE2H1MulEquivRatSquareClasses_paid.symm 1).toAdd = 0
  rw [map_one]
  rfl

theorem cmExplicitSelmerClassToActualE2H1_mul
    (s t : explicitTwoSelmerSubgroup) :
    cmExplicitSelmerClassToActualE2H1 (s * t) =
      cmExplicitSelmerClassToActualE2H1 s +
        cmExplicitSelmerClassToActualE2H1 t := by
  change
    (cmActualE2H1MulEquivRatSquareClasses_paid.symm (s.1 * t.1)).toAdd =
      (cmActualE2H1MulEquivRatSquareClasses_paid.symm s.1).toAdd +
        (cmActualE2H1MulEquivRatSquareClasses_paid.symm t.1).toAdd
  rw [map_mul]
  rfl

/-- Canonical global cohomology class attached to an explicit Selmer class:
first recover its actual E[2] H¹ class, then apply the literal inclusion
E[2] -> E(Qbar).  No classical Kummer exactness is assumed in this
definition. -/
noncomputable def cmExplicitSelmerClassToEllipticH1
    (s : explicitTwoSelmerSubgroup) :
    ContinuousCohomology.continuousCohomology 1
      cmEllipticPointRepresentation :=
  cmActualE2H1ToEllipticPointH1
    (cmExplicitSelmerClassToActualE2H1 s)

@[simp] theorem cmExplicitSelmerClassToEllipticH1_one_paid :
    cmExplicitSelmerClassToEllipticH1 1 = 0 := by
  unfold cmExplicitSelmerClassToEllipticH1
  rw [cmExplicitSelmerClassToActualE2H1_one]
  simp

theorem cmExplicitSelmerClassToEllipticH1_mul_paid
    (s t : explicitTwoSelmerSubgroup) :
    cmExplicitSelmerClassToEllipticH1 (s * t) =
      cmExplicitSelmerClassToEllipticH1 s +
        cmExplicitSelmerClassToEllipticH1 t := by
  unfold cmExplicitSelmerClassToEllipticH1
  rw [cmExplicitSelmerClassToActualE2H1_mul]
  exact map_add _ _ _

/-- The canonical explicit-Selmer class lands in a two-torsion class of
H¹(E(Qbar)) because it comes from H¹(E[2]), which is already proved
exponent two, and continuous cohomology functoriality is additive. -/
theorem cmExplicitSelmerClassToEllipticH1_two_torsion_paid
    (s : explicitTwoSelmerSubgroup) :
    (2 : ℕ) • cmExplicitSelmerClassToEllipticH1 s = 0 := by
  unfold cmExplicitSelmerClassToEllipticH1
  rw [← map_nsmul]
  rw [cmActualE2ContinuousH1_exponent_two]
  simp

/--
The genuinely remaining laws for the canonical global class above.

These are the continuous Kummer/localization assertions which are not yet in
mathlib or the repo:
* identity and product compatibility (so the canonical class is a hom);
* every explicit Selmer class localizes trivially in H¹(E(Qbar));
* its image is 2-torsion;
* its kernel is exactly the paid global Kummer image E(Q)/2E(Q);
* every classical Sha[2] class is represented by an explicit Selmer class.
-/
structure ClassicalTwoDescentCanonicalMapLaws where
  map_one :
    cmExplicitSelmerClassToEllipticH1 1 = 0
  map_mul :
    ∀ s t : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 (s * t) =
        cmExplicitSelmerClassToEllipticH1 s +
          cmExplicitSelmerClassToEllipticH1 t
  localization_zero :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s ∈
        classicalEllipticShaOne cmEllipticPointRepresentation
  two_torsion :
    ∀ s : explicitTwoSelmerSubgroup,
      (2 : ℕ) • cmExplicitSelmerClassToEllipticH1 s = 0
  kernel_iff_globalKummerImage :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s = 0 ↔
        s ∈ globalKummerImageSubgroup
  surjective_on_sha_two :
    ∀ x : classicalEllipticShaTwo cmEllipticPointRepresentation,
      ∃ s : explicitTwoSelmerSubgroup,
        cmExplicitSelmerClassToEllipticH1 s = x.1.1

/-- Reduced classical Kummer boundary after paying the 2-torsion law internally. -/
structure ClassicalTwoDescentCanonicalCoreLaws where
  map_one :
    cmExplicitSelmerClassToEllipticH1 1 = 0
  map_mul :
    ∀ s t : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 (s * t) =
        cmExplicitSelmerClassToEllipticH1 s +
          cmExplicitSelmerClassToEllipticH1 t
  localization_zero :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s ∈
        classicalEllipticShaOne cmEllipticPointRepresentation
  kernel_iff_globalKummerImage :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s = 0 ↔
        s ∈ globalKummerImageSubgroup
  surjective_on_sha_two :
    ∀ x : classicalEllipticShaTwo cmEllipticPointRepresentation,
      ∃ s : explicitTwoSelmerSubgroup,
        cmExplicitSelmerClassToEllipticH1 s = x.1.1

/-- Fill the full canonical-law record from the reduced core boundary. -/
noncomputable def classicalTwoDescentCanonicalMapLaws_of_core
    (h : ClassicalTwoDescentCanonicalCoreLaws) :
    ClassicalTwoDescentCanonicalMapLaws where
  map_one := h.map_one
  map_mul := h.map_mul
  localization_zero := h.localization_zero
  two_torsion := cmExplicitSelmerClassToEllipticH1_two_torsion_paid
  kernel_iff_globalKummerImage := h.kernel_iff_globalKummerImage
  surjective_on_sha_two := h.surjective_on_sha_two

/-- Final reduced classical two-descent boundary after paying the group law
and 2-torsion internally.  These are precisely the localization/exactness
statements still missing from the repo. -/
structure ClassicalTwoDescentLocalizationExactnessLaws where
  localization_zero :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s ∈
        classicalEllipticShaOne cmEllipticPointRepresentation
  kernel_iff_globalKummerImage :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s = 0 ↔
        s ∈ globalKummerImageSubgroup
  surjective_on_sha_two :
    ∀ x : classicalEllipticShaTwo cmEllipticPointRepresentation,
      ∃ s : explicitTwoSelmerSubgroup,
        cmExplicitSelmerClassToEllipticH1 s = x.1.1

/-- Fill the reduced-core law record from the three genuinely remaining
localization/exactness statements. -/
noncomputable def classicalTwoDescentCanonicalCoreLaws_of_localizationExactness
    (h : ClassicalTwoDescentLocalizationExactnessLaws) :
    ClassicalTwoDescentCanonicalCoreLaws where
  map_one := cmExplicitSelmerClassToEllipticH1_one_paid
  map_mul := cmExplicitSelmerClassToEllipticH1_mul_paid
  localization_zero := h.localization_zero
  kernel_iff_globalKummerImage := h.kernel_iff_globalKummerImage
  surjective_on_sha_two := h.surjective_on_sha_two

/-- The three remaining localization/exactness laws compile all the way to
the full canonical-map law record. -/
noncomputable def classicalTwoDescentCanonicalMapLaws_of_localizationExactness
    (h : ClassicalTwoDescentLocalizationExactnessLaws) :
    ClassicalTwoDescentCanonicalMapLaws :=
  classicalTwoDescentCanonicalMapLaws_of_core
    (classicalTwoDescentCanonicalCoreLaws_of_localizationExactness h)

/-- Package the canonical global class as an actual homomorphism to classical
Sha[2] once the remaining Kummer/localization laws are supplied. -/
noncomputable def cmExplicitSelmerToClassicalShaTwo
    (h : ClassicalTwoDescentCanonicalMapLaws) :
    explicitTwoSelmerSubgroup →*
      Multiplicative (classicalEllipticShaTwo cmEllipticPointRepresentation) where
  toFun s :=
    Multiplicative.ofAdd
      ⟨⟨cmExplicitSelmerClassToEllipticH1 s, h.localization_zero s⟩,
        by
          apply Subtype.ext
          exact h.two_torsion s⟩
  map_one' := by
    apply Multiplicative.toAdd_injective
    apply Subtype.ext
    apply Subtype.ext
    exact h.map_one
  map_mul' s t := by
    apply Multiplicative.toAdd_injective
    apply Subtype.ext
    apply Subtype.ext
    exact h.map_mul s t

theorem cmExplicitSelmerToClassicalShaTwo_kernel
    (h : ClassicalTwoDescentCanonicalMapLaws) :
    (cmExplicitSelmerToClassicalShaTwo h).ker =
      globalKummerImageSubgroup := by
  ext s
  rw [MonoidHom.mem_ker]
  change cmExplicitSelmerClassToEllipticH1 s = 0 ↔
    s ∈ globalKummerImageSubgroup
  exact h.kernel_iff_globalKummerImage s

theorem cmExplicitSelmerToClassicalShaTwo_surjective
    (h : ClassicalTwoDescentCanonicalMapLaws) :
    Function.Surjective (cmExplicitSelmerToClassicalShaTwo h) := by
  intro x
  rcases h.surjective_on_sha_two x.toAdd with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  apply Multiplicative.toAdd_injective
  apply Subtype.ext
  apply Subtype.ext
  exact hs

/--
Canonical exact-map form of the remaining classical two-descent theorem.

Rather than asking for the final quotient equivalence as a black box, this
records exactly what continuous Kummer exactness and localization must
produce on the already-built explicit Selmer subgroup:

* a homomorphism from the explicit Selmer group to classical Sha(E)[2];
* kernel equal to the already-paid global Kummer image E(Q)/2E(Q);
* surjectivity.

Noether's first isomorphism theorem then constructs the desired cokernel
equivalence automatically.
-/
structure ClassicalTwoDescentExactMapBoundary where
  selmerToSha :
    explicitTwoSelmerSubgroup →*
      Multiplicative (classicalEllipticShaTwo cmEllipticPointRepresentation)
  kernel_eq_globalKummerImage :
    selmerToSha.ker = globalKummerImageSubgroup
  surjective : Function.Surjective selmerToSha

/-- The canonical Kummer/localization laws inhabit the exact-map boundary
without any further mathematical assumptions. -/
noncomputable def classicalTwoDescentExactMapBoundary_of_canonicalLaws
    (h : ClassicalTwoDescentCanonicalMapLaws) :
    ClassicalTwoDescentExactMapBoundary where
  selmerToSha := cmExplicitSelmerToClassicalShaTwo h
  kernel_eq_globalKummerImage :=
    cmExplicitSelmerToClassicalShaTwo_kernel h
  surjective :=
    cmExplicitSelmerToClassicalShaTwo_surjective h

/-- The exact-map boundary compiles to the literal explicit Selmer cokernel
equivalence by the first isomorphism theorem. -/
noncomputable def explicitSelmerCokernelEquivClassicalShaTwo_of_exactMap
    (h : ClassicalTwoDescentExactMapBoundary) :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo cmEllipticPointRepresentation := by
  let eKer :
      ExplicitTwoSelmerCokernel ≃*
        (explicitTwoSelmerSubgroup ⧸ h.selmerToSha.ker) :=
    QuotientGroup.quotientMulEquivOfEq h.kernel_eq_globalKummerImage
  let eSha :
      (explicitTwoSelmerSubgroup ⧸ h.selmerToSha.ker) ≃*
        Multiplicative (classicalEllipticShaTwo cmEllipticPointRepresentation) :=
    QuotientGroup.quotientKerEquivOfSurjective h.selmerToSha h.surjective
  let e := eKer.trans eSha
  exact
    { toFun := fun q => (e q).toAdd
      invFun := fun s => e.symm (Multiplicative.ofAdd s)
      left_inv := by
        intro q
        simp [e]
      right_inv := by
        intro s
        simp [e] }

/--
Exact remaining arithmetic producer after the explicit 2-descent work.

`ellipticPointRepresentation` must be the full `E(Qbar)` Galois module, not
`E[2]`.  The equivalence is precisely what continuous Kummer + local Kummer
compatibility prove in the classical descent argument.
-/
structure ClassicalTwoDescentShaComparison where
  ellipticPointRepresentation : TopRep ℤ RationalAbsoluteGalois
  explicitCokernelEquivClassicalShaTwo :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo ellipticPointRepresentation

noncomputable def explicitSelmerCokernelEquivClassicalShaTwo
    (comparison : ClassicalTwoDescentShaComparison) :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo comparison.ellipticPointRepresentation :=
  comparison.explicitCokernelEquivClassicalShaTwo

/--
The prize-facing BA4--BA6 boundary: continuous Kummer must construct the
comparison above from the already-paid actual E[2] representation and the
explicit local square-class Selmer conditions.
-/
def ContinuousKummerTwoDescentProducer : Prop :=
  Nonempty ClassicalTwoDescentShaComparison

/--
Sharpened prize-facing boundary with the full elliptic-point representation
already fixed internally.  The only remaining datum is the actual continuous
Kummer/localization equivalence from the explicit Selmer cokernel to
classical Sha(E)[2].
-/
def ActualClassicalTwoDescentShaComparison : Prop :=
  Nonempty
    (ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo cmEllipticPointRepresentation)

/-- Exact-map data therefore pays the older fixed-representation comparison
boundary without asking for an independent equivalence producer. -/
theorem actualClassicalTwoDescentShaComparison_of_exactMap
    (h : ClassicalTwoDescentExactMapBoundary) :
    ActualClassicalTwoDescentShaComparison :=
  ⟨explicitSelmerCokernelEquivClassicalShaTwo_of_exactMap h⟩


/-- The three remaining localization/exactness laws compile directly to the
fixed-representation classical Sha comparison. -/
theorem actualClassicalTwoDescentShaComparison_of_localizationExactness
    (h : ClassicalTwoDescentLocalizationExactnessLaws) :
    ActualClassicalTwoDescentShaComparison :=
  actualClassicalTwoDescentShaComparison_of_exactMap
    (classicalTwoDescentExactMapBoundary_of_canonicalLaws
      (classicalTwoDescentCanonicalMapLaws_of_localizationExactness h))

/-- The fixed-representation comparison compiles back to the older
structure-shaped producer. -/
theorem continuousKummerTwoDescentProducer_of_actualComparison
    (h : ActualClassicalTwoDescentShaComparison) :
    ContinuousKummerTwoDescentProducer := by
  rcases h with ⟨e⟩
  exact ⟨
    { ellipticPointRepresentation := cmEllipticPointRepresentation
      explicitCokernelEquivClassicalShaTwo := e }⟩

/-- Machine-readable sharpening of the classical Sha boundary. -/
structure ClassicalShaTwoBoundaryStatus where
  fullEllipticPointCarrierPaid : Bool
  coordinateGaloisActionPaid : Bool
  additiveGaloisActionPaid : Bool
  fullEllipticPointTopRepPaid : Bool
  actualE2InclusionTopRepPaid : Bool
  inducedGlobalH1ArrowPaid : Bool
  globalH1SquareClassGroupEquivPaid : Bool
  canonicalSelmerMapHomLawPaid : Bool
  canonicalSelmerMapTwoTorsionPaid : Bool
  localizationZeroPaid : Bool
  exactKernelPaid : Bool
  shaTwoSurjectivityPaid : Bool
  finalCokernelCompilerPaid : Bool
  deriving DecidableEq, Repr

def classicalShaTwoBoundaryStatus : ClassicalShaTwoBoundaryStatus :=
  ⟨true, true, true, true,
    true, true, true, true, true,
    false, false, false,
    true⟩


end Synthesis.Millennium.BSD
