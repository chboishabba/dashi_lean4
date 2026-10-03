import BSDCohomology.EllipticKummerCocycleAlgebraExact
import Synthesis.MillenniumBSDCMGenericE2SameObjectExact
import Synthesis.MillenniumBSDCMGenericE2H1SquareClassExact
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Order

/-!
# Selected CM curve: geometric Kummer cocycle as an actual continuous H¹ class

Current Mathlib continuous cohomology does not yet expose the generic
short-exact-sequence -> long-exact-sequence connecting morphism.  Rather than
postulating that missing API, this owner constructs the selected CM Kummer
class directly from the same geometric exact sequence.

For a Galois-fixed geometric point P and a chosen half Q with 2Q=P,

  c_Q(σ) = σ(Q) - Q.

The generic algebra owner already proves the crossed-cocycle law.  On the
selected curve y²=x³-x all of E[2] is rational, hence pointwise Galois-fixed,
so c_Q is an honest homomorphism.  Its kernel contains the intersection of the
Krull-open stabilizers of the two coordinates of Q, giving continuity into the
discrete E[2] carrier.  We then transport the resulting continuous character
through the already-paid same-object E[2] equivalences and the repository's
literal low-degree H¹/character equivalence.

Thus the class constructed here lands in the exact coefficient object used by
the genuine Kummer/Sha lane.  It is not defined through square classes.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology
open scoped Topology

noncomputable section

------------------------------------------------------------------------
-- Selected crossed cocycle is an actual group homomorphism because E[2] is
-- pointwise fixed on this full-rational-two-torsion curve.
------------------------------------------------------------------------

noncomputable def cmGeometricKummerMonoidHom
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    RationalAbsoluteGalois →*
      Multiplicative (EllipticTwoTorsion cmWeierstrass) where
  toFun σ := Multiplicative.ofAdd (kummerCocycleValue cmWeierstrass hP Q σ)
  map_one' := by
    apply Multiplicative.toAdd_injective
    simp
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    change kummerCocycleValue cmWeierstrass hP Q (σ * τ) =
      kummerCocycleValue cmWeierstrass hP Q σ +
        kummerCocycleValue cmWeierstrass hP Q τ
    rw [kummerCocycleValue_mul]
    rw [cmGenericKummerE2_pointwise_fixed]

@[simp] theorem cmGeometricKummerMonoidHom_apply
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P)
    (σ : RationalAbsoluteGalois) :
    Multiplicative.toAdd (cmGeometricKummerMonoidHom hP Q σ) =
      kummerCocycleValue cmWeierstrass hP Q σ := rfl

------------------------------------------------------------------------
-- Krull continuity.
--
-- For an affine half Q=(x,y), Gal(Qbar/Q)-automorphisms fixing x and y fix Q,
-- hence lie in the Kummer-character kernel.  Each coordinate stabilizer is
-- open because x and y are algebraic over Q.  The point at infinity is the
-- trivial case.
------------------------------------------------------------------------

local instance : TopologicalSpace (EllipticTwoTorsion cmWeierstrass) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion cmWeierstrass) :=
  discreteTopology_bot _

private theorem cmGeometricKummer_kernel_isOpen
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    IsOpen ((cmGeometricKummerMonoidHom hP Q).ker : Set RationalAbsoluteGalois) := by
  cases hQ : Q.half with
  | zero =>
      have hker : (cmGeometricKummerMonoidHom hP Q).ker = ⊤ := by
        ext σ
        simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
        apply Multiplicative.toAdd_injective
        apply Subtype.ext
        change galoisPointMap cmWeierstrass σ Q.half - Q.half = 0
        rw [hQ]
        simp [galoisPointMap_one]
      rw [hker]
      exact isOpen_univ
  | some x y hxy =>
      let Hx : Subgroup RationalAbsoluteGalois :=
        MulAction.stabilizer RationalAbsoluteGalois x
      let Hy : Subgroup RationalAbsoluteGalois :=
        MulAction.stabilizer RationalAbsoluteGalois y
      have hxOpen : IsOpen (Hx : Set RationalAbsoluteGalois) := by
        dsimp [Hx]
        exact stabilizer_isOpen_of_isIntegral x
      have hyOpen : IsOpen (Hy : Set RationalAbsoluteGalois) := by
        dsimp [Hy]
        exact stabilizer_isOpen_of_isIntegral y
      have hInterOpen : IsOpen ((Hx ⊓ Hy : Subgroup RationalAbsoluteGalois) :
          Set RationalAbsoluteGalois) := hxOpen.inter hyOpen
      have hsub : Hx ⊓ Hy ≤ (cmGeometricKummerMonoidHom hP Q).ker := by
        intro σ hσ
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd_injective
        apply Subtype.ext
        change galoisPointMap cmWeierstrass σ Q.half - Q.half = 0
        have hx : σ x = x := by
          exact hσ.1
        have hy : σ y = y := by
          exact hσ.2
        rw [hQ]
        simp [galoisPointMap, hx, hy]
      apply Subgroup.isOpen_of_mem_nhds
      exact Filter.mem_of_superset
        (hInterOpen.mem_nhds (by simp [Hx, Hy])) hsub

/-- The selected geometric Kummer character is continuous for the Krull
 topology on G_Q and the discrete topology on actual E[2]. -/
noncomputable def cmGeometricKummerContinuousCharacter
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    RationalAbsoluteGalois →ₜ*
      Multiplicative (EllipticTwoTorsion cmWeierstrass) where
  __ := cmGeometricKummerMonoidHom hP Q
  continuous_toFun := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete, map_one, tendsto_pure]
    exact (cmGeometricKummer_kernel_isOpen hP Q).mem_nhds (by simp)

------------------------------------------------------------------------
-- Transport to the already-paid trivial (Z/2)^2 coefficient character.
------------------------------------------------------------------------

noncomputable def cmGeometricKummerActualE2Character
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    RationalAbsoluteGalois →ₜ* Multiplicative cmAlgClosureTwoTorsionSubgroup where
  toFun σ := Multiplicative.ofAdd
    (cmGenericKummerE2ToActualTopRep
      (Multiplicative.toAdd (cmGeometricKummerContinuousCharacter hP Q σ)))
  map_one' := by simp
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    simp
  continuous_toFun := by
    exact cmGenericKummerE2ToActualTopRep.hom.continuous.comp
      (cmGeometricKummerContinuousCharacter hP Q).continuous_toFun

noncomputable def cmGeometricKummerTrivialCharacter
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    CMTwoTorsionContinuousCharacter where
  toFun σ := Multiplicative.ofAdd
    (cmActualE2ContRepresentationEquiv.symm
      (Multiplicative.toAdd (cmGeometricKummerActualE2Character hP Q σ)))
  map_one' := by simp
  map_mul' σ τ := by
    apply Multiplicative.toAdd_injective
    simp
  continuous_toFun := by
    exact cmActualE2ContRepresentationEquiv.symm.toContinuousLinearEquiv.continuous.comp
      (cmGeometricKummerActualE2Character hP Q).continuous_toFun

------------------------------------------------------------------------
-- Package the literal character into continuous H¹ and transport it back to
-- the exact generic Kummer E[2] coefficient object.
------------------------------------------------------------------------

noncomputable def cmGeometricKummerTrivialH1
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    continuousCohomology 1 cmTwoTorsionRepresentation :=
  cmContinuousH1AddEquivOneCocycle.symm
    (cmCharacterToContinuousOneCocycle
      (cmGeometricKummerTrivialCharacter hP Q))

noncomputable def cmGeometricKummerActualE2H1
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    continuousCohomology 1 cmActualE2Representation :=
  cmE2H1ToActual (cmGeometricKummerTrivialH1 hP Q)

/-- Direct geometric Kummer H¹ class on the exact coefficient object used by
`cmGenericKummerE2H1MulEquivRatSquareClasses`. -/
noncomputable def cmGeometricKummerGenericE2H1
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q : GeometricHalfData cmWeierstrass P) :
    continuousCohomology 1 CMGenericKummerE2TopRep :=
  cmActualE2H1ToGenericKummer (cmGeometricKummerActualE2H1 hP Q)

------------------------------------------------------------------------
-- On the selected curve the class is independent of the chosen half already
-- before quotienting, because actual E[2] is pointwise fixed.
------------------------------------------------------------------------

theorem cmGeometricKummerContinuousCharacter_half_independent
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q₁ Q₂ : GeometricHalfData cmWeierstrass P) :
    cmGeometricKummerContinuousCharacter hP Q₁ =
      cmGeometricKummerContinuousCharacter hP Q₂ := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply Multiplicative.toAdd_injective
  exact kummerCocycleValue_eq_of_twoTorsion_fixed
    cmWeierstrass hP Q₁ Q₂ cmGenericKummerE2_pointwise_fixed σ

/-!
MAX-CUT STATUS

PAID IN THIS OWNER (subject to exact-head kernel certification):
* selected geometric Kummer crossed cocycle becomes an honest homomorphism on
  the exact generic E[2] object because all selected E[2] is Galois-fixed;
* its kernel is Krull-open, hence the character is continuous;
* the class is packaged through the repository's literal homogeneous-cocycle
  H¹ construction, not postulated and not defined from square classes;
* the resulting H¹ class is transported back to the exact generic Kummer E[2]
  coefficient object;
* half-choice independence holds already at character level for the selected
  full-rational-two-torsion curve.

NEXT STANDARD BRIDGE:
* embed literal E(Q) points into this geometric carrier and prove Galois
  fixedness;
* compute the image of `cmGeometricKummerGenericE2H1` under
  `cmGenericKummerE2H1MulEquivRatSquareClasses` and identify it with the
  existing `totalGlobalKummer` x-T class;
* repeat locally and prove localization naturality;
* identify explicit and cohomological Selmer and descend the quotient to
  genuine Sha(E)[2].
-/

end

end Synthesis.Millennium.BSD
