import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
import BSDCohomology.EllipticTwoTorsionAction
import Mathlib.Tactic

/-!
# K2: Galois-equivariance of the original geometric Kummer sequence

This implements the two required equivariance squares over the original
selected curve E:y²=x³-x. The actions are the EXISTING literal
base-change actions on the geometric point group and its actual E[2]
subgroup, not artificial representations.

The underlying short exact sequence was proved by the already-established
geometric inclusion/kernel and algebraic-closure half-point theorems.

The result is an exact sequence of Galois modules AT THE LEVEL OF
EQUIVARIANT ADDITIVE MAPS. It does not by itself construct the
continuous TopRep short exact sequence, connecting δ in continuous H¹,
local completion naturality, or the classical Sha[2] cokernel.
-/

namespace Synthesis.Millennium.BSD

/-- Inclusion of literal geometric E[2] commutes with every original
absolute-Galois automorphism, on the actual Weierstrass curve. -/
theorem cmSelectedGeometricE2Inclusion_galois_equivariant
    (σ : Field.absoluteGaloisGroup ℚ)
    (T : BSDCohomology.EllipticTwoTorsion cmWeierstrass) :
    BSDCohomology.twoTorsionInclusion cmWeierstrass
      (BSDCohomology.galoisTwoTorsionMap cmWeierstrass σ T) =
    BSDCohomology.galoisPointMap cmWeierstrass σ
      (BSDCohomology.twoTorsionInclusion cmWeierstrass T) := by
  change
    (BSDCohomology.galoisTwoTorsionMap cmWeierstrass σ T).1 =
      BSDCohomology.galoisPointMap cmWeierstrass σ T.1
  exact BSDCohomology.galoisTwoTorsionMap_coe cmWeierstrass σ T

/-- Geometric doubling commutes with every original absolute-Galois
action: the actual map [2] is an equivariant group homomorphism. -/
theorem cmSelectedGeometricDoubling_galois_equivariant
    (σ : Field.absoluteGaloisGroup ℚ)
    (P : BSDCohomology.GeometricPoint cmWeierstrass) :
    BSDCohomology.geometricDoubling cmWeierstrass
      (BSDCohomology.galoisPointMap cmWeierstrass σ P) =
    BSDCohomology.galoisPointMap cmWeierstrass σ
      (BSDCohomology.geometricDoubling cmWeierstrass P) := by
  change
    (2 : ℕ) • BSDCohomology.galoisPointMap cmWeierstrass σ P =
      BSDCohomology.galoisPointMap cmWeierstrass σ ((2 : ℕ) • P)
  exact (BSDCohomology.galoisPointMap_double cmWeierstrass σ P).symm

/-- Group exactness and both equivariant squares on the literal
selected-curve geometric point group, with no additional hypotheses. -/
theorem cmSelectedGeometricKummerShortExact_galois_equivariant :
    (Function.Injective
        (BSDCohomology.twoTorsionInclusion cmWeierstrass)
      ∧
      (BSDCohomology.twoTorsionInclusion cmWeierstrass).range =
        (BSDCohomology.geometricDoubling cmWeierstrass).ker
      ∧
      Function.Surjective
        (BSDCohomology.geometricDoubling cmWeierstrass))
      ∧
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
          (T : BSDCohomology.EllipticTwoTorsion cmWeierstrass),
        BSDCohomology.twoTorsionInclusion cmWeierstrass
          (BSDCohomology.galoisTwoTorsionMap cmWeierstrass σ T) =
        BSDCohomology.galoisPointMap cmWeierstrass σ
          (BSDCohomology.twoTorsionInclusion cmWeierstrass T))
      ∧
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
          (P : BSDCohomology.GeometricPoint cmWeierstrass),
        BSDCohomology.geometricDoubling cmWeierstrass
          (BSDCohomology.galoisPointMap cmWeierstrass σ P) =
        BSDCohomology.galoisPointMap cmWeierstrass σ
          (BSDCohomology.geometricDoubling cmWeierstrass P)) := by
  exact ⟨cmSelectedGeometricKummerShortExact_group,
    cmSelectedGeometricE2Inclusion_galois_equivariant,
    cmSelectedGeometricDoubling_galois_equivariant⟩

end Synthesis.Millennium.BSD
