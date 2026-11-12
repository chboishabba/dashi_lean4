import Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact
import BSDCohomology.EllipticKummerKernelExact
import Mathlib.Tactic

/-!
# K2: unconditional selected-curve geometric Kummer group exactness

The repository has already separately established BOTH difficult
geometric inputs:
* the kernel of doubling on the genuine selected geometric point
  group is precisely its actual two-torsion subgroup;
* multiplication by two is surjective on the actual selected curve
  over AlgebraicClosure Q, by explicitly constructed half-points.

Here those two facts are joined on the ORIGINAL
BSDCohomology.GeometricPoint cmWeierstrass point carrier.

This pays the underlying abstract-group exact sequence
  0 -> E[2](Qbar) -> E(Qbar) --[2]--> E(Qbar) -> 0.
It does NOT construct the exact sequence in continuous
G_Q-TopRep, H¹ connecting morphisms, naturality at every
completion, or classical Sha(E)[2]. Those are separate K1/K2
gates. No axiom or uninhabited exactness record is used.

Source attribution:
BSDCohomology.EllipticKummerKernelExact and
Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact.
Exact-head pinned local kernel run pending.
-/

namespace Synthesis.Millennium.BSD

/-- Literal injectivity of geometric E[2] into the actual
E(Qbar) point group on the selected y²=x³-x curve. -/
theorem cmSelectedGeometricE2Inclusion_injective :
    Function.Injective
      (BSDCohomology.twoTorsionInclusion cmWeierstrass) :=
  BSDCohomology.twoTorsionInclusion_injective cmWeierstrass

/-- Kernel of the LITERAL geometric doubling homomorphism
equals the range of the actual selected E[2] inclusion. -/
theorem cmSelectedGeometricE2Range_eq_doubleKernel :
    (BSDCohomology.twoTorsionInclusion cmWeierstrass).range =
      (BSDCohomology.geometricDoubling cmWeierstrass).ker :=
  BSDCohomology.range_twoTorsionInclusion_eq_kernel_doubling
    cmWeierstrass

/-- Algebraic-closure doubling has an ACTUAL pointwise half
on the selected curve, not an assumed divisible carrier. -/
theorem cmSelectedGeometricDoubling_onto :
    Function.Surjective
      (BSDCohomology.geometricDoubling cmWeierstrass) :=
  cmGeometricDoubling_surjective

/-- The FULL point-group short exact Kummer sequence for
E : y²=x³−x over Qbar, with all three maps tied to the
existing genuine geometric coefficient objects. -/
theorem cmSelectedGeometricKummerShortExact_group :
    Function.Injective
        (BSDCohomology.twoTorsionInclusion cmWeierstrass)
      ∧
      (BSDCohomology.twoTorsionInclusion cmWeierstrass).range =
        (BSDCohomology.geometricDoubling cmWeierstrass).ker
      ∧
      Function.Surjective
        (BSDCohomology.geometricDoubling cmWeierstrass) :=
  ⟨cmSelectedGeometricE2Inclusion_injective,
    cmSelectedGeometricE2Range_eq_doubleKernel,
    cmSelectedGeometricDoubling_onto⟩

end Synthesis.Millennium.BSD
