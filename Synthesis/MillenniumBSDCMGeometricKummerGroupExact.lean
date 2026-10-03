import Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact
import BSDCohomology.EllipticKummerKernelExact

/-!
# Selected CM curve: unconditional geometric Kummer group exactness

The previous owner proves literal surjectivity of multiplication by two on the
selected curve over `AlgebraicClosure ℚ`.  The generic Kummer-kernel owner
already proves injectivity of `E[2] → E(Qbar)` and identifies its range with
the kernel of doubling.  This file combines those same-object theorems.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

/-- All three underlying-group exactness facts for the selected CM curve. -/
theorem cmGeometricKummer_group_exact :
    Function.Injective
        (BSDCohomology.twoTorsionInclusion cmWeierstrass) ∧
      (BSDCohomology.twoTorsionInclusion cmWeierstrass).range =
        (BSDCohomology.geometricDoubling cmWeierstrass).ker ∧
      Function.Surjective
        (BSDCohomology.geometricDoubling cmWeierstrass) := by
  exact ⟨
    BSDCohomology.twoTorsionInclusion_injective cmWeierstrass,
    BSDCohomology.range_twoTorsionInclusion_eq_kernel_doubling cmWeierstrass,
    cmGeometricDoubling_surjective
  ⟩

/-- The selected geometric Kummer sequence is therefore a genuine short exact
sequence at the underlying additive-group level.  The next unpaid property is
equivariance/continuity, not point-group exactness. -/
theorem cmGeometricKummer_doubling_surjective :
    Function.Surjective
      (BSDCohomology.geometricDoubling cmWeierstrass) :=
  cmGeometricKummer_group_exact.2.2

/-!
NEXT MAX-CUT

Lift these exact maps to morphisms between the already-existing continuous
Galois representations:

  E[2] → E(Qbar) →[2] E(Qbar),

prove the same kernel/range/surjectivity facts there, then instantiate the
continuous-cohomology connecting morphism and prove localization naturality.
-/

end Synthesis.Millennium.BSD
