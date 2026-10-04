import Synthesis.MillenniumBSDCMGaloisRootSignExact
import BSDCohomology.EllipticKummerCocycleAlgebraExact
import Mathlib.Tactic

/-!
# Selected CM curve: literal Galois half-point / E[2] table

The previous owner proves that Galois acts on the selected square roots by one
of four even sign patterns.  The finite E[2] owner identifies those same four
explicit half-points with Q, Q+(0,0), Q+(1,0), Q+(-1,0).

This file performs the same-object weld on the actual Mathlib elliptic-point
group: `galoisPointMap` of the explicit half lies in exactly those four points,
and hence the raw Kummer difference `σQ-Q` is literally one of the four E[2]
points.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

/-- Galois transport of the explicit half is obtained by applying σ to the
three chosen roots and the target coordinates. -/
theorem cmGaloisPointMap_explicitHalf
    (σ : RationalAbsoluteGalois)
    {x y a b c : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y) :
    galoisPointMap cmWeierstrass σ
      (cmExplicitHalfPoint x y a b c ha hb hc habc) =
    cmExplicitHalfPoint
      (σ x) (σ y) (σ a) (σ b) (σ c)
      (by simpa using congrArg σ ha)
      (by simpa using congrArg σ hb)
      (by simpa using congrArg σ hc)
      (by simpa using congrArg σ habc) := by
  simp [galoisPointMap, cmExplicitHalfPoint,
    algClosureHalfX, algClosureHalfY]

/-- The actual Galois image of a non-two-torsion selected half is exactly one
of the four points in the finite E[2] translation table. -/
theorem cmGalois_explicitHalf_point_table
    (σ : RationalAbsoluteGalois)
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y)
    (hx : σ x = x)
    (hy : σ y = y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    galoisPointMap cmWeierstrass σ Q = Q ∨
    galoisPointMap cmWeierstrass σ Q = Q + actualZeroTorsionSubgroupPoint.1 ∨
    galoisPointMap cmWeierstrass σ Q = Q + actualOneTorsionSubgroupPoint.1 ∨
    galoisPointMap cmWeierstrass σ Q = Q + actualMinusOneTorsionSubgroupPoint.1 := by
  dsimp
  rcases cmGalois_half_even_sign_patterns σ hy0 ha hb hc habc hx hy with
      h0 | hbc | hac | hab
  · left
    rw [cmGaloisPointMap_explicitHalf σ ha hb hc habc]
    simp [hx, hy, h0.1, h0.2.1, h0.2.2]
  · right; left
    rw [cmGaloisPointMap_explicitHalf σ ha hb hc habc]
    rw [hx, hy, hbc.1, hbc.2.1, hbc.2.2]
    symm
    exact cmExplicitHalf_flip_bc_eq_add_torsion0 hcurve hy0 ha hb hc habc
  · right; right; left
    rw [cmGaloisPointMap_explicitHalf σ ha hb hc habc]
    rw [hx, hy, hac.1, hac.2.1, hac.2.2]
    symm
    exact cmExplicitHalf_flip_ac_eq_add_torsion1 hcurve hy0 ha hb hc habc
  · right; right; right
    rw [cmGaloisPointMap_explicitHalf σ ha hb hc habc]
    rw [hx, hy, hab.1, hab.2.1, hab.2.2]
    symm
    exact cmExplicitHalf_flip_ab_eq_add_torsionNeg1 hcurve hy0 ha hb hc habc

/-- Pointwise geometric Kummer difference table on the literal elliptic group. -/
theorem cmGalois_explicitHalf_difference_table
    (σ : RationalAbsoluteGalois)
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y)
    (hx : σ x = x)
    (hy : σ y = y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    galoisPointMap cmWeierstrass σ Q - Q = 0 ∨
    galoisPointMap cmWeierstrass σ Q - Q = actualZeroTorsionSubgroupPoint.1 ∨
    galoisPointMap cmWeierstrass σ Q - Q = actualOneTorsionSubgroupPoint.1 ∨
    galoisPointMap cmWeierstrass σ Q - Q = actualMinusOneTorsionSubgroupPoint.1 := by
  dsimp
  rcases cmGalois_explicitHalf_point_table σ hcurve hy0 ha hb hc habc hx hy with
      h0 | h0t | h1t | hnt
  · left
    rw [h0]
    exact sub_self _
  · right; left
    rw [h0t]
    abel
  · right; right; left
    rw [h1t]
    abel
  · right; right; right
    rw [hnt]
    abel

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* `galoisPointMap` is evaluated on the same explicit half used by the finite
  sign table;
* every σ-image is one of Q, Q+T₀, Q+T₁, Q+T₋₁;
* therefore the raw geometric Kummer difference `σQ-Q` is literally one of
  the four actual E[2] points, not merely an abstract sign pair.

NEXT AND ONLY GLOBAL PACKAGING STEP:
identify which of these four rows is selected by the two paid square-class
characters `(χ_x, χ_{x-1})` in the repository's x-T orientation, then transport
the pointwise equality through `cmGenericKummerE2H1MulEquivRatSquareClasses`.
-/

end

end Synthesis.Millennium.BSD
