import BSDCohomology.EllipticPointTopRep

/-!
# First exact half of the elliptic Kummer sequence

On the literal geometric point group E(K̄):

  E[2] = ker([2])

by definition. This file makes the inclusion and doubling homomorphisms
explicit and proves exactness at E(K̄):

  range(E[2] → E(K̄)) = ker([2]).

This is genuine same-curve group theory. The remaining theorem required
for the short exact sequence is surjectivity of [2] on E(K̄), i.e.
divisibility of geometric elliptic points over the algebraic closure.
-/

namespace BSDCohomology

open WeierstrassCurve

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Literal inclusion of the actual doubling kernel into geometric points. -/
def twoTorsionInclusion :
    EllipticTwoTorsion W →+ GeometricPoint W :=
  (EllipticTwoTorsion W).subtype

/-- Literal multiplication-by-two homomorphism on geometric points. -/
def geometricDoubling :
    GeometricPoint W →+ GeometricPoint W :=
  nsmulAddMonoidHom 2

/-- The kernel of literal doubling is definitionally the actual E[2] subgroup. -/
theorem geometricDoubling_kernel :
    (geometricDoubling W).ker = EllipticTwoTorsion W := by
  rfl

/-- The E[2] inclusion is genuinely injective. -/
theorem twoTorsionInclusion_injective :
    Function.Injective (twoTorsionInclusion W) :=
  Subtype.val_injective

/-- Exactness at geometric points:
the image of E[2] is precisely the kernel of multiplication by two. -/
theorem range_twoTorsionInclusion_eq_kernel_doubling :
    (twoTorsionInclusion W).range =
      (geometricDoubling W).ker := by
  ext P
  constructor
  · rintro ⟨Q, rfl⟩
    exact Q.2
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩

/-- Composition is zero, as required by the Kummer complex. -/
theorem doubling_comp_twoTorsionInclusion_zero :
    (geometricDoubling W).comp (twoTorsionInclusion W) = 0 := by
  ext P
  exact P.2

/-!
OPEN KUMMER GEOMETRIC GATE

Need:
  Function.Surjective (geometricDoubling W)

over AlgebraicClosure K.

Once paid, the underlying group sequence
  0 → E[2] → E(K̄) --[2]→ E(K̄) → 0
is short exact. The next step is equivariance/TopRep exactness and then the
continuous-cohomology connecting morphism.
-/

end

end BSDCohomology
