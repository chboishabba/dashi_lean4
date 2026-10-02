import BSDCohomology.EllipticKummerKernelExact
import Mathlib.GroupTheory.Divisible
import Mathlib.Tactic

/-!
# BSD max-cut: reduce the geometric Kummer gate to actual divisibility

The Kummer owner already proves the kernel half of

  0 → E[2] → E(K̄) --[2]→ E(K̄).

The remaining group-theoretic gate is surjectivity of multiplication by two.
Mathlib's standard constructive interface for exactly this property is
`DivisibleBy`.

This file does not assume elliptic divisibility globally.  It proves that once
the genuine geometric point group has the standard natural-number divisibility
structure, the missing [2]-surjectivity theorem follows immediately on the
literal same-curve `GeometricPoint W` carrier.
-/

namespace BSDCohomology

open WeierstrassCurve

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Natural-number divisibility of the actual geometric point group pays the
literal multiplication-by-two surjectivity gate. -/
theorem geometricDoubling_surjective_of_divisible
    [DivisibleBy (GeometricPoint W) ℕ] :
    Function.Surjective (geometricDoubling W) := by
  simpa [geometricDoubling] using
    (DivisibleBy.surjective_smul
      (A := GeometricPoint W) (α := ℕ)
      (show (2 : ℕ) ≠ 0 by norm_num))

/-- Under genuine divisibility, the group-level Kummer sequence has all three
required elementary exactness facts: injective left map, exact middle, and
surjective doubling. -/
theorem geometricKummer_group_exact_of_divisible
    [DivisibleBy (GeometricPoint W) ℕ] :
    Function.Injective (twoTorsionInclusion W) ∧
    (twoTorsionInclusion W).range = (geometricDoubling W).ker ∧
    Function.Surjective (geometricDoubling W) := by
  exact ⟨
    twoTorsionInclusion_injective W,
    range_twoTorsionInclusion_eq_kernel_doubling W,
    geometricDoubling_surjective_of_divisible W
  ⟩

/-!
MAX-CUT BOUNDARY

PAID:
* the exact consumer theorem from Mathlib's standard `DivisibleBy` property
  to the literal geometric [2]-surjectivity target;
* the complete underlying-group short-exactness package conditional only on
  actual divisibility of `GeometricPoint W`.

STILL OPEN MATHEMATICS:
* construct `DivisibleBy (GeometricPoint W) ℕ` over an algebraically closed
  field (or prove the n=2 case directly) from elliptic-curve geometry;
* lift the short exact sequence to equivariant TopRep coefficient objects;
* continuous-H¹ connecting morphism and localization naturality.

This is a reduction theorem, not a replacement for geometric divisibility.
-/

end

end BSDCohomology
