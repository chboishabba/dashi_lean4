import Synthesis.MillenniumBSDCMGeometricKummerGroupExact
import BSDCohomology.EllipticKummerTopRepMapsExact

/-!
# Selected CM curve: exact Kummer sequence on the actual TopRep morphisms

The previous two owners establish, on the same literal geometric point objects:

* underlying additive-group exactness of
    E[2] -> E(Qbar) ->[2] E(Qbar),
* and equivariant continuous TopRep morphisms for those exact same maps.

This file transports the three point-set exactness facts to the coercions of
those TopRep morphisms.  It deliberately does not claim a long exact sequence:
current Mathlib continuous cohomology still lists the short-exact -> long-exact
construction as TODO.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- The actual TopRep inclusion is injective on its literal carrier. -/
theorem cmKummerTopRep_inclusion_injective :
    Function.Injective
      (BSDCohomology.twoTorsionInclusionTopRep cmWeierstrass) := by
  intro P Q h
  apply Subtype.ext
  exact h

/-- The range of the actual TopRep inclusion is exactly the kernel of the
actual TopRep doubling morphism, stated pointwise on the shared carrier. -/
theorem cmKummerTopRep_range_eq_kernel :
    Set.range
        (BSDCohomology.twoTorsionInclusionTopRep cmWeierstrass)
      =
    {P : BSDCohomology.GeometricPoint cmWeierstrass |
      BSDCohomology.geometricDoublingTopRep cmWeierstrass P = 0} := by
  ext P
  constructor
  · rintro ⟨T, rfl⟩
    simp
  · intro hP
    change (2 : ℕ) • P = 0 at hP
    exact ⟨⟨P, hP⟩, rfl⟩

/-- Multiplication by two as the actual TopRep morphism is surjective for the
selected CM curve over Qbar. -/
theorem cmKummerTopRep_doubling_surjective :
    Function.Surjective
      (BSDCohomology.geometricDoublingTopRep cmWeierstrass) := by
  intro P
  obtain ⟨Q, hQ⟩ := cmGeometricKummer_doubling_surjective P
  exact ⟨Q, hQ⟩

/-- Point-set short exactness receipt on the exact morphisms living in TopRep. -/
theorem cmKummerTopRep_exact :
    Function.Injective
        (BSDCohomology.twoTorsionInclusionTopRep cmWeierstrass) ∧
      Set.range
          (BSDCohomology.twoTorsionInclusionTopRep cmWeierstrass)
        =
          {P : BSDCohomology.GeometricPoint cmWeierstrass |
            BSDCohomology.geometricDoublingTopRep cmWeierstrass P = 0} ∧
      Function.Surjective
        (BSDCohomology.geometricDoublingTopRep cmWeierstrass) := by
  exact ⟨
    cmKummerTopRep_inclusion_injective,
    cmKummerTopRep_range_eq_kernel,
    cmKummerTopRep_doubling_surjective
  ⟩

/-!
MAX-CUT STATUS

PAID:
* exact same E[2] and E(Qbar) continuous Galois representations;
* actual TopRep inclusion and doubling maps;
* zero composition;
* injectivity, exact middle kernel/range, and surjectivity on those exact maps
  for the selected CM regression curve.

NEXT STANDARD BRIDGE:
* construct the degree-one Kummer cocycle directly from a chosen geometric half
  Q of P via sigma |-> sigma(Q)-Q;
* prove continuity using the Krull-topology open-stabilizer theorem;
* prove independence of half choice and compatibility with the already-paid
  H1 <-> rational-square-class comparison;
* prove localization naturality place by place.

The absence of a generic continuous-cohomology long-exact-sequence API is kept
as a library boundary, not replaced by a synthetic exact-sequence theorem.
-/

end

end Synthesis.Millennium.BSD
