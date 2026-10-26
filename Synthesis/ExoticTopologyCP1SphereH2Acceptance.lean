import Synthesis.ExoticTopologyCP1TopCatSphereWeld
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The smallest source-sensitive CP¹ rational singular H₂ acceptance theorem

The real `CP1 ≃ₜ TopCat.sphere 2` and its literal singular H₂ functor
transport are paid by ExoticTopologyCP1TopCatSphereWeld.

The remaining positive input is SINGLE and exactly on the correct
object: a rational sphere singular-H₂ computation, expressed as an
isomorphism in ModuleCat ℚ to its coefficient object.
From such an input we derive the corresponding CP1 result without
another projective, categorical, or cellular comparison.

Hatcher-at: Jack McCarthy's theorem
`Hatcher.Sphere.reducedHomology_sphere` is a promising SOURCE.
But it computes REDUCED homology on a different Mathlib revision, so
the required positive-degree reduced-to-ordinary comparison and
dual-environment kernel certificate are NOT claimed here.
-/

namespace Synthesis.ExoticTopology

open CategoryTheory
open AlgebraicTopology
open Synthesis.Millennium.Hodge

noncomputable abbrev LiteralSphere2RationalH2 : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).obj (TopCat.sphere 2)

/-- The missing input names the literal sphere, the correct degree,
    and the correct coefficient category. Not a generic `Set` token. -/
def SourceSphereH2Q : Prop :=
  Nonempty (LiteralSphere2RationalH2 ≅ rationalCoefficientObject)

/-- Exact application of the already-owned functorial CP¹↔sphere isomorphism.
    No CW comparison or Hatcher import is introduced. -/
theorem cp1SingularH2Q_of_literalSphereSource
    (h : SourceSphereH2Q) :
    Nonempty (cp1SingularH2 ≅ rationalCoefficientObject) := by
  rcases h with ⟨iso⟩
  exact ⟨cp1SingularH2IsoTopCatSphere2 ≪≫ iso⟩

end Synthesis.ExoticTopology
