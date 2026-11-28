import Mathlib
import YangMills.LiteralSU2CompactQuaternionHaar

open MeasureTheory

/-!
# Canonical finite product Haar on the literal SU(2) link carrier

The selected finite Gibbs construction previously accepted an arbitrary
probability measure as its reference law.  For the physical lattice route the
reference is canonical: independent normalized Haar on every literal SU(2)
link.  This file constructs exactly that law on the existing curried
four-dimensional link carrier, without introducing a second group or field
representation.
-/

namespace RequestProject.YangMills

/--
Independent normalized literal SU(2) Haar on every site-direction link.
This is the exact finite product law intended by the lattice path integral.
-/
noncomputable def literalSU2ProductLinkHaar
    (L : ℕ) [NeZero L] :
    ProbabilityMeasure (SU2TorusLinks L) :=
  ProbabilityMeasure.pi
    (fun _ : SU2TorusSite L =>
      ProbabilityMeasure.pi
        (fun _ : Fin 4 => literalSU2OneLinkHaar))

/-- The underlying measure is definitionally the nested finite product Haar. -/
theorem literal_su2_product_link_haar_toMeasure
    (L : ℕ) [NeZero L] :
    (((literalSU2ProductLinkHaar L : ProbabilityMeasure (SU2TorusLinks L)) :
      Measure (SU2TorusLinks L))) =
      Measure.pi (fun _ : SU2TorusSite L =>
        Measure.pi (fun _ : Fin 4 =>
          (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
            Measure SU2PlaquetteHolonomy)))) := by
  rfl

end RequestProject.YangMills
