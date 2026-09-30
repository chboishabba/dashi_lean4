import Mathlib
import YangMills.FourDimensionalCompactGroupLinks

/-!
# Actual normalized Haar probability on every finite 4D compact-group link field

For a compact Hausdorff topological group G, the finite periodic 4D
link carrier has the pointwise compact topological group structure.
Mathlib's Haar existence theorem constructs its canonical Haar measure;
normalizing that finite measure yields an honest ProbabilityMeasure.

No independent "some Haar reference law" is selected.  The choice is
Mathlib's native Haar of the FULL link-configuration group G^(links).
This is the finite product-Haar law by the usual Haar uniqueness
principle, but a separate identification proof may be needed if the
CMP119 paper fixes a differently presented link product.

The physical source must still establish the actual CMP119 action on
this same group, continuity/measurability and cutoff-uniform
non-Wilson sector bounds.  The present construction is finite-volume,
not a Yang--Mills continuum measure or an OS theorem.
-/

namespace RequestProject.YangMills

/--
Finite normalized Haar on the literal FOUR-DIMENSIONAL periodic
link configuration group. This construction applies without choosing
a simply connected cover and so respects any global compact-simple
form supplied as `G`.
-/
noncomputable def fourDimensionalNativeLinkHaar
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure (FourDimensionalGroupLinks G L) := by
  let μ : MeasureTheory.Measure (FourDimensionalGroupLinks G L) :=
    MeasureTheory.Measure.haar
  have hfinite : MeasureTheory.IsFiniteMeasure μ :=
    ⟨MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact
      (Set.isCompact_univ)⟩
  let finite :
      MeasureTheory.FiniteMeasure (FourDimensionalGroupLinks G L) :=
    ⟨μ, hfinite⟩
  exact finite.normalize

end RequestProject.YangMills
