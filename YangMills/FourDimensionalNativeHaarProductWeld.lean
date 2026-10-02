import Mathlib
import YangMills.FourDimensionalCompactGroupHaar
import YangMills.FourDimensionalNativeHaarReflectionMaxCut

/-!
# Native whole-link Haar equals finite product Haar

For a compact Hausdorff topological group G, the literal finite 4D link field is
a finite dependent function space.  This file gives the explicit probability
law intended by lattice gauge theory:

  product over sites x, product over directions mu, normalized Haar(dU_{x,mu}).

The identification with the repository's pre-existing
fourDimensionalNativeLinkHaar is made by compact-group Haar uniqueness:
the product law is finite and left invariant, hence proportional to whole-link
Haar; both laws have total mass one, so the proportionality scalar is one.

This is the A1 same-object theorem needed before reflection invariance is
proved by reindexing and inversion coordinatewise.
-/

namespace RequestProject.YangMills

/-- Normalized Haar probability on one compact-group link variable. -/
noncomputable def compactGroupNativeHaar
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    MeasureTheory.ProbabilityMeasure G := by
  let μ : MeasureTheory.Measure G := MeasureTheory.Measure.haar
  have hfinite : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  let finite : MeasureTheory.FiniteMeasure G := ⟨μ, hfinite⟩
  exact finite.normalize

/--
The literal finite product Haar law on the curried link carrier
  site -> direction -> G.
No equivalence or reshaping of the physical link field is involved.
-/
noncomputable def fourDimensionalProductLinkHaar
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure (FourDimensionalGroupLinks G L) :=
  MeasureTheory.ProbabilityMeasure.pi
    (fun _ : FourDimensionalTorusSite L =>
      MeasureTheory.ProbabilityMeasure.pi
        (fun _ : Fin 4 => compactGroupNativeHaar G))

/--
A reusable one-link leaf: normalized compact Haar is invariant under every left
translation.  This is deliberately separated from the product argument.
-/
def CompactGroupNormalizedHaarLeftInvariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  ∀ g : G,
    MeasureTheory.Measure.map (fun x : G => g * x)
      (((compactGroupNativeHaar G :
        MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G))
    =
      (((compactGroupNativeHaar G :
        MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G))

/--
Finite nested products preserve coordinatewise left invariance.

This theorem contains no Yang--Mills dynamics; it is the exact measure-theory
compiler from one-link normalized Haar invariance to the literal whole-link
product law.
-/
theorem four_dimensional_product_link_haar_left_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L]
    (hSingle : CompactGroupNormalizedHaarLeftInvariant G)
    (g : FourDimensionalGroupLinks G L) :
    MeasureTheory.Measure.map (fun U => g * U)
      (((fourDimensionalProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)))
    =
      (((fourDimensionalProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)) := by
  classical
  -- Expose the nested finite products and push the pointwise multiplication
  -- through them one coordinate family at a time.
  change
    MeasureTheory.Measure.map
      (fun U x μ => g x μ * U x μ)
      (MeasureTheory.Measure.pi
        (fun _ : FourDimensionalTorusSite L =>
          MeasureTheory.Measure.pi
            (fun _ : Fin 4 =>
              (((compactGroupNativeHaar G :
                MeasureTheory.ProbabilityMeasure G) :
                MeasureTheory.Measure G)))))
    =
    MeasureTheory.Measure.pi
      (fun _ : FourDimensionalTorusSite L =>
        MeasureTheory.Measure.pi
          (fun _ : Fin 4 =>
            (((compactGroupNativeHaar G :
              MeasureTheory.ProbabilityMeasure G) :
              MeasureTheory.Measure G))))
  rw [MeasureTheory.Measure.pi_map_pi]
  · congr with x
    rw [MeasureTheory.Measure.pi_map_pi]
    · congr with μ
      exact hSingle (g x μ)
    · intro μ
      exact (measurable_const.mul measurable_id).aemeasurable
  · intro x
    exact (measurable_pi_lambda _ fun μ => measurable_const.mul
      (measurable_apply μ)).aemeasurable

/--
A compact-group left-invariant probability law on the literal whole-link
carrier is exactly the repository native whole-link Haar law.

The proof uses compact-space Haar uniqueness plus normalization; no statement
about reflection or Wilson weights enters.
-/
theorem four_dimensional_native_haar_eq_product_haar
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L]
    (hSingle : CompactGroupNormalizedHaarLeftInvariant G) :
    (((fourDimensionalNativeLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)))
    =
    (((fourDimensionalProductLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)) := by
  let ν : MeasureTheory.Measure (FourDimensionalGroupLinks G L) :=
    ((fourDimensionalProductLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L))
  let μ : MeasureTheory.Measure (FourDimensionalGroupLinks G L) :=
    ((fourDimensionalNativeLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L))
  letI : MeasureTheory.Measure.IsMulLeftInvariant ν :=
    ⟨fun g => four_dimensional_product_link_haar_left_invariant
      G L hSingle g⟩
  have hνFinite : MeasureTheory.IsFiniteMeasureOnCompacts ν := by infer_instance
  have hμHaar : MeasureTheory.Measure.IsHaarMeasure μ := by infer_instance
  have hscale :=
    MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  have hmass := congrArg (fun ρ : MeasureTheory.Measure
      (FourDimensionalGroupLinks G L) => ρ Set.univ) hscale
  have hscalar :
      MeasureTheory.Measure.haarScalarFactor ν μ = 1 := by
    simpa [ν, μ] using hmass
  rw [hscale, hscalar, one_smul]
  rfl

end RequestProject.YangMills
