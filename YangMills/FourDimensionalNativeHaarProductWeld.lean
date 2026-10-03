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
The first one-link Haar leaf is unconditional: normalizing a nonzero left Haar
measure only rescales it, so left-translation invariance survives exactly.
-/
theorem compact_group_native_haar_left_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    CompactGroupNormalizedHaarLeftInvariant G := by
  let μ : MeasureTheory.Measure G := MeasureTheory.Measure.haar
  let finite : MeasureTheory.FiniteMeasure G := ⟨μ, by infer_instance⟩
  have hμ : μ ≠ 0 := NeZero.ne μ
  have hfinite : finite ≠ 0 := by
    intro h
    apply hμ
    have h' := congrArg
      (fun ν : MeasureTheory.FiniteMeasure G =>
        (ν : MeasureTheory.Measure G)) h
    simpa [finite, μ] using h'
  intro g
  change MeasureTheory.Measure.map (fun x : G => g * x)
      ((finite.normalize : MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G)
    =
      ((finite.normalize : MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G)
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite]
  rw [MeasureTheory.Measure.map_smul,
    MeasureTheory.map_mul_left_eq_self]
  exact (measurable_const.mul measurable_id).aemeasurable

/--
Probability normalization removes the scalar ambiguity between finite
left-invariant measures.  This is the compact-group uniqueness form needed to
turn right translates of normalized Haar back into the same probability law.
-/
theorem compact_group_left_invariant_probability_unique
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ ν : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν]
    [MeasureTheory.Measure.IsMulLeftInvariant μ]
    [MeasureTheory.Measure.IsMulLeftInvariant ν] :
    μ = ν := by
  ext s hs
  have h := MeasureTheory.measure_mul_measure_eq
    μ ν Set.univ s (by simp) (by simp)
  simpa using h

/--
Normalized Haar on a compact group is also right invariant.  The proof does
not assume commutativity: a right translate of a left-invariant probability
measure is again left invariant, and probability-normalized left Haar is
unique.
-/
theorem compact_group_native_haar_right_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] :
    MeasureTheory.Measure.IsMulRightInvariant
      (((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
        MeasureTheory.Measure G)) := by
  let μ : MeasureTheory.Measure G :=
    ((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G)
  letI : MeasureTheory.Measure.IsMulLeftInvariant μ :=
    ⟨compact_group_native_haar_left_invariant G⟩
  constructor
  intro g
  let ν : MeasureTheory.Measure G :=
    MeasureTheory.Measure.map (fun x : G => x * g) μ
  letI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : MeasureTheory.Measure.IsMulLeftInvariant ν := by
    dsimp [ν]
    infer_instance
  exact compact_group_left_invariant_probability_unique ν μ

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

/-- A1 with its one-link Haar premise discharged. -/
theorem four_dimensional_native_haar_eq_product_haar_closed
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    (((fourDimensionalNativeLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)))
    =
    (((fourDimensionalProductLinkHaar G L :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)) :=
  four_dimensional_native_haar_eq_product_haar
    G L (compact_group_native_haar_left_invariant G)

end RequestProject.YangMills
