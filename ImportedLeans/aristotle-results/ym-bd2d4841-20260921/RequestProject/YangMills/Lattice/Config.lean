/-
# The literal lattice gauge configuration space and its symmetries

The configuration space of a lattice gauge theory with compact gauge group `G`
and link set `ι` is `ι → G`, carrying the product of the normalised Haar
measures.  Two families of transformations act on it and are used below:

* a relabelling of the links by a permutation (used for lattice translations);
* a two-sided translation of each link variable (used for gauge
  transformations).

Both preserve the product Haar measure, and this is proved here, from
`CompactHaar`, with no appeal to any external input.
-/
import Mathlib
import RequestProject.YangMills.Lattice.CompactHaar

namespace RequestProject.YangMills.Lattice

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The product of normalised Haar measures on the space of link
configurations. -/
noncomputable def prodHaar (ι : Type*) [Fintype ι] (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Measure (ι → G) :=
  Measure.pi fun _ => haarProb G

variable {ι : Type*} [Fintype ι]

instance prodHaar.isProbabilityMeasure : IsProbabilityMeasure (prodHaar ι G) := by
  unfold prodHaar; infer_instance

/-- Relabelling the links by a permutation preserves the product Haar
measure. -/
theorem measurePreserving_reindex (e : Equiv.Perm ι) :
    MeasurePreserving (fun (U : ι → G) => fun i => U (e i)) (prodHaar ι G) (prodHaar ι G) := by
  have h := measurePreserving_piCongrLeft (fun _ : ι => haarProb G) e.symm
  have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => G) e.symm))
      = fun (U : ι → G) => fun i => U (e i) := by
    funext U i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  rw [hfun] at h
  exact h

/-- A two-sided translation of every link variable preserves the product Haar
measure.  This is the measure-theoretic content of gauge invariance of the
lattice measure. -/
theorem measurePreserving_translate (a b : ι → G) :
    MeasurePreserving (fun (U : ι → G) => fun i => a i * U i * b i)
      (prodHaar ι G) (prodHaar ι G) :=
  measurePreserving_pi (fun _ => haarProb G) (fun _ => haarProb G)
    (fun i => measurePreserving_mul_left_mul_right (a i) (b i))

/-- The general symmetry of the lattice measure: relabel the links and translate
each variable on both sides. -/
theorem measurePreserving_translate_reindex (e : Equiv.Perm ι) (a b : ι → G) :
    MeasurePreserving (fun (U : ι → G) => fun i => a i * U (e i) * b i)
      (prodHaar ι G) (prodHaar ι G) :=
  (measurePreserving_translate a b).comp (measurePreserving_reindex e)

end RequestProject.YangMills.Lattice
