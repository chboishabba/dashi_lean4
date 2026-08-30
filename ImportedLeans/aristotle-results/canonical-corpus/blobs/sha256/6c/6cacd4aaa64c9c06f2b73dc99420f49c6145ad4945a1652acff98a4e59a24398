import Mathlib
import RequestProject.PaletteUniversality
import RequestProject.UltrametricTaxonomy

/-!
# Best views, and the taxonomy tree they carry

`RequestProject/PaletteUniversality.lean` proves that high above the real axis every
normalised `q`-series paints the *same* plate: up there the picture is a function of the
height alone and the forms are indistinguishable.  This file is about the opposite
question, the one the gallery asks of the LMFDB: *which view of a form shows the most?*

A **view** is the finite sample `V ⊆ ℂ` of the upper half plane that a plate reads.  Two
readers are *indistinguishable at* `V` when they paint every sample of `V` with the same
palette rank, and the **palette distance** `viewDist V f g` counts the samples at which
they differ.  Given a finite family of readers, the **separation score** `sepScore F V`
counts the ordered pairs the view tells apart, and a **best view** is one maximising it.

What is proved here:

* `viewDist_comm`, `viewDist_self`, `viewDist_triangle`, `viewDist_eq_zero_iff` — the
  palette distance is a pseudometric, and it vanishes exactly on indistinguishable pairs;
* `sepScore_eq_zero_of_deep` — **a deep view is blind**: if every reader is a normalised
  `q`-series with a common coefficient bound and the view sits above `qHeight C k δ` with
  its heights `δ`-separated, then the score is zero and the tree degenerates to a single
  group (`deep_cluster_eq_univ`).  This is the universality theorem read as a statement
  about views;
* `exists_bestView` — over any finite non-empty list of candidate views a best view
  exists;
* `bestView_not_deep` — as soon as *some* candidate view separates *some* pair, the best
  view is not a deep one: the search is forced down towards the real axis, which is
  exactly what the search over the LMFDB sample finds;
* `palette_tree_laminar`, `palette_cluster_monochrome`, `palette_slink_ultra` — feeding
  the palette distances at the best view into `UltrametricTaxonomy` gives a genuine tree
  of the forms: the groups at all thresholds are pairwise nested or disjoint, the chain
  distance is an ultrametric, and any arithmetic invariant that cannot change across a
  short palette step is constant on every group, i.e. the tree refines that
  classification.
-/

namespace PaletteTaxonomy

open PaletteUniversality UltrametricTaxonomy
open scoped Classical

/-- A **view**: the finite sample of the upper half plane that a plate reads. -/
abbrev View := Finset ℂ

/-! ### Indistinguishability and the palette distance -/

/-- Two readers are indistinguishable at a view when they paint every sample of it with
the same rank. -/
def Indist (f g : ℂ → ℂ) (V : View) : Prop :=
  ∀ z ∈ V, paletteRank f V z = paletteRank g V z

/-- The **palette distance** at a view: the number of samples painted differently. -/
noncomputable def viewDist (V : View) (f g : ℂ → ℂ) : ℕ :=
  (V.filter fun z => paletteRank f V z ≠ paletteRank g V z).card

theorem viewDist_self (V : View) (f : ℂ → ℂ) : viewDist V f f = 0 := by
  simp [viewDist]

theorem viewDist_comm (V : View) (f g : ℂ → ℂ) : viewDist V f g = viewDist V g f := by
  unfold viewDist
  congr 1
  apply Finset.filter_congr
  intro z _
  exact ⟨fun h he => h he.symm, fun h he => h he.symm⟩

theorem viewDist_triangle (V : View) (f g h : ℂ → ℂ) :
    viewDist V f h ≤ viewDist V f g + viewDist V g h := by
  classical
  have hsub : (V.filter fun z => paletteRank f V z ≠ paletteRank h V z) ⊆
      (V.filter fun z => paletteRank f V z ≠ paletteRank g V z) ∪
        (V.filter fun z => paletteRank g V z ≠ paletteRank h V z) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_union] at hz ⊢
    by_cases hfg : paletteRank f V z = paletteRank g V z
    · exact Or.inr ⟨hz.1, fun hgh => hz.2 (hfg.trans hgh)⟩
    · exact Or.inl ⟨hz.1, hfg⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem viewDist_eq_zero_iff {V : View} {f g : ℂ → ℂ} :
    viewDist V f g = 0 ↔ Indist f g V := by
  unfold viewDist Indist
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h z hz => not_not.1 (h hz), fun h z hz => not_not.2 (h z hz)⟩

/-! ### Deep views are blind -/

/-- A view is **deep** for the data `C, k, δ` when all its samples lie above the
universality height and their heights are `δ`-separated. -/
def DeepView (C : ℝ) (k : ℕ) (δ : ℝ) (V : View) : Prop :=
  (∀ z ∈ V, qHeight C k δ ≤ z.im) ∧ ∀ z ∈ V, ∀ w ∈ V, z ≠ w → δ ≤ |z.im - w.im|

/-- **Up there, everything is the same picture.**  At a deep view any two normalised
`q`-series are indistinguishable. -/
theorem indist_of_deep {a b : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k)
    (hb : Normalized b C k) {δ : ℝ} (hδ : 0 < δ) {V : View} (hV : DeepView C k δ V) :
    Indist (qSeries a) (qSeries b) V := fun _ hz =>
  paletteRank_eq_of_normalized ha hb hδ hV.1 hV.2 hz

theorem viewDist_eq_zero_of_deep {a b : ℕ → ℂ} {C : ℝ} {k : ℕ} (ha : Normalized a C k)
    (hb : Normalized b C k) {δ : ℝ} (hδ : 0 < δ) {V : View} (hV : DeepView C k δ V) :
    viewDist V (qSeries a) (qSeries b) = 0 :=
  viewDist_eq_zero_iff.2 (indist_of_deep ha hb hδ hV)

/-! ### Searching for the best view -/

variable {ι : Type*} [Fintype ι]

/-- The **separation score** of a view for a family of readers: the number of ordered
pairs it tells apart. -/
noncomputable def sepScore (F : ι → ℂ → ℂ) (V : View) : ℕ :=
  (Finset.univ.filter fun p : ι × ι => ¬ Indist (F p.1) (F p.2) V).card

/-- A **best view** in a finite catalogue of candidate views: one of maximal score. -/
def IsBestView (F : ι → ℂ → ℂ) (𝒱 : Finset View) (V : View) : Prop :=
  V ∈ 𝒱 ∧ ∀ W ∈ 𝒱, sepScore F W ≤ sepScore F V

/-- **The search terminates.**  Over a finite non-empty catalogue of views a best view
exists. -/
theorem exists_bestView (F : ι → ℂ → ℂ) {𝒱 : Finset View} (h𝒱 : 𝒱.Nonempty) :
    ∃ V, IsBestView F 𝒱 V := by
  obtain ⟨V, hV, hmax⟩ := Finset.exists_max_image 𝒱 (sepScore F) h𝒱
  exact ⟨V, hV, hmax⟩

/-- **A deep view scores nothing.**  If every reader of the family is a normalised
`q`-series with the same coefficient bound, a deep view separates no pair at all. -/
theorem sepScore_eq_zero_of_deep {a : ι → ℕ → ℂ} {C : ℝ} {k : ℕ}
    (ha : ∀ i, Normalized (a i) C k) {δ : ℝ} (hδ : 0 < δ) {V : View}
    (hV : DeepView C k δ V) : sepScore (fun i => qSeries (a i)) V = 0 := by
  unfold sepScore
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  simpa using indist_of_deep (ha p.1) (ha p.2) hδ hV

/-- **The best view is never a deep one** — provided some candidate view sees a
difference at all.  This is the reason the search over the LMFDB sample runs away from
the cusp: high up there is nothing to see. -/
theorem bestView_not_deep {a : ι → ℕ → ℂ} {C : ℝ} {k : ℕ}
    (ha : ∀ i, Normalized (a i) C k) {δ : ℝ} (hδ : 0 < δ) {𝒱 : Finset View} {V : View}
    (hbest : IsBestView (fun i => qSeries (a i)) 𝒱 V)
    {W : View} (hW : W ∈ 𝒱) {i j : ι} (hsep : ¬ Indist (qSeries (a i)) (qSeries (a j)) W) :
    ¬ DeepView C k δ V := by
  intro hdeep
  have hzero : sepScore (fun i => qSeries (a i)) V = 0 :=
    sepScore_eq_zero_of_deep ha hδ hdeep
  have hpos : 0 < sepScore (fun i => qSeries (a i)) W := by
    refine Finset.card_pos.2 ⟨(i, j), ?_⟩
    simpa using hsep
  exact absurd (hbest.2 W hW) (by omega)

/-! ### The tree of the forms at a view -/

/-- The table of palette distances of a family of readers at a view: the input of the
taxonomy. -/
noncomputable def palTable (V : View) (F : ι → ℂ → ℂ) : ι → ι → ℕ :=
  fun i j => viewDist V (F i) (F j)

omit [Fintype ι] in
theorem palTable_symm (V : View) (F : ι → ℂ → ℂ) (i j : ι) :
    palTable V F i j = palTable V F j i := viewDist_comm V (F i) (F j)

/-- The taxonomy tree of the family at a view: the group of `i` at threshold `t` is
everything reachable from `i` by steps of palette distance at most `t`. -/
noncomputable def palCluster (V : View) (F : ι → ℂ → ℂ) (t : ℕ) (i : ι) : Finset ι :=
  cluster (palTable V F) t i

/-- **The chain distance of the palette table is an ultrametric.** -/
theorem palette_slink_ultra (V : View) (F : ι → ℂ → ℂ) (i j k : ι) :
    slink (palTable V F) i k ≤
      max (slink (palTable V F) i j) (slink (palTable V F) j k) :=
  slink_ultra _ i j k

/-- **The groups form a tree.**  Any two groups of the taxonomy, at any two thresholds,
are nested or disjoint. -/
theorem palette_tree_laminar (V : View) (F : ι → ℂ → ℂ) (t s : ℕ) (i j : ι) :
    Disjoint (palCluster V F t i) (palCluster V F s j) ∨
      palCluster V F t i ⊆ palCluster V F s j ∨
        palCluster V F s j ⊆ palCluster V F t i :=
  cluster_laminar (palTable_symm V F) t s i j

/-- **The tree refines the arithmetic.**  If an invariant of the forms — the weight, the
level, having complex multiplication — cannot change between two forms whose plates
differ at at most `t` samples, then it is constant on every group of the taxonomy at
threshold `t`. -/
theorem palette_cluster_monochrome {κ : Type*} (V : View) (F : ι → ℂ → ℂ) (inv : ι → κ)
    {t : ℕ} (h : ∀ i j : ι, viewDist V (F i) (F j) ≤ t → inv i = inv j) (i : ι) :
    ∀ j ∈ palCluster V F t i, inv j = inv i :=
  cluster_monochrome inv h i

/-- **A deep view has no taxonomy.**  At a deep view all the palette distances vanish, so
already at threshold `0` there is a single group: the tree is a stump. -/
theorem deep_cluster_eq_univ {a : ι → ℕ → ℂ} {C : ℝ} {k : ℕ}
    (ha : ∀ i, Normalized (a i) C k) {δ : ℝ} (hδ : 0 < δ) {V : View}
    (hV : DeepView C k δ V) (i : ι) :
    palCluster V (fun i => qSeries (a i)) 0 i = Finset.univ := by
  ext x
  simp only [palCluster, mem_cluster, Finset.mem_univ, iff_true]
  refine slink_le_of_linked (Linked.single ?_)
  simpa [palTable] using
    (viewDist_eq_zero_of_deep (ha i) (ha x) hδ hV).le

end PaletteTaxonomy
