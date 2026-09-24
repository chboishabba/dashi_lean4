import Mathlib

/-!
# Chain distances, ultrametrics and the tree they carry

A taxonomy is a *tree*: a family of groups in which any two groups are either nested or
disjoint.  This file builds, and certifies, the tree that a table of pairwise distances
gives rise to — the classical single-linkage (nearest-neighbour) hierarchy.

Fix a finite set `ι` of objects and a table `d : ι → ι → ℕ` of pairwise distances (no
axioms are asked of `d`: it need not be symmetric, and need not satisfy any triangle
inequality).  Say that `i` and `j` are `Linked d t` when one can walk from `i` to `j` in
steps each of cost at most `t`, and let the **chain distance** `slink d i j` be the least
`t` for which that is possible.  Then

* `slink_le_dist`     : `slink d i j ≤ d i j`;
* `slink_ultra`       : `slink d i k ≤ max (slink d i j) (slink d j k)` — the strong
                        (ultrametric) triangle inequality;
* `slink_symm`        : `slink` is symmetric as soon as `d` is;
* `le_slink_of_ultra` : `slink d` is the **largest** ultrametric below `d`, i.e. the
                        subdominant ultrametric;
* `cluster_laminar`   : the level sets `cluster d t i = {j | slink d i j ≤ t}`, taken over
                        all thresholds `t` and all objects `i`, form a *laminar family*:
                        any two of them are nested or disjoint.  This is exactly the
                        statement that the level sets are the nodes of a tree;
* `cluster_top`       : at a large enough threshold there is a single group, the root;
* `cluster_bot`       : at threshold `0`, when no two distinct objects are at distance
                        zero, the groups are the leaves;
* `cluster_monochrome`: if some invariant `inv` is constant on every pair at distance at
                        most `t`, then every group at threshold `t` is `inv`-monochrome —
                        the computed tree refines the classification by `inv`.

`RequestProject/PaletteTaxonomy.lean` feeds the palette distances of modular forms into
this machinery.
-/

namespace UltrametricTaxonomy

open Finset

variable {ι : Type*} [Fintype ι] {d : ι → ι → ℕ} {i j k : ι} {s t : ℕ}

/-! ### Linking at a threshold -/

/-- `Linked d t i j`: one can walk from `i` to `j` in steps of cost at most `t`. -/
def Linked (d : ι → ι → ℕ) (t : ℕ) : ι → ι → Prop :=
  Relation.ReflTransGen fun a b => d a b ≤ t

omit [Fintype ι] in
theorem Linked.refl (d : ι → ι → ℕ) (t : ℕ) (i : ι) : Linked d t i i :=
  Relation.ReflTransGen.refl

omit [Fintype ι] in
theorem Linked.single (h : d i j ≤ t) : Linked d t i j :=
  Relation.ReflTransGen.single h

omit [Fintype ι] in
theorem Linked.trans (h₁ : Linked d t i j) (h₂ : Linked d t j k) : Linked d t i k :=
  Relation.ReflTransGen.trans h₁ h₂

omit [Fintype ι] in
theorem Linked.mono (hts : t ≤ s) (h : Linked d t i j) : Linked d s i j :=
  Relation.ReflTransGen.mono (fun _ _ hab => hab.trans hts) h

omit [Fintype ι] in
theorem Linked.symm (hd : ∀ a b, d a b = d b a) (h : Linked d t i j) : Linked d t j i := by
  induction h with
  | refl => exact Linked.refl d t i
  | tail _ hbc ih => exact (Linked.single (by rw [hd]; exact hbc)).trans ih

/-- The largest entry of the table: every pair is linked at this threshold. -/
def dmax (d : ι → ι → ℕ) : ℕ := Finset.univ.sup fun p : ι × ι => d p.1 p.2

theorem le_dmax (d : ι → ι → ℕ) (i j : ι) : d i j ≤ dmax d :=
  Finset.le_sup (f := fun p : ι × ι => d p.1 p.2) (Finset.mem_univ (i, j))

theorem linked_dmax (d : ι → ι → ℕ) (i j : ι) : Linked d (dmax d) i j :=
  Linked.single (le_dmax d i j)

/-! ### The chain distance -/

/-- The **chain distance** (single linkage): the least threshold at which `i` and `j` are
linked by a chain of steps. -/
noncomputable def slink (d : ι → ι → ℕ) (i j : ι) : ℕ := sInf {t | Linked d t i j}

theorem slink_spec (d : ι → ι → ℕ) (i j : ι) : Linked d (slink d i j) i j := by
  have hne : {t | Linked d t i j}.Nonempty := ⟨dmax d, linked_dmax d i j⟩
  simpa only [slink] using Nat.sInf_mem hne

omit [Fintype ι] in
theorem slink_le_of_linked (h : Linked d t i j) : slink d i j ≤ t :=
  Nat.sInf_le (Set.mem_setOf_eq ▸ h)

omit [Fintype ι] in
/-- Nothing distinct is linked at threshold `0` when the table has no zero off the
diagonal. -/
theorem eq_of_linked_zero (hpos : ∀ a b : ι, a ≠ b → 0 < d a b) {a b : ι}
    (h : Linked d 0 a b) : a = b := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      have : x = y := by
        by_contra hne
        exact absurd (hpos x y hne) (by omega)
      exact this ▸ ih

omit [Fintype ι] in
/-- An invariant that survives every single step survives a whole chain. -/
theorem inv_eq_of_linked {κ : Type*} (inv : ι → κ)
    (hstep : ∀ a b : ι, d a b ≤ t → inv a = inv b) {a b : ι} (h : Linked d t a b) :
    inv a = inv b := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih => exact ih.trans (hstep x y hxy)

/-- Being linked at a threshold and having chain distance at most that threshold are the
same thing. -/
theorem linked_iff_slink_le : Linked d t i j ↔ slink d i j ≤ t :=
  ⟨slink_le_of_linked, fun h => (slink_spec d i j).mono h⟩

omit [Fintype ι] in
theorem slink_le_dist (d : ι → ι → ℕ) (i j : ι) : slink d i j ≤ d i j :=
  slink_le_of_linked (Linked.single le_rfl)

omit [Fintype ι] in
theorem slink_self (d : ι → ι → ℕ) (i : ι) : slink d i i = 0 :=
  Nat.le_zero.1 (slink_le_of_linked (Linked.refl d 0 i))

theorem slink_symm (hd : ∀ a b, d a b = d b a) (i j : ι) : slink d i j = slink d j i :=
  le_antisymm (slink_le_of_linked ((slink_spec d j i).symm hd))
    (slink_le_of_linked ((slink_spec d i j).symm hd))

/-- **The chain distance is an ultrametric.** -/
theorem slink_ultra (d : ι → ι → ℕ) (i j k : ι) :
    slink d i k ≤ max (slink d i j) (slink d j k) :=
  slink_le_of_linked
    (((slink_spec d i j).mono (le_max_left _ _)).trans
      ((slink_spec d j k).mono (le_max_right _ _)))

theorem slink_triangle (d : ι → ι → ℕ) (i j k : ι) :
    slink d i k ≤ slink d i j + slink d j k :=
  (slink_ultra d i j k).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

/-- **Maximality: `slink d` is the subdominant ultrametric.**  Any ultrametric `u` that
never exceeds `d` never exceeds the chain distance either. -/
theorem le_slink_of_ultra {u : ι → ι → ℕ} (hrefl : ∀ a, u a a = 0)
    (hultra : ∀ a b c, u a c ≤ max (u a b) (u b c)) (hle : ∀ a b, u a b ≤ d a b) (i j : ι) :
    u i j ≤ slink d i j := by
  have key : ∀ {t : ℕ} {a b : ι}, Linked d t a b → u a b ≤ t := by
    intro t a b h
    induction h with
    | refl => simp [hrefl]
    | @tail b' c' _ hbc ih =>
        exact (hultra a b' c').trans (max_le ih ((hle b' c').trans hbc))
  exact key (slink_spec d i j)

/-! ### The tree -/

/-- The group of `i` at threshold `t`: everything reachable from `i` by steps of cost at
most `t`.  These are the nodes of the taxonomy tree. -/
noncomputable def cluster (d : ι → ι → ℕ) (t : ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => slink d i j ≤ t

theorem mem_cluster : j ∈ cluster d t i ↔ slink d i j ≤ t := by
  simp [cluster]

theorem self_mem_cluster (d : ι → ι → ℕ) (t : ℕ) (i : ι) : i ∈ cluster d t i :=
  mem_cluster.2 (by simp [slink_self])

theorem cluster_mono (d : ι → ι → ℕ) (hts : t ≤ s) (i : ι) :
    cluster d t i ⊆ cluster d s i := fun _ hj =>
  mem_cluster.2 ((mem_cluster.1 hj).trans hts)

/-- Two objects in a common group at threshold `t` have the same group at that
threshold. -/
theorem cluster_eq_of_mem (hd : ∀ a b, d a b = d b a) (hj : j ∈ cluster d t i) :
    cluster d t j = cluster d t i := by
  have hij : slink d i j ≤ t := mem_cluster.1 hj
  have hji : slink d j i ≤ t := by rwa [slink_symm hd]
  ext x
  simp only [mem_cluster]
  constructor
  · intro hx; exact (slink_ultra d i j x).trans (max_le hij hx)
  · intro hx; exact (slink_ultra d j i x).trans (max_le hji hx)

/-- **The groups form a tree.**  Any two groups, at any two thresholds, are either
disjoint or one contains the other: a laminar family, i.e. a rooted tree ordered by
inclusion. -/
theorem cluster_laminar (hd : ∀ a b, d a b = d b a) (t s : ℕ) (i j : ι) :
    Disjoint (cluster d t i) (cluster d s j) ∨
      cluster d t i ⊆ cluster d s j ∨ cluster d s j ⊆ cluster d t i := by
  by_cases hdis : Disjoint (cluster d t i) (cluster d s j)
  · exact Or.inl hdis
  obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.1 hdis
  have e1 : cluster d t x = cluster d t i := cluster_eq_of_mem hd hx1
  have e2 : cluster d s x = cluster d s j := cluster_eq_of_mem hd hx2
  rcases le_total t s with h | h
  · exact Or.inr (Or.inl (by rw [← e1, ← e2]; exact cluster_mono d h x))
  · exact Or.inr (Or.inr (by rw [← e1, ← e2]; exact cluster_mono d h x))

/-- At a large enough threshold everything is one group: the root of the tree. -/
theorem cluster_top (d : ι → ι → ℕ) (i : ι) : cluster d (dmax d) i = Finset.univ := by
  ext x
  simp only [mem_cluster, Finset.mem_univ, iff_true]
  exact slink_le_of_linked (linked_dmax d i x)

/-- At threshold `0`, if no two distinct objects are at distance zero, the groups are the
single objects: the leaves of the tree. -/
theorem cluster_bot (hpos : ∀ a b : ι, a ≠ b → 0 < d a b) (i : ι) :
    cluster d 0 i = {i} := by
  ext x
  simp only [mem_cluster, Finset.mem_singleton]
  constructor
  · intro hx
    exact (eq_of_linked_zero hpos (linked_iff_slink_le.2 hx)).symm
  · rintro rfl; exact le_of_eq (slink_self d _)

/-- **The tree refines a classification.**  If an invariant `inv` cannot change across a
step of cost at most `t`, then every group at threshold `t` is `inv`-monochrome. -/
theorem cluster_monochrome {κ : Type*} (inv : ι → κ)
    (h : ∀ a b : ι, d a b ≤ t → inv a = inv b) (i : ι) :
    ∀ j ∈ cluster d t i, inv j = inv i := by
  intro j hj
  exact (inv_eq_of_linked inv h (linked_iff_slink_le.2 (mem_cluster.1 hj))).symm

end UltrametricTaxonomy
