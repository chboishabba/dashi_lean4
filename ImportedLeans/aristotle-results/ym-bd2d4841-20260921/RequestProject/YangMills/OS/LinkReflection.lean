/-
# Reflections of a lattice gauge configuration space

A reflection of a lattice gauge theory is, combinatorially, an involution `r` of
the link set together with

* a set of **plane** links, fixed by `r`, shared by the two half-spaces;
* a set of **positive** links, carried by `r` onto the remaining (**negative**)
  links;
* a set of **inverted** links, whose group variable is inverted by the
  reflection (the links transported against their orientation; in the Wilson
  theory these are the temporal links).

`LinkReflectionData` packages exactly that, `confRefl` is the induced involution
of configurations, and the main result of this file, `reflectionSplitting`,
produces from this data a `ReflectionSplitting` of the product Haar measure: a
measure-preserving identification

```
  (links → G)  ≅  (plane links → G) × (positive links → G) × (negative links → G)
```

in which `confRefl` fixes the plane coordinates and carries the negative
coordinates onto the positive ones by a measure-preserving map.  Everything is
proved from the Haar theory of the compact gauge group; in particular
`measurePreserving_confRefl` needs inversion invariance of Haar measure on a
compact group, which is proved here (`haarProb.isInvInvariant`) from uniqueness
of the Haar probability measure.

Combined with `OS/GramPositivity.lean` this reduces reflection positivity of any
lattice gauge measure to the factorisation of its Boltzmann weight.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Config
import RequestProject.YangMills.OS.GramPositivity

namespace RequestProject.YangMills.OS

open MeasureTheory
open RequestProject.YangMills.Lattice

/-! ## Inversion invariance of Haar measure on a compact group -/

/-- The normalised Haar measure of a compact group is invariant under inversion.
(Compact groups are unimodular; the proof here is uniqueness of the Haar
probability measure, applied to the push-forward under inversion, which is left
invariant because Haar measure on a compact group is right invariant.) -/
instance haarProb.isInvInvariant (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    (haarProb G).IsInvInvariant := by
  constructor
  haveI : IsProbabilityMeasure ((haarProb G).inv) := by
    constructor
    rw [Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ]
    simp
  haveI : ((haarProb G).inv).IsOpenPosMeasure := by
    constructor
    intro U hU hne h0
    rw [Measure.inv, Measure.map_apply measurable_inv hU.measurableSet] at h0
    have hne' : (Inv.inv ⁻¹' U).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x⁻¹, by simpa using hx⟩
    exact (hU.preimage continuous_inv).measure_ne_zero (haarProb G) hne' h0
  haveI : ((haarProb G).inv).IsHaarMeasure := ⟨⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-! ## Combinatorial reflection data -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The combinatorics of a reflection of a lattice gauge theory: an involution
of the links, the plane links it fixes, the positive links it carries onto the
complement, and the links whose variable it inverts. -/
structure LinkReflectionData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The link involution. -/
  r : Equiv.Perm ι
  /-- The links lying in the reflection plane. -/
  plane : Finset ι
  /-- The links strictly on the positive side. -/
  pos : Finset ι
  /-- The links whose group variable the reflection inverts. -/
  inverted : Finset ι
  /-- `r` is an involution. -/
  r_involutive : ∀ i, r (r i) = i
  /-- Plane links are not positive. -/
  plane_not_pos : ∀ i ∈ plane, i ∉ pos
  /-- Plane links are fixed. -/
  r_plane : ∀ i ∈ plane, r i = i
  /-- The reflection of a positive link is not a plane link. -/
  r_pos_not_plane : ∀ i ∈ pos, r i ∉ plane
  /-- The reflection of a positive link is not positive. -/
  r_pos_not_pos : ∀ i ∈ pos, r i ∉ pos
  /-- The reflection of a negative link is positive. -/
  r_neg : ∀ i, i ∉ plane → i ∉ pos → r i ∈ pos
  /-- Plane links are not inverted. -/
  inverted_not_plane : ∀ i ∈ inverted, i ∉ plane
  /-- Being inverted is a reflection-invariant property. -/
  inverted_r : ∀ i, r i ∈ inverted ↔ i ∈ inverted

namespace LinkReflectionData

variable (D : LinkReflectionData ι)

/-- The links strictly on the negative side. -/
def neg : Finset ι := (D.plane ∪ D.pos)ᶜ

theorem mem_neg {i : ι} : i ∈ D.neg ↔ (i ∉ D.plane ∧ i ∉ D.pos) := by
  simp [neg]

/-- The plane links as a type. -/
abbrev Plane := {i : ι // i ∈ D.plane}

/-- The positive links as a type. -/
abbrev Pos := {i : ι // i ∈ D.pos}

/-- The negative links as a type. -/
abbrev Neg := {i : ι // i ∈ D.neg}

theorem pos_not_plane {i : ι} (hi : i ∈ D.pos) : i ∉ D.plane := fun h => D.plane_not_pos i h hi

/-- The reflection carries positive links to negative links. -/
def rPosNeg : D.Pos ≃ D.Neg where
  toFun p := ⟨D.r p.1, D.mem_neg.2 ⟨D.r_pos_not_plane p.1 p.2, D.r_pos_not_pos p.1 p.2⟩⟩
  invFun q := ⟨D.r q.1, D.r_neg q.1 (D.mem_neg.1 q.2).1 (D.mem_neg.1 q.2).2⟩
  left_inv p := by ext; exact D.r_involutive p.1
  right_inv q := by ext; exact D.r_involutive q.1

/-- The link set is the disjoint union of the plane, positive and negative
links. -/
def idxEquiv : D.Plane ⊕ D.Pos ⊕ D.Neg ≃ ι where
  toFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  invFun i :=
    if h : i ∈ D.plane then Sum.inl ⟨i, h⟩
    else if h2 : i ∈ D.pos then Sum.inr (Sum.inl ⟨i, h2⟩)
    else Sum.inr (Sum.inr ⟨i, D.mem_neg.2 ⟨h, h2⟩⟩)
  left_inv := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩)
    · simp [hi]
    · simp [D.pos_not_plane hi, hi]
    · simp [(D.mem_neg.1 hi).1, (D.mem_neg.1 hi).2]
  right_inv := by
    intro i
    by_cases h : i ∈ D.plane
    · simp [h]
    · by_cases h2 : i ∈ D.pos <;> simp [h, h2]

@[simp] theorem idxEquiv_inl (p : D.Plane) : D.idxEquiv (Sum.inl p) = p.1 := rfl
@[simp] theorem idxEquiv_inr_inl (p : D.Pos) : D.idxEquiv (Sum.inr (Sum.inl p)) = p.1 := rfl
@[simp] theorem idxEquiv_inr_inr (p : D.Neg) : D.idxEquiv (Sum.inr (Sum.inr p)) = p.1 := rfl

/-! ## The reflection of configurations -/

variable {G : Type*} [Group G]

/-- The reflection of a gauge field configuration: relabel the links by `r`, and
invert the variables of the inverted links. -/
def confRefl (U : ι → G) : ι → G :=
  fun i => if i ∈ D.inverted then (U (D.r i))⁻¹ else U (D.r i)

/-- The reflection of configurations is an involution. -/
theorem confRefl_involutive (U : ι → G) : D.confRefl (D.confRefl U) = U := by
  funext i
  by_cases h : i ∈ D.inverted
  · have hr : D.r i ∈ D.inverted := (D.inverted_r i).2 h
    simp [confRefl, h, hr, D.r_involutive i]
  · have hr : D.r i ∉ D.inverted := fun hc => h ((D.inverted_r i).1 hc)
    simp [confRefl, h, hr, D.r_involutive i]

/-- The reflection does not touch the plane links. -/
theorem confRefl_plane (U : ι → G) {i : ι} (hi : i ∈ D.plane) : D.confRefl U i = U i := by
  have h1 : i ∉ D.inverted := fun hc => D.inverted_not_plane i hc hi
  simp [confRefl, h1, D.r_plane i hi]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

omit [CompactSpace G] [T2Space G] in
theorem measurable_confRefl : Measurable (D.confRefl (G := G)) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ D.inverted <;> simp only [confRefl, h, if_true, if_false]
  · exact (measurable_pi_apply (D.r i)).inv
  · exact measurable_pi_apply (D.r i)

/-! ## Coordinates -/

/-- Coordinatewise inversion of the marked positive link variables. -/
def invCoordsFun (W : D.Pos → G) : D.Pos → G :=
  fun p => if p.1 ∈ D.inverted then (W p)⁻¹ else W p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] in
theorem invCoordsFun_involutive (W : D.Pos → G) : D.invCoordsFun (D.invCoordsFun W) = W := by
  funext p
  by_cases h : p.1 ∈ D.inverted
  · simp only [invCoordsFun, if_pos h, inv_inv]
  · simp only [invCoordsFun, if_neg h]

omit [CompactSpace G] [T2Space G] in
theorem measurable_invCoordsFun : Measurable (D.invCoordsFun (G := G)) := by
  refine measurable_pi_lambda _ fun p => ?_
  by_cases h : p.1 ∈ D.inverted
  · simp only [invCoordsFun, if_pos h]
    exact (measurable_pi_apply p).inv
  · simp only [invCoordsFun, if_neg h]
    exact measurable_pi_apply p

/-- Coordinatewise inversion as a measurable involution. -/
def invCoords : (D.Pos → G) ≃ᵐ (D.Pos → G) where
  toFun := D.invCoordsFun
  invFun := D.invCoordsFun
  left_inv := D.invCoordsFun_involutive
  right_inv := D.invCoordsFun_involutive
  measurable_toFun := D.measurable_invCoordsFun
  measurable_invFun := D.measurable_invCoordsFun

theorem measurePreserving_invCoords :
    MeasurePreserving (D.invCoords (G := G)) (prodHaar D.Pos G) (prodHaar D.Pos G) := by
  have h := measurePreserving_pi (fun _ : D.Pos => haarProb G) (fun _ : D.Pos => haarProb G)
    (f := fun p : D.Pos => fun u : G => if p.1 ∈ D.inverted then u⁻¹ else u)
    (fun p => by
      by_cases h : p.1 ∈ D.inverted
      · simpa [h] using MeasureTheory.Measure.measurePreserving_inv (haarProb G)
      · simpa [h] using MeasurePreserving.id (haarProb G))
  exact h

/-- Reindexing the negative link variables by the reflection. -/
noncomputable def negToPos : (D.Neg → G) ≃ᵐ (D.Pos → G) :=
  (MeasurableEquiv.piCongrLeft (fun _ : D.Neg => G) D.rPosNeg).symm

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem negToPos_apply (V : D.Neg → G) (p : D.Pos) :
    D.negToPos V p = V (D.rPosNeg p) := by
  simp [negToPos, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem measurePreserving_negToPos :
    MeasurePreserving (D.negToPos (G := G)) (prodHaar D.Neg G) (prodHaar D.Pos G) := by
  have h := measurePreserving_piCongrLeft (fun _ : D.Neg => haarProb G) D.rPosNeg
  exact MeasurePreserving.symm _ h

/-- The identification of the negative variables with the positive ones
implemented by the reflection: relabel by `r` and invert the marked variables. -/
noncomputable def sigmaEquiv : (D.Neg → G) ≃ᵐ (D.Pos → G) :=
  (D.negToPos).trans D.invCoords

omit [CompactSpace G] [T2Space G] in
theorem sigmaEquiv_apply (V : D.Neg → G) (p : D.Pos) :
    D.sigmaEquiv V p = if p.1 ∈ D.inverted then (V (D.rPosNeg p))⁻¹ else V (D.rPosNeg p) := by
  simp [sigmaEquiv, invCoords, invCoordsFun, negToPos_apply]

theorem measurePreserving_sigmaEquiv :
    MeasurePreserving (D.sigmaEquiv (G := G)) (prodHaar D.Neg G) (prodHaar D.Pos G) :=
  (D.measurePreserving_invCoords).comp D.measurePreserving_negToPos

/-- The splitting of a configuration into its plane, positive and negative
coordinates. -/
noncomputable def coordEquiv :
    (ι → G) ≃ᵐ ((D.Plane → G) × ((D.Pos → G) × (D.Neg → G))) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : ι => G) D.idxEquiv).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : D.Plane ⊕ D.Pos ⊕ D.Neg => G)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (D.Plane → G))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : D.Pos ⊕ D.Neg => G))))

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem coordEquiv_apply (U : ι → G) :
    D.coordEquiv U = (fun p : D.Plane => U p.1,
      (fun p : D.Pos => U p.1, fun p : D.Neg => U p.1)) := by
  have hpi : ((MeasurableEquiv.piCongrLeft (fun _ : ι => G) D.idxEquiv).symm) U
      = fun a => U (D.idxEquiv a) := by
    funext a
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  simp [coordEquiv, hpi]
  rfl

theorem measurePreserving_coordEquiv :
    MeasurePreserving (D.coordEquiv (G := G)) (prodHaar ι G)
      ((prodHaar D.Plane G).prod ((prodHaar D.Pos G).prod (prodHaar D.Neg G))) := by
  have h1 : MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : ι => G) D.idxEquiv).symm)
      (prodHaar ι G) (prodHaar (D.Plane ⊕ D.Pos ⊕ D.Neg) G) :=
    MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : ι => haarProb G) D.idxEquiv)
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : D.Plane ⊕ D.Pos ⊕ D.Neg => G))
      (prodHaar (D.Plane ⊕ D.Pos ⊕ D.Neg) G)
      ((prodHaar D.Plane G).prod (prodHaar (D.Pos ⊕ D.Neg) G)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : D.Plane ⊕ D.Pos ⊕ D.Neg => haarProb G)
  have h3 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : D.Pos ⊕ D.Neg => G))
      (prodHaar (D.Pos ⊕ D.Neg) G)
      ((prodHaar D.Pos G).prod (prodHaar D.Neg G)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : D.Pos ⊕ D.Neg => haarProb G)
  have h4 : MeasurePreserving
      (Prod.map (id : (D.Plane → G) → (D.Plane → G))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : D.Pos ⊕ D.Neg => G)))
      ((prodHaar D.Plane G).prod (prodHaar (D.Pos ⊕ D.Neg) G))
      ((prodHaar D.Plane G).prod ((prodHaar D.Pos G).prod (prodHaar D.Neg G))) :=
    (MeasurePreserving.id _).prod h3
  exact h4.comp (h2.comp h1)


/-- The reflection of configurations as a measurable involution. -/
def confReflEquiv : (ι → G) ≃ᵐ (ι → G) where
  toFun := D.confRefl
  invFun := D.confRefl
  left_inv := D.confRefl_involutive
  right_inv := D.confRefl_involutive
  measurable_toFun := D.measurable_confRefl
  measurable_invFun := D.measurable_confRefl

omit [CompactSpace G] [T2Space G] in
@[simp] theorem confReflEquiv_apply (U : ι → G) : D.confReflEquiv U = D.confRefl U := rfl

/-- **The reflection of configurations preserves the product Haar measure**:
it relabels the links by a permutation and inverts some of the variables, and
Haar measure on a compact group is both translation and inversion invariant. -/
theorem measurePreserving_confRefl :
    MeasurePreserving (D.confRefl (G := G)) (prodHaar ι G) (prodHaar ι G) := by
  have h1 : MeasurePreserving (fun U : ι → G => fun i => U (D.r i))
      (prodHaar ι G) (prodHaar ι G) := measurePreserving_reindex D.r
  have h2 : MeasurePreserving
      (fun W : ι → G => fun i => if i ∈ D.inverted then (W i)⁻¹ else W i)
      (prodHaar ι G) (prodHaar ι G) := by
    refine measurePreserving_pi (fun _ : ι => haarProb G) (fun _ : ι => haarProb G)
      (f := fun i => fun u : G => if i ∈ D.inverted then u⁻¹ else u) fun i => ?_
    by_cases h : i ∈ D.inverted
    · simpa [h] using MeasureTheory.Measure.measurePreserving_inv (haarProb G)
    · simpa [h] using MeasurePreserving.id (haarProb G)
  exact h2.comp h1

/-! ## The reflection splitting -/

/-- **The reflection splitting of a lattice gauge configuration space.**  The
product Haar measure factorises through the plane, positive and negative link
variables, the reflection fixes the plane variables, and it carries the negative
variables onto the positive ones by the measure-preserving map `sigmaEquiv`. -/
noncomputable def reflectionSplitting :
    ReflectionSplitting (ι → G) (prodHaar ι G) (D.Pos → G) (D.Plane → G) (D.Neg → G) where
  coord := D.coordEquiv
  muA := prodHaar D.Pos G
  muB := prodHaar D.Plane G
  muC := prodHaar D.Neg G
  sfiniteA := by infer_instance
  sfiniteB := by infer_instance
  sfiniteC := by infer_instance
  coord_mp := D.measurePreserving_coordEquiv
  refl := D.confRefl
  sigma := D.sigmaEquiv
  sigma_mp := D.measurePreserving_sigmaEquiv
  plane_refl := by
    intro U
    rw [coordEquiv_apply, coordEquiv_apply]
    funext p
    exact D.confRefl_plane U p.2
  pos_refl := by
    intro U
    rw [coordEquiv_apply, coordEquiv_apply]
    funext p
    rw [sigmaEquiv_apply]
    rfl

@[simp] theorem reflectionSplitting_plane (U : ι → G) :
    (D.reflectionSplitting (G := G)).plane U = fun p : D.Plane => U p.1 := by
  simp [ReflectionSplitting.plane, reflectionSplitting, coordEquiv_apply]

@[simp] theorem reflectionSplitting_pos (U : ι → G) :
    (D.reflectionSplitting (G := G)).pos U = fun p : D.Pos => U p.1 := by
  simp [ReflectionSplitting.pos, reflectionSplitting, coordEquiv_apply]

@[simp] theorem reflectionSplitting_neg (U : ι → G) :
    (D.reflectionSplitting (G := G)).neg U = fun p : D.Neg => U p.1 := by
  simp [ReflectionSplitting.neg, reflectionSplitting, coordEquiv_apply]

@[simp] theorem reflectionSplitting_refl (U : ι → G) :
    (D.reflectionSplitting (G := G)).refl U = D.confRefl U := rfl

end LinkReflectionData

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms LinkReflectionData.confRefl_involutive
#print axioms LinkReflectionData.measurePreserving_coordEquiv
#print axioms LinkReflectionData.reflectionSplitting

end Audit
