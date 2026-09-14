import RequestProject.CenterRetraction

/-!
# Further structure of retractions onto the center

This file continues `RequestProject.CenterRetraction`.

* `mem_center_prod_iff'` / `hasCenterRetraction_prod` : the class of groups retracting onto
  their center is closed under (binary) products.
* `commutator_le_ker` and `disjoint_commutator_center` : a retraction kills all commutators,
  so the derived subgroup meets the center trivially; in particular a *perfect* group with a
  retraction onto its center is centerless
  (`center_eq_bot_of_commutator_eq_top`).
* `mulEquivKerProdCenter` : a retraction splits the group, `G ≃* ker r × Z(G)`.
* `hasCenterRetraction_of_coprime` : by Schur–Zassenhaus, a finite group whose center has
  order coprime to its index retracts onto its center — e.g. any finite group of order `n`
  with `Nat.card (center G)` coprime to the index.
-/

open Subgroup

variable {G H : Type*} [Group G] [Group H]

section Products

/-- A group in which all elements commute retracts onto its center (which is everything).
This is the `CommGroup`-free form of `hasCenterRetraction_of_commGroup`. -/
theorem hasCenterRetraction_of_commute (h : ∀ a b : G, a * b = b * a) :
    HasCenterRetraction G := by
  refine ⟨⟨⟨fun g => ⟨g, mem_center_iff.2 fun x => h x g⟩, rfl⟩, fun a b => rfl⟩, fun z => rfl⟩

/-- Membership in the center of a product is componentwise. -/
theorem mem_center_prod_iff' (x : G × H) :
    x ∈ center (G × H) ↔ x.1 ∈ center G ∧ x.2 ∈ center H := by
  constructor
  · intro hx
    refine ⟨mem_center_iff.2 fun g => congrArg Prod.fst (mem_center_iff.1 hx (g, 1)),
      mem_center_iff.2 fun h => congrArg Prod.snd (mem_center_iff.1 hx (1, h))⟩
  · rintro ⟨h1, h2⟩
    rw [mem_center_iff]
    rintro ⟨g, h⟩
    exact Prod.ext (mem_center_iff.1 h1 g) (mem_center_iff.1 h2 h)

/-- Groups retracting onto their center are closed under products. -/
theorem hasCenterRetraction_prod (hG : HasCenterRetraction G) (hH : HasCenterRetraction H) :
    HasCenterRetraction (G × H) := by
  obtain ⟨r₁, hr₁⟩ := hG
  obtain ⟨r₂, hr₂⟩ := hH
  refine ⟨⟨⟨fun x => ⟨((r₁ x.1 : G), (r₂ x.2 : H)),
      (mem_center_prod_iff' _).2 ⟨(r₁ x.1).2, (r₂ x.2).2⟩⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    simp [map_mul]
  · rintro ⟨⟨g, h⟩, hz⟩
    obtain ⟨hg, hh⟩ := (mem_center_prod_iff' _).1 hz
    apply Subtype.ext
    have e₁ := hr₁ ⟨g, hg⟩
    have e₂ := hr₂ ⟨h, hh⟩
    exact Prod.ext (congrArg Subtype.val e₁) (congrArg Subtype.val e₂)

end Products

section Commutators

variable {r : G →* center G} (hr : ∀ z : center G, r z = z)
include hr

omit hr in
/-- A retraction onto the center kills every commutator (its target is abelian). -/
theorem commutator_le_ker : commutator G ≤ r.ker := by
  rw [commutator_eq_closure]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro x ⟨a, b, rfl⟩
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
  exact mul_inv_eq_one.2 (by rw [mul_comm (r a) (r b)]; group)

/-- The derived subgroup of a group retracting onto its center meets the center trivially. -/
theorem disjoint_commutator_center : Disjoint (commutator G) (center G) :=
  Disjoint.mono_left commutator_le_ker (isComplement_ker_center hr).disjoint

/-- A *perfect* group admitting a retraction onto its center is centerless. -/
theorem center_eq_bot_of_commutator_eq_top (htop : commutator G = ⊤) : center G = ⊥ := by
  have hd := disjoint_commutator_center hr
  rw [htop] at hd
  simpa using (disjoint_iff.1 hd)

/-- The multiplication map `ker r × Z(G) → G`; it is a homomorphism because the second
factor is central. -/
def kerCenterHom : ↥(MonoidHom.ker r) × ↥(center G) →* G where
  toFun x := (x.1 : G) * (x.2 : G)
  map_one' := by simp
  map_mul' := by
    rintro ⟨⟨a, ha⟩, ⟨z, hz⟩⟩ ⟨⟨b, hb⟩, ⟨w, hw⟩⟩
    have hzb : z * b = b * z := (mem_center_iff.1 hz b).symm
    show a * b * (z * w) = a * z * (b * w)
    calc a * b * (z * w) = a * (b * z) * w := by group
      _ = a * (z * b) * w := by rw [hzb]
      _ = a * z * (b * w) := by group

/-- **A retraction splits the group**: `G ≃* ker r × Z(G)`. -/
noncomputable def mulEquivKerProdCenter : (↥(MonoidHom.ker r) × ↥(center G)) ≃* G :=
  MulEquiv.ofBijective kerCenterHom (isComplement_ker_center hr)

theorem mulEquivKerProdCenter_apply (x : ↥(MonoidHom.ker r) × ↥(center G)) :
    mulEquivKerProdCenter hr x = (x.1 : G) * (x.2 : G) := rfl

end Commutators

section Nilpotent

/-- A nontrivial nilpotent group has nontrivial center. -/
theorem center_ne_bot_of_nilpotent (G : Type*) [Group G] [Group.IsNilpotent G] [Nontrivial G] :
    center G ≠ ⊥ := by
  intro h
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsNilpotent G)
  have key : ∀ k, upperCentralSeries G k = ⊥ := by
    intro k
    induction k with
    | zero => exact upperCentralSeries_zero G
    | succ k ih =>
        rw [eq_bot_iff]
        intro x hx
        rw [mem_upperCentralSeries_succ_iff] at hx
        have hxc : x ∈ center G := by
          rw [mem_center_iff]
          intro g
          have hg := hx g
          rw [ih, Subgroup.mem_bot] at hg
          have h2 : x * g * x⁻¹ = g := by
            rw [← mul_inv_eq_one]
            simpa [mul_assoc] using hg
          calc g * x = (x * g * x⁻¹) * x := by rw [h2]
            _ = x * g := by group
        rw [h, Subgroup.mem_bot] at hxc
        simp [hxc]
  have hbt : (⊥ : Subgroup G) = ⊤ := by rw [← key n, hn]
  exact bot_ne_top hbt

/-- **No nonabelian nilpotent group retracts onto its center** (this generalizes the
`p`-group case, since finite `p`-groups are nilpotent): a nilpotent group admitting a
retraction onto its center is abelian. -/
theorem commute_of_hasCenterRetraction_of_nilpotent [Group.IsNilpotent G]
    (h : HasCenterRetraction G) : ∀ a b : G, a * b = b * a := by
  obtain ⟨r, hr⟩ := h
  have hker : center (r.ker : Subgroup G) = ⊥ := center_ker_eq_bot hr
  have hbot : r.ker = ⊥ := by
    by_contra hne
    have hnt : Nontrivial (r.ker : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact center_ne_bot_of_nilpotent (r.ker : Subgroup G) hker
  intro a b
  have hcent : ∀ g : G, g ∈ center G := by
    intro g
    have hg : g * ((r g : G))⁻¹ ∈ r.ker := retraction_apply_mem_ker hr g
    rw [hbot, Subgroup.mem_bot] at hg
    have hgr : g = (r g : G) := mul_inv_eq_one.1 hg
    rw [hgr]
    exact (r g).2
  exact mem_center_iff.1 (hcent b) a

/-- Contrapositive form: a nonabelian nilpotent group has no retraction onto its center. -/
theorem not_hasCenterRetraction_of_nilpotent [Group.IsNilpotent G]
    (hnc : ¬ ∀ a b : G, a * b = b * a) : ¬ HasCenterRetraction G :=
  fun h => hnc (commute_of_hasCenterRetraction_of_nilpotent h)

end Nilpotent

section SchurZassenhaus

/-- **Schur–Zassenhaus criterion.** If the center of `G` has order coprime to its index, then
`G` retracts onto its center. -/
theorem hasCenterRetraction_of_coprime
    (h : (Nat.card (center G)).Coprime (center G).index) : HasCenterRetraction G := by
  obtain ⟨N, hN⟩ := Subgroup.exists_right_complement'_of_coprime (N := center G) h
  exact (hasCenterRetraction_iff_isComplement G).2 ⟨N, hN.symm⟩

end SchurZassenhaus

section Examples

/-- The nilpotent obstruction applies beyond `p`-groups: the group `D₄ × C₃` of order `24` is
nilpotent and nonabelian, so it does not retract onto its center. -/
theorem not_hasCenterRetraction_dihedralFour_prod_cyclicThree :
    ¬ HasCenterRetraction (DihedralGroup 4 × Multiplicative (ZMod 3)) := by
  have hcard : Nat.card (DihedralGroup 4) = 2 ^ 3 := by
    simp [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hp : IsPGroup 2 (DihedralGroup 4) := IsPGroup.of_card hcard
  haveI : Group.IsNilpotent (DihedralGroup 4) := hp.isNilpotent
  refine not_hasCenterRetraction_of_nilpotent ?_
  intro hcomm
  have := hcomm (DihedralGroup.r 1, 1) (DihedralGroup.sr 0, 1)
  revert this
  decide

end Examples
