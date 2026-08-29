import Mathlib

/-!
# Retractions onto the center of a group

A *retraction onto the center* of a group `G` is a group homomorphism
`r : G →* Z(G)` which restricts to the identity on `Z(G)`.

This file proves:

* `HasCenterRetraction` : the definition.
* `hasCenterRetraction_iff_isComplement` : such a retraction exists iff the center admits a
  complement, i.e. iff `Z(G)` is a direct factor of `G`.
* `hasCenterRetraction_of_commGroup`, `hasCenterRetraction_of_center_eq_bot`,
  `hasCenterRetraction_prod_of_center_eq_bot` : positive families (abelian groups, centerless
  groups, and products `G × A` of a centerless group with an abelian group).
* `center_ker_eq_bot` : the kernel of a retraction is itself centerless.
* `not_hasCenterRetraction_of_isPGroup` : *no* nonabelian finite `p`-group admits a retraction
  onto its center; in particular the quaternion group `Q₈` and the dihedral group `D₄` of
  order `8` do not.
-/

open Subgroup

variable {G : Type*} [Group G]

/-- `G` admits a retraction onto its center: a group homomorphism `G →* Z(G)` restricting to
the identity on the center. -/
def HasCenterRetraction (G : Type*) [Group G] : Prop :=
  ∃ r : G →* center G, ∀ z : center G, r z = z

section Basic

/-- Every abelian group is its own center, and the identity is a retraction onto it. -/
theorem hasCenterRetraction_of_commGroup (G : Type*) [CommGroup G] : HasCenterRetraction G := by
  refine ⟨⟨⟨fun g => ⟨g, mem_center_iff.2 fun h => mul_comm h g⟩, rfl⟩, fun a b => rfl⟩, ?_⟩
  intro z
  rfl

/-- A group with trivial center admits the (trivial) retraction onto its center. -/
theorem hasCenterRetraction_of_center_eq_bot (h : center G = ⊥) : HasCenterRetraction G := by
  have : Subsingleton (center G) := by
    rw [h]; infer_instance
  exact ⟨1, fun z => Subsingleton.elim _ _⟩

/-- In a product `G × A` with `G` centerless, the center is `1 × A`. -/
theorem mem_center_prod_iff {A : Type*} [CommGroup A] (x : G × A) :
    x ∈ center (G × A) ↔ x.1 ∈ center G := by
  constructor
  · intro hx
    rw [mem_center_iff]
    intro g
    exact congrArg Prod.fst (mem_center_iff.1 hx (g, 1))
  · intro hx
    rw [mem_center_iff]
    rintro ⟨g, a⟩
    have h1 : g * x.1 = x.1 * g := mem_center_iff.1 hx g
    exact Prod.ext h1 (mul_comm a x.2)

/-- If `G` has trivial center and `A` is abelian, then `G × A` retracts onto its center
(`= 1 × A`) via the second projection. -/
theorem hasCenterRetraction_prod_of_center_eq_bot {A : Type*} [CommGroup A]
    (h : center G = ⊥) : HasCenterRetraction (G × A) := by
  have hmem : ∀ a : A, ((1 : G), a) ∈ center (G × A) := by
    intro a
    exact (mem_center_prod_iff _).2 (one_mem _)
  refine ⟨⟨⟨fun x => ⟨(1, x.2), hmem x.2⟩, ?_⟩, ?_⟩, ?_⟩
  · rfl
  · intro a b
    apply Subtype.ext
    simp
  · rintro ⟨⟨g, a⟩, hz⟩
    apply Subtype.ext
    have : g ∈ center G := (mem_center_prod_iff _).1 hz
    rw [h] at this
    simp [Subgroup.mem_bot.1 this]

end Basic

section Structure

variable {r : G →* center G} (hr : ∀ z : center G, r z = z)
include hr

theorem retraction_apply_mem_ker (g : G) : g * ((r g : G))⁻¹ ∈ r.ker := by
  simp only [MonoidHom.mem_ker, map_mul, map_inv]
  rw [hr (r g)]
  simp

/-- A retraction onto the center exhibits `Z(G)` as a direct factor: `ker r` and `Z(G)` are
complementary subgroups. -/
theorem isComplement_ker_center : IsComplement' r.ker (center G) := by
  constructor
  · rintro ⟨⟨n₁, hn₁⟩, ⟨z₁, hz₁⟩⟩ ⟨⟨n₂, hn₂⟩, ⟨z₂, hz₂⟩⟩ h
    simp only at h
    have hz : z₁ = z₂ := by
      have := congrArg r h
      rw [map_mul, map_mul, MonoidHom.mem_ker.1 hn₁, MonoidHom.mem_ker.1 hn₂] at this
      have e₁ : r z₁ = ⟨z₁, hz₁⟩ := hr ⟨z₁, hz₁⟩
      have e₂ : r z₂ = ⟨z₂, hz₂⟩ := hr ⟨z₂, hz₂⟩
      rw [e₁, e₂, one_mul, one_mul] at this
      exact congrArg Subtype.val this
    subst hz
    have : n₁ = n₂ := mul_right_cancel h
    subst this
    rfl
  · intro g
    exact ⟨(⟨g * ((r g : G))⁻¹, retraction_apply_mem_ker hr g⟩, ⟨(r g : G), (r g).2⟩), by
      simp⟩

/-- The kernel of a retraction onto the center is a centerless subgroup. -/
theorem center_ker_eq_bot : center (r.ker : Subgroup G) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hx⟩ hxc
  have hxZ : x ∈ center G := by
    rw [mem_center_iff]
    intro g
    -- write `g = n * z` with `n ∈ ker r` and `z` central
    set z : G := (r g : G) with hz
    set n : G := g * z⁻¹ with hn
    have hnk : n ∈ r.ker := retraction_apply_mem_ker hr g
    have hgn : g = n * z := by simp [hn]
    have h1 : n * x = x * n := by
      have := mem_center_iff.1 hxc ⟨n, hnk⟩
      exact congrArg Subtype.val this
    have h2 : ∀ y : G, z * y = y * z := fun y => (mem_center_iff.1 (r g).2 y).symm
    calc g * x = n * (z * x) := by rw [hgn]; group
      _ = n * (x * z) := by rw [h2 x]
      _ = (n * x) * z := by group
      _ = (x * n) * z := by rw [h1]
      _ = x * (n * z) := by group
      _ = x * g := by rw [← hgn]
  have hdisj : Disjoint (r.ker) (center G) := (isComplement_ker_center hr).disjoint
  have hx1 : x = 1 := by
    have hmem : x ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.1 hdisj]; exact ⟨hx, hxZ⟩
    simpa using hmem
  exact Subgroup.mem_bot.2 (Subtype.ext hx1)

end Structure

section Characterization

/-- A retraction onto the center exists exactly when the center is a direct factor, i.e. when
it admits a complement. -/
theorem hasCenterRetraction_iff_isComplement (G : Type*) [Group G] :
    HasCenterRetraction G ↔ ∃ N : Subgroup G, IsComplement' N (center G) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r.ker, isComplement_ker_center hr⟩
  · rintro ⟨N, hN⟩
    classical
    set e := Equiv.ofBijective _ hN with he
    have key : ∀ g : G, ((e.symm g).1 : G) * ((e.symm g).2 : G) = g := fun g =>
      e.apply_symm_apply g
    have huniq : ∀ (x : N × center G) (g : G), (x.1 : G) * (x.2 : G) = g → e.symm g = x := by
      intro x g hx
      apply e.injective
      rw [Equiv.apply_symm_apply]
      exact hx.symm
    refine ⟨⟨⟨fun g => (e.symm g).2, ?_⟩, ?_⟩, ?_⟩
    · show (e.symm (1 : G)).2 = 1
      rw [huniq (1, 1) 1 (by simp)]
    · intro a b
      show (e.symm (a * b)).2 = (e.symm a).2 * (e.symm b).2
      have hz : ∀ (z : center G) (y : G), (z : G) * y = y * z := fun z y =>
        (mem_center_iff.1 z.2 y).symm
      have : e.symm (a * b) = ((e.symm a).1 * (e.symm b).1, (e.symm a).2 * (e.symm b).2) := by
        refine huniq _ _ ?_
        calc ((e.symm a).1 : G) * (e.symm b).1 * (((e.symm a).2 : G) * (e.symm b).2)
            = ((e.symm a).1 : G) * ((((e.symm b).1 : G) * ((e.symm a).2 : G)) *
              ((e.symm b).2 : G)) := by group
          _ = ((e.symm a).1 : G) * ((((e.symm a).2 : G) * ((e.symm b).1 : G)) *
              ((e.symm b).2 : G)) := by rw [hz (e.symm a).2 ((e.symm b).1 : G)]
          _ = (((e.symm a).1 : G) * ((e.symm a).2 : G)) *
              (((e.symm b).1 : G) * ((e.symm b).2 : G)) := by group
          _ = a * b := by rw [key a, key b]
      rw [this]
    · intro z
      show (e.symm (z : G)).2 = z
      rw [huniq (1, z) _ (by simp)]

end Characterization

section PGroups

/-- **No nonabelian finite `p`-group retracts onto its center.**
If a finite `p`-group `G` admits a retraction onto its center, then `G` is abelian. -/
theorem commute_of_hasCenterRetraction_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (h : HasCenterRetraction G) : ∀ a b : G, a * b = b * a := by
  obtain ⟨r, hr⟩ := h
  have hker : center (r.ker : Subgroup G) = ⊥ := center_ker_eq_bot hr
  have hbot : r.ker = ⊥ := by
    by_contra hne
    have : Nontrivial (r.ker : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hp : IsPGroup p (r.ker : Subgroup G) := hG.to_subgroup _
    have := hp.center_nontrivial
    rw [hker] at this
    exact (not_nontrivial_iff_subsingleton.2 (by infer_instance)) this
  -- `ker r = ⊥` forces every element to be central
  intro a b
  have : ∀ g : G, g ∈ center G := by
    intro g
    have hg : g * ((r g : G))⁻¹ ∈ r.ker := retraction_apply_mem_ker hr g
    rw [hbot, Subgroup.mem_bot] at hg
    have : g = (r g : G) := by
      have := mul_inv_eq_one.1 hg
      exact this
    rw [this]
    exact (r g).2
  exact mem_center_iff.1 (this b) a

/-- Contrapositive form: a nonabelian finite `p`-group has no retraction onto its center. -/
theorem not_hasCenterRetraction_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (hnc : ¬ ∀ a b : G, a * b = b * a) : ¬ HasCenterRetraction G :=
  fun h => hnc (commute_of_hasCenterRetraction_of_isPGroup hG h)

end PGroups

section Examples

/-- The quaternion group `Q₈` does not retract onto its center. -/
theorem not_hasCenterRetraction_quaternion : ¬ HasCenterRetraction (QuaternionGroup 2) := by
  have hcard : Nat.card (QuaternionGroup 2) = 2 ^ 3 := by
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hp : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card hcard
  refine not_hasCenterRetraction_of_isPGroup (p := 2) hp ?_
  decide

/-- The dihedral group `D₄` of order `8` does not retract onto its center. -/
theorem not_hasCenterRetraction_dihedral_four : ¬ HasCenterRetraction (DihedralGroup 4) := by
  have hcard : Nat.card (DihedralGroup 4) = 2 ^ 3 := by
    simp [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hp : IsPGroup 2 (DihedralGroup 4) := IsPGroup.of_card hcard
  refine not_hasCenterRetraction_of_isPGroup (p := 2) hp ?_
  decide

/-- Dihedral groups of order `2n` with `n` odd, `n ≠ 1`, are centerless, hence retract onto
their (trivial) center. -/
theorem hasCenterRetraction_dihedral_odd {n : ℕ} (hn : Odd n) (h1 : n ≠ 1) :
    HasCenterRetraction (DihedralGroup n) :=
  hasCenterRetraction_of_center_eq_bot (DihedralGroup.center_eq_bot_of_odd_ne_one hn h1)

/-- A product of a centerless dihedral group with an abelian group retracts onto its center. -/
theorem hasCenterRetraction_dihedral_odd_prod {n : ℕ} (hn : Odd n) (h1 : n ≠ 1)
    (A : Type*) [CommGroup A] : HasCenterRetraction (DihedralGroup n × A) :=
  hasCenterRetraction_prod_of_center_eq_bot (DihedralGroup.center_eq_bot_of_odd_ne_one hn h1)

end Examples
