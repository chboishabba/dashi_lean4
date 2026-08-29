import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore
import RequestProject.QuaternionCenterRetraction

/-!
# Isomorphism invariance and the exact behaviour under products

Two further structural facts about `HasCenterRetraction`:

* `hasCenterRetraction_congr` : the property is invariant under group isomorphism.
* `hasCenterRetraction_prod_iff` : a product retracts onto its center **iff both factors do**.
  One direction is `hasCenterRetraction_prod`; the new content is that the property is
  inherited by the factors, obtained by restricting a retraction of `G × H` to `G × 1`.

As an application, no group of the form `QuaternionGroup n × A` (`n ≠ 0, 1`, `A` arbitrary)
retracts onto its center.
-/

open Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- An isomorphism carries central elements to central elements. -/
theorem mem_center_mulEquiv (e : G ≃* H) {g : G} (hg : g ∈ center G) : e g ∈ center H := by
  rw [mem_center_iff]
  intro h
  have := mem_center_iff.1 hg (e.symm h)
  have h2 := congrArg e this
  simpa using h2

/-- Retracting onto the center is invariant under isomorphism. -/
theorem hasCenterRetraction_congr (e : G ≃* H) (hG : HasCenterRetraction G) :
    HasCenterRetraction H := by
  obtain ⟨r, hr⟩ := hG
  refine ⟨⟨⟨fun h => ⟨e (r (e.symm h) : G), mem_center_mulEquiv e (r (e.symm h)).2⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    simp [map_mul]
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    have hz' : e.symm z ∈ center G := mem_center_mulEquiv e.symm hz
    show e (r (e.symm z) : G) = z
    rw [show ((r (e.symm z) : G)) = e.symm z from congrArg Subtype.val (hr ⟨e.symm z, hz'⟩)]
    simp

/-- If a product retracts onto its center, so does its first factor. -/
theorem hasCenterRetraction_of_prod_left (h : HasCenterRetraction (G × H)) :
    HasCenterRetraction G := by
  obtain ⟨r, hr⟩ := h
  have hcen : ∀ g : G, ((r (g, 1) : G × H)).1 ∈ center G := fun g =>
    ((mem_center_prod_iff' _).1 (r (g, 1)).2).1
  refine ⟨⟨⟨fun g => ⟨((r (g, 1) : G × H)).1, hcen g⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    show ((r ((1 : G), (1 : H)) : G × H)).1 = 1
    rw [show ((1 : G), (1 : H)) = 1 from rfl, map_one]
    rfl
  · intro a b
    apply Subtype.ext
    show ((r ((a * b : G), (1 : H)) : G × H)).1
      = ((r (a, 1) : G × H)).1 * ((r (b, 1) : G × H)).1
    rw [show ((a * b : G), (1 : H)) = (a, 1) * (b, 1) by simp, map_mul]
    rfl
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    have hzc : ((z : G), (1 : H)) ∈ center (G × H) :=
      (mem_center_prod_iff' _).2 ⟨hz, one_mem _⟩
    have := hr ⟨(z, 1), hzc⟩
    exact congrArg (fun x => (Subtype.val x).1) this

/-- If a product retracts onto its center, so does its second factor. -/
theorem hasCenterRetraction_of_prod_right (h : HasCenterRetraction (G × H)) :
    HasCenterRetraction H :=
  hasCenterRetraction_of_prod_left (hasCenterRetraction_congr (MulEquiv.prodComm : G × H ≃* H × G) h)

/-- **A product retracts onto its center iff both factors do.** -/
theorem hasCenterRetraction_prod_iff :
    HasCenterRetraction (G × H) ↔ HasCenterRetraction G ∧ HasCenterRetraction H :=
  ⟨fun h => ⟨hasCenterRetraction_of_prod_left h, hasCenterRetraction_of_prod_right h⟩,
    fun h => hasCenterRetraction_prod h.1 h.2⟩

/-- No product having a genuine dicyclic group as a factor retracts onto its center. -/
theorem not_hasCenterRetraction_quaternion_prod {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    ¬ HasCenterRetraction (QuaternionGroup n × H) := fun h =>
  QuaternionGroup.not_hasCenterRetraction hn0 hn1 (hasCenterRetraction_of_prod_left h)
