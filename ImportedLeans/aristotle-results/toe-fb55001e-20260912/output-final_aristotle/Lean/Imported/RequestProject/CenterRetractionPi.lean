import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore
import RequestProject.CenterRetractionProd

/-!
# Arbitrary products and retractions onto the center

`CenterRetractionProd.lean` settled binary products.  This file does the same for an arbitrary
(possibly infinite) family of groups `G : ι → Type*`:

* `mem_center_pi_iff` : an element of `∀ i, G i` is central iff each coordinate is central,
  i.e. `Z(∏ i, G i) = ∏ i, Z(G i)`;
* `hasCenterRetraction_pi_iff` : **`∏ i, G i` retracts onto its center iff every factor does.**
  The easy direction assembles the coordinatewise retractions; the converse restricts a
  retraction of the product along the coordinate embedding `G i → ∏ j, G j`.

Applications: an arbitrary product of centerless groups (for instance a product of symmetric
groups) retracts onto its center, while no product having a genuine dicyclic factor does.
-/

open Subgroup

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]

/-- **The center of a product is the product of the centers.** -/
theorem mem_center_pi_iff (x : ∀ i, G i) :
    x ∈ center (∀ i, G i) ↔ ∀ i, x i ∈ center (G i) := by
  constructor
  · intro hx i
    rw [mem_center_iff]
    intro g
    have h := congrFun (mem_center_iff.1 hx (Pi.mulSingle i g)) i
    simpa using h
  · intro hx
    rw [mem_center_iff]
    intro g
    funext i
    exact mem_center_iff.1 (hx i) (g i)

/-- If every factor retracts onto its center, so does the product. -/
theorem hasCenterRetraction_pi (h : ∀ i, HasCenterRetraction (G i)) :
    HasCenterRetraction (∀ i, G i) := by
  choose r hr using h
  refine ⟨⟨⟨fun x => ⟨fun i => (r i (x i) : G i), (mem_center_pi_iff _).2 fun i => (r i (x i)).2⟩,
    ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    funext i
    show ((r i ((1 : ∀ j, G j) i)) : G i) = 1
    rw [show (1 : ∀ j, G j) i = 1 from rfl, map_one]
    rfl
  · intro a b
    apply Subtype.ext
    funext i
    show ((r i ((a * b) i)) : G i) = (r i (a i) : G i) * (r i (b i) : G i)
    rw [show (a * b) i = a i * b i from rfl, map_mul]
    rfl
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    funext i
    have hzi : z i ∈ center (G i) := (mem_center_pi_iff _).1 hz i
    show ((r i (z i)) : G i) = z i
    exact congrArg Subtype.val (hr i ⟨z i, hzi⟩)

/-- If a product retracts onto its center, so does each factor. -/
theorem hasCenterRetraction_of_pi (h : HasCenterRetraction (∀ i, G i)) (i : ι) :
    HasCenterRetraction (G i) := by
  obtain ⟨r, hr⟩ := h
  have hcen : ∀ g : G i, ((r (Pi.mulSingle i g) : ∀ j, G j)) i ∈ center (G i) := fun g =>
    (mem_center_pi_iff _).1 (r (Pi.mulSingle i g)).2 i
  refine ⟨⟨⟨fun g => ⟨((r (Pi.mulSingle i g) : ∀ j, G j)) i, hcen g⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    show ((r (Pi.mulSingle i (1 : G i)) : ∀ j, G j)) i = 1
    rw [Pi.mulSingle_one, map_one]
    rfl
  · intro a b
    apply Subtype.ext
    show ((r (Pi.mulSingle i (a * b)) : ∀ j, G j)) i
      = ((r (Pi.mulSingle i a) : ∀ j, G j)) i * ((r (Pi.mulSingle i b) : ∀ j, G j)) i
    rw [Pi.mulSingle_mul, map_mul]
    rfl
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    have hzc : Pi.mulSingle i z ∈ center (∀ j, G j) := by
      refine (mem_center_pi_iff _).2 fun j => ?_
      by_cases hj : j = i
      · subst hj
        simpa using hz
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact one_mem _
    have h := hr ⟨Pi.mulSingle i z, hzc⟩
    have h2 := congrArg (fun x => (Subtype.val x) i) h
    simpa using h2

/-- **A product of groups retracts onto its center iff every factor does.** -/
theorem hasCenterRetraction_pi_iff :
    HasCenterRetraction (∀ i, G i) ↔ ∀ i, HasCenterRetraction (G i) :=
  ⟨fun h => hasCenterRetraction_of_pi h, hasCenterRetraction_pi⟩

/-- An arbitrary product of centerless groups retracts onto its center (the center of the
product is trivial). -/
theorem hasCenterRetraction_pi_of_center_eq_bot (h : ∀ i, center (G i) = ⊥) :
    HasCenterRetraction (∀ i, G i) :=
  hasCenterRetraction_pi fun i => hasCenterRetraction_of_center_eq_bot (h i)

/-- No product having a genuine dicyclic group among its factors retracts onto its center. -/
theorem not_hasCenterRetraction_pi_of_quaternion {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (i : ι)
    (e : G i ≃* QuaternionGroup n) : ¬ HasCenterRetraction (∀ j, G j) := fun h =>
  QuaternionGroup.not_hasCenterRetraction hn0 hn1
    (hasCenterRetraction_congr e (hasCenterRetraction_of_pi h i))
