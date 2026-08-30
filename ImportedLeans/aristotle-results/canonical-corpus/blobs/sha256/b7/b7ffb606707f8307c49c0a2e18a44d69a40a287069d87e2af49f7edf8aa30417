import RequestProject.CenterRetractionMore
import RequestProject.CenterRetractionProd

/-!
# A structure theorem for groups retracting onto their center

`RequestProject.CenterRetraction` shows that `HasCenterRetraction G` is equivalent to the
center admitting a complement, and `RequestProject.CenterRetractionMore` produces from a
retraction an isomorphism `G ≃* ker r × Z(G)` with `ker r` centerless. This file records the
sharpened equivalence and its converse:

* `hasCenterRetraction_iff_exists_centerless_complement` : `G` retracts onto its center **iff**
  the center has a *centerless* complement;
* `hasCenterRetraction_of_mulEquiv_prod` : conversely, any group isomorphic to a product
  `N × A` with `N` centerless and `A` abelian retracts onto its center;
* `hasCenterRetraction_iff_mulEquiv_prod` : so, in the form of a splitting statement,
  `G` retracts onto its center iff `G ≃* N × Z(G)` for some centerless subgroup `N ≤ G`.
-/

open Subgroup

variable {G : Type*} [Group G]

/-- **A group retracts onto its center iff the center has a centerless complement.** -/
theorem hasCenterRetraction_iff_exists_centerless_complement :
    HasCenterRetraction G ↔ ∃ N : Subgroup G, IsComplement' N (center G) ∧ center N = ⊥ := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r.ker, isComplement_ker_center hr, center_ker_eq_bot hr⟩
  · rintro ⟨N, hN, -⟩
    exact (hasCenterRetraction_iff_isComplement G).2 ⟨N, hN⟩

/-- A product of a centerless group and an abelian group retracts onto its center; hence so
does any group isomorphic to such a product. -/
theorem hasCenterRetraction_of_mulEquiv_prod {N A : Type*} [Group N] [CommGroup A]
    (hN : center N = ⊥) (e : G ≃* N × A) : HasCenterRetraction G :=
  hasCenterRetraction_congr e.symm (hasCenterRetraction_prod_of_center_eq_bot hN)

/-- **Splitting form of the criterion.** `G` retracts onto its center exactly when it splits
as a direct product of a centerless subgroup and its center. -/
theorem hasCenterRetraction_iff_mulEquiv_prod :
    HasCenterRetraction G ↔
      ∃ N : Subgroup G, center N = ⊥ ∧ Nonempty (G ≃* (N × center G)) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r.ker, center_ker_eq_bot hr, ⟨(mulEquivKerProdCenter hr).symm⟩⟩
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact hasCenterRetraction_of_mulEquiv_prod hN e
