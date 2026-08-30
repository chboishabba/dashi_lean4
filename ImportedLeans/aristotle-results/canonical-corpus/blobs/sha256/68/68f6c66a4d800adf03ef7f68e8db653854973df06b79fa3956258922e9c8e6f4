import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore

/-!
# Small groups, and squarefree orders

Two positive results complementing the obstructions of the other files, and the resulting
statement that `8` is the smallest order at which a retraction onto the center can fail.

* `Nat.coprime_div_of_squarefree` : for `d ∣ n` with `n` squarefree, `d` and `n / d` are coprime.
* `hasCenterRetraction_of_squarefree_card` : **every finite group of squarefree order retracts
  onto its center** — the order of the center is automatically coprime to its index, so the
  Schur–Zassenhaus criterion applies.
* `hasCenterRetraction_of_card_lt_eight` : every group of order at most `7` retracts onto its
  center (the only non-squarefree order below `8` is `4`, and groups of order `p²` are abelian).
* `eight_is_least_order_without_center_retraction` : together with the quaternion group `Q₈`,
  this pins the first failure at order `8`.
-/

open Subgroup

namespace CenterRetractionSmall

/-- If `n` is squarefree and `d ∣ n`, then `d` is coprime to the cofactor `n / d`. -/
theorem Nat.coprime_div_of_squarefree {n d : ℕ} (hn : Squarefree n) (hd : d ∣ n) :
    Nat.Coprime d (n / d) := by
  by_contra hcop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hcop
  have h1 : p ∣ d := hpg.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ n / d := hpg.trans (Nat.gcd_dvd_right _ _)
  have hsq : p * p ∣ n := by
    calc p * p ∣ d * (n / d) := Nat.mul_dvd_mul h1 h2
    _ = n := Nat.mul_div_cancel' hd
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hn p hsq))

/-- **Every finite group of squarefree order retracts onto its center.**  Indeed `|Z(G)|`
divides `|G|`, so squarefreeness makes it coprime to the index `[G : Z(G)]`, and the
Schur–Zassenhaus criterion produces the retraction. -/
theorem hasCenterRetraction_of_squarefree_card {G : Type*} [Group G] [Finite G]
    (h : Squarefree (Nat.card G)) : HasCenterRetraction G := by
  refine hasCenterRetraction_of_coprime ?_
  have hmul : Nat.card (center G) * (center G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hdvd : Nat.card (center G) ∣ Nat.card G := ⟨_, hmul.symm⟩
  have hidx : (center G).index = Nat.card G / Nat.card (center G) := by
    rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [hidx]
  exact Nat.coprime_div_of_squarefree h hdvd

/-- **Every group of order less than `8` retracts onto its center.**  All such orders are
squarefree except `4`, and a group of order `p²` is abelian. -/
theorem hasCenterRetraction_of_card_lt_eight {G : Type*} [Group G] [Finite G]
    (h : Nat.card G < 8) : HasCenterRetraction G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hn : Nat.card G
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)
  · exact hasCenterRetraction_of_commute
      (IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [hn]; norm_num))
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)
  · exact hasCenterRetraction_of_squarefree_card (by rw [hn]; decide +kernel)

/-- The quaternion group `Q₈` has order `8`. -/
theorem card_quaternionGroup_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- **`8` is the least order at which a retraction onto the center can fail**: every group of
smaller order has one, and the quaternion group of order `8` has none. -/
theorem eight_is_least_order_without_center_retraction :
    (∀ (G : Type) [Group G] [Finite G], Nat.card G < 8 → HasCenterRetraction G) ∧
      Nat.card (QuaternionGroup 2) = 8 ∧ ¬ HasCenterRetraction (QuaternionGroup 2) :=
  ⟨fun _ _ _ h => hasCenterRetraction_of_card_lt_eight h,
    card_quaternionGroup_two, not_hasCenterRetraction_quaternion⟩

end CenterRetractionSmall
