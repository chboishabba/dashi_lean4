import Mathlib
import YangMills.LiteralSU2PlaquetteReflectionTransport

/-!
# Literal plaquette-index reflection and Wilson product transport

The orientation-sensitive link reflection induces one explicit involution
on physical plaquette indices:

* spatial plaquette base x -> theta x;
* temporal plaquette base x -> theta x - e0.

The direction pair is unchanged.  This file proves the index map is
involutive and that the Wilson cost on reflected links at p equals the
original Wilson cost at reflectedIndex(p).  Consequently, for EVERY finite
plaquette family S, the Wilson product on theta(U) over S is exactly the
Wilson product on U over reflectedIndex(S).

The remaining global geometric statement is therefore only
  image(reflectedIndex, P_plus) = P_minus
for the chosen numerical even-time cut.
-/

namespace RequestProject.YangMills

def su2EvenTimeReflectPlaquetteIndex
    {n : ℕ}
    (p : SU2LiteralPlaquetteIndex (2 * n)) :
    SU2LiteralPlaquetteIndex (2 * n) :=
  if h : p.2.1 = su2TimeDirection then
    (su2ShiftBackward
      (su2EvenTimeReflectSite p.1)
      su2TimeDirection, p.2.1, p.2.2)
  else
    (su2EvenTimeReflectSite p.1, p.2.1, p.2.2)

theorem su2_even_time_reflect_plaquette_index_directions
    {n : ℕ}
    (p : SU2LiteralPlaquetteIndex (2 * n)) :
    (su2EvenTimeReflectPlaquetteIndex p).2 = p.2 := by
  unfold su2EvenTimeReflectPlaquetteIndex
  split_ifs <;> rfl

theorem su2_even_time_reflect_plaquette_index_involutive
    {n : ℕ}
    (p : SU2LiteralPlaquetteIndex (2 * n)) :
    su2EvenTimeReflectPlaquetteIndex
      (su2EvenTimeReflectPlaquetteIndex p) = p := by
  rcases p with ⟨x, μ, ν⟩
  by_cases hμ : μ = su2TimeDirection
  · simp only [su2EvenTimeReflectPlaquetteIndex, hμ, ↓reduceDIte]
    rw [su2_backward_reflect_backward_reflect]
  · simp only [su2EvenTimeReflectPlaquetteIndex, hμ, ↓reduceDIte]
    rw [su2_even_time_reflect_site_involutive]

theorem su2_even_time_reflect_plaquette_index_injective
    {n : ℕ} :
    Function.Injective
      (@su2EvenTimeReflectPlaquetteIndex n) := by
  intro p q h
  have hp := congrArg
    (@su2EvenTimeReflectPlaquetteIndex n) h
  simpa [su2_even_time_reflect_plaquette_index_involutive] using hp

/--
Same-object cost transport for any physical oriented plaquette.
The order condition mu<nu rules out "spatial mu, temporal nu".
-/
theorem su2_reflected_link_plaquette_cost_eq_index_reflection
    {n : ℕ} [NeZero n]
    (links : SU2TorusLinks (2 * n))
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2FourDimensionalPlaquettes (2 * n)) :
    su2PositivePlaquetteCost
      (su2Plaquette (su2EvenTimeReflectLinks links)
        p.1 p.2.1 p.2.2) =
    su2PositivePlaquetteCost
      (su2Plaquette links
        (su2EvenTimeReflectPlaquetteIndex p).1
        (su2EvenTimeReflectPlaquetteIndex p).2.1
        (su2EvenTimeReflectPlaquetteIndex p).2.2) := by
  by_cases hμ : p.2.1 = su2TimeDirection
  · rw [show
      su2EvenTimeReflectPlaquetteIndex p =
        (su2ShiftBackward
          (su2EvenTimeReflectSite p.1)
          su2TimeDirection, p.2.1, p.2.2) by
            simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
    subst p
    simpa using
      su2_reflected_temporal_plaquette_cost
        links _ _ (by
          intro hν
          have hp' := hp
          simp only [su2FourDimensionalPlaquettes,
            Finset.mem_filter, Finset.mem_univ, true_and] at hp'
          subst hν
          exact (Nat.lt_irrefl _) hp')
  · have hν : p.2.2 ≠ su2TimeDirection := by
      intro hν
      have ht := su2_temporal_plaquette_first_direction hp
        (Or.inr hν)
      exact hμ ht
    rw [show
      su2EvenTimeReflectPlaquetteIndex p =
        (su2EvenTimeReflectSite p.1, p.2.1, p.2.2) by
          simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
    exact su2_reflected_spatial_plaquette_cost
      links p.1 p.2.1 p.2.2 hμ hν

/--
Wilson product transport holds over an arbitrary physical plaquette set.
This is the finite multiplicative form needed for the global half-action.
-/
theorem su2_literal_wilson_product_reflection_transport
    {n : ℕ} [NeZero n]
    (S : Finset (SU2LiteralPlaquetteIndex (2 * n)))
    (hPhysical :
      ∀ p ∈ S, p ∈ su2FourDimensionalPlaquettes (2 * n))
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct S
      (su2EvenTimeReflectLinks links) β =
    su2LiteralWilsonProduct
      (S.image su2EvenTimeReflectPlaquetteIndex)
      links β := by
  classical
  unfold su2LiteralWilsonProduct
  rw [Finset.prod_image
    (@su2_even_time_reflect_plaquette_index_injective n).injOn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [su2_reflected_link_plaquette_cost_eq_index_reflection
    links p (hPhysical p hp)]

/--
The pure-Wilson global half identity follows from exactly one finite-set
geometric equality.  The next source-written theorem should discharge that
equality for the explicit even-time numerical cut.
-/
theorem su2_negative_half_eq_reflected_positive_half_of_index_image
    (n : ℕ) [NeZero n]
    (hImage :
      (su2EvenTimePositivePlaquettes n).image
          su2EvenTimeReflectPlaquetteIndex =
        su2EvenTimeNegativePlaquettes n)
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct
        (su2EvenTimePositivePlaquettes n)
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2EvenTimeNegativePlaquettes n)
        links β := by
  rw [su2_literal_wilson_product_reflection_transport]
  · rw [hImage]
  · intro p hp
    exact (Finset.mem_filter.mp hp).1

end RequestProject.YangMills
