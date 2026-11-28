import Mathlib
import YangMills.LiteralSU2PlaquetteIndexReflection

/-!
# Global positive/negative plaquette bijection for the even-time Wilson cut

The local reflected-link and plaquette transport is already exact.  This file
pays the remaining GLOBAL finite-set geometry:

  image(theta_P, P_plus) = P_minus.

The proof uses the literal numerical time coordinate on ZMod (2n).  Spatial
plaquettes reflect their base time t to 2n-1-t.  Temporal noncrossing
plaquettes reflect their base to 2n-2-t because orientation reversal moves
the reflected base one time step backward.

Combining this finite-set identity with the arbitrary-set product transport
closes

  W_minus(U) = W_plus(Theta U)

on the literal link field.
-/

namespace RequestProject.YangMills

private theorem neZero_two_mul (n : ℕ) [NeZero n] :
    2 * n ≠ 0 := by
  omega

private theorem reflected_site_time_val_of_positive
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (hx : (x su2TimeDirection).val < n) :
    (su2EvenTimeReflectSite x su2TimeDirection).val =
      2 * n - 1 - (x su2TimeDirection).val := by
  haveI : NeZero (2 * n) := ⟨neZero_two_mul n⟩
  have hn : 0 < n := NeZero.pos n
  have hpluslt :
      (x su2TimeDirection).val + 1 < 2 * n := by omega
  have hplusval :
      (x su2TimeDirection + 1).val =
        (x su2TimeDirection).val + 1 := by
    simpa using
      (ZMod.val_add_of_lt
        (a := x su2TimeDirection) (b := (1 : ZMod (2 * n)))
        (by simpa using hpluslt))
  have hplusne : x su2TimeDirection + 1 ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [hplusval] at hv
    simp at hv
    omega
  rw [show
    su2EvenTimeReflectSite x su2TimeDirection =
      -(x su2TimeDirection + 1) by
        simp [su2EvenTimeReflectSite]
        ring]
  rw [ZMod.neg_val, if_neg hplusne, hplusval]
  omega

private theorem reflected_temporal_base_time_val_of_positive_noncross
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (hx : (x su2TimeDirection).val < n)
    (hBoundary :
      (x su2TimeDirection).val ≠ n - 1) :
    (su2ShiftBackward
      (su2EvenTimeReflectSite x)
      su2TimeDirection su2TimeDirection).val =
      2 * n - 2 - (x su2TimeDirection).val := by
  haveI : NeZero (2 * n) := ⟨neZero_two_mul n⟩
  have hn : 0 < n := NeZero.pos n
  have hx2 : (x su2TimeDirection).val + 2 ≤ n := by omega
  have hlt : (x su2TimeDirection).val + 2 < 2 * n := by omega
  have hsumval :
      (x su2TimeDirection + 2).val =
        (x su2TimeDirection).val + 2 := by
    have htwo : ((2 : ZMod (2 * n))).val = 2 := by
      rw [ZMod.val_natCast_of_lt]
      omega
    rw [ZMod.val_add_of_lt]
    · simp [htwo]
    · simpa [htwo] using hlt
  have hsumne : x su2TimeDirection + 2 ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [hsumval] at hv
    simp at hv
    omega
  have halgebra :
      su2ShiftBackward
        (su2EvenTimeReflectSite x)
        su2TimeDirection su2TimeDirection =
      -(x su2TimeDirection + 2) := by
    simp [su2ShiftBackward, su2EvenTimeReflectSite]
    ring
  rw [halgebra, ZMod.neg_val, if_neg hsumne, hsumval]
  omega

private theorem reflected_index_positive_to_negative
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2EvenTimePositivePlaquettes n) :
    su2EvenTimeReflectPlaquetteIndex p ∈
      su2EvenTimeNegativePlaquettes n := by
  classical
  have hpdata := Finset.mem_filter.mp hp
  have hphys : p ∈ su2FourDimensionalPlaquettes (2 * n) := hpdata.1
  have hpos := hpdata.2
  have hnoncross := hpos.1
  have htime := hpos.2
  have hdirections :=
    su2_even_time_reflect_plaquette_index_directions p
  have hphysRef :
      su2EvenTimeReflectPlaquetteIndex p ∈
        su2FourDimensionalPlaquettes (2 * n) := by
    simp only [su2FourDimensionalPlaquettes,
      Finset.mem_filter, Finset.mem_univ, true_and] at hphys ⊢
    simpa [hdirections] using hphys
  refine Finset.mem_filter.mpr ⟨hphysRef, ?_, ?_⟩
  · intro hcrossRef
    have hback :
        su2EvenTimeCrossingPlaquette n p := by
      have hμ :
          p.2.1 = su2TimeDirection := by
        have hrefμ := hcrossRef.1
        simpa [hdirections] using hrefμ
      have hInv :=
        congrArg
          (fun q =>
            su2EvenTimeCrossingPlaquette n q)
          (su2_even_time_reflect_plaquette_index_involutive p)
      -- Numerical boundary slabs are invariant under the plaquette-index
      -- involution; discharge directly from the two possible time values.
      unfold su2EvenTimeCrossingPlaquette at hcrossRef ⊢
      constructor
      · exact hμ
      · rcases hcrossRef.2 with h | h
        · left
          by_cases hpμ : p.2.1 = su2TimeDirection
          · rw [show
              su2EvenTimeReflectPlaquetteIndex p =
                (su2ShiftBackward
                  (su2EvenTimeReflectSite p.1)
                  su2TimeDirection, p.2.1, p.2.2) by
                    simp [su2EvenTimeReflectPlaquetteIndex, hpμ]] at h
            have hval :=
              reflected_temporal_base_time_val_of_positive_noncross
                n p.1 htime (by
                  intro hb
                  exact hnoncross ⟨hpμ, Or.inl hb⟩)
            simp only at hval
            omega
          · exact False.elim (hpμ hμ)
        · right
          by_cases hpμ : p.2.1 = su2TimeDirection
          · rw [show
              su2EvenTimeReflectPlaquetteIndex p =
                (su2ShiftBackward
                  (su2EvenTimeReflectSite p.1)
                  su2TimeDirection, p.2.1, p.2.2) by
                    simp [su2EvenTimeReflectPlaquetteIndex, hpμ]] at h
            have hval :=
              reflected_temporal_base_time_val_of_positive_noncross
                n p.1 htime (by
                  intro hb
                  exact hnoncross ⟨hpμ, Or.inl hb⟩)
            simp only at hval
            omega
          · exact False.elim (hpμ hμ)
    exact hnoncross hback
  · by_cases hμ : p.2.1 = su2TimeDirection
    · rw [show
        su2EvenTimeReflectPlaquetteIndex p =
          (su2ShiftBackward
            (su2EvenTimeReflectSite p.1)
            su2TimeDirection, p.2.1, p.2.2) by
              simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
      have hb :
          (p.1 su2TimeDirection).val ≠ n - 1 := by
        intro hb
        exact hnoncross ⟨hμ, Or.inl hb⟩
      have hv :=
        reflected_temporal_base_time_val_of_positive_noncross
          n p.1 htime hb
      simpa using (show
        n ≤ 2 * n - 2 - (p.1 su2TimeDirection).val by
          have hn : 0 < n := NeZero.pos n
          omega)
    · rw [show
        su2EvenTimeReflectPlaquetteIndex p =
          (su2EvenTimeReflectSite p.1, p.2.1, p.2.2) by
            simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
      have hv := reflected_site_time_val_of_positive n p.1 htime
      simpa [hv] using (show
        n ≤ 2 * n - 1 - (p.1 su2TimeDirection).val by
          have hn : 0 < n := NeZero.pos n
          omega)

private theorem reflected_site_time_val_of_negative
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (hx : n ≤ (x su2TimeDirection).val) :
    (su2EvenTimeReflectSite x su2TimeDirection).val =
      2 * n - 1 - (x su2TimeDirection).val := by
  haveI : NeZero (2 * n) := ⟨neZero_two_mul n⟩
  have hmax : (x su2TimeDirection).val ≤ 2 * n - 1 := by
    have hv := (x su2TimeDirection).val_lt
    omega
  by_cases htop : (x su2TimeDirection).val = 2 * n - 1
  · rw [show
      su2EvenTimeReflectSite x su2TimeDirection =
        -(x su2TimeDirection + 1) by
          simp [su2EvenTimeReflectSite]
          ring]
    have hsumzero : x su2TimeDirection + 1 = 0 := by
      apply ZMod.val_injective
      rw [ZMod.val_add]
      have hone : ((1 : ZMod (2 * n))).val = 1 := by
        rw [ZMod.val_natCast_of_lt]
        omega
      rw [hone, htop]
      simp
    rw [hsumzero]
    simp
  · have hpluslt :
        (x su2TimeDirection).val + 1 < 2 * n := by omega
    have hplusval :
        (x su2TimeDirection + 1).val =
          (x su2TimeDirection).val + 1 := by
      simpa using
        (ZMod.val_add_of_lt
          (a := x su2TimeDirection) (b := (1 : ZMod (2 * n)))
          (by simpa using hpluslt))
    have hplusne : x su2TimeDirection + 1 ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [hplusval] at hv
      simp at hv
      omega
    rw [show
      su2EvenTimeReflectSite x su2TimeDirection =
        -(x su2TimeDirection + 1) by
          simp [su2EvenTimeReflectSite]
          ring]
    rw [ZMod.neg_val, if_neg hplusne, hplusval]
    omega

private theorem reflected_temporal_base_time_val_of_negative_noncross
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (hx : n ≤ (x su2TimeDirection).val)
    (hTop : (x su2TimeDirection).val ≠ 2 * n - 1) :
    (su2ShiftBackward
      (su2EvenTimeReflectSite x)
      su2TimeDirection su2TimeDirection).val =
      2 * n - 2 - (x su2TimeDirection).val := by
  haveI : NeZero (2 * n) := ⟨neZero_two_mul n⟩
  have htheta :=
    reflected_site_time_val_of_negative n x hx
  have hthetaPos :
      1 ≤ (su2EvenTimeReflectSite x su2TimeDirection).val := by
    rw [htheta]
    have hv := (x su2TimeDirection).val_lt
    omega
  change
    ((su2EvenTimeReflectSite x su2TimeDirection) - 1).val =
      2 * n - 2 - (x su2TimeDirection).val
  rw [ZMod.val_sub]
  · rw [htheta]
    omega
  · simpa using hthetaPos

private theorem reflected_index_negative_to_positive
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2EvenTimeNegativePlaquettes n) :
    su2EvenTimeReflectPlaquetteIndex p ∈
      su2EvenTimePositivePlaquettes n := by
  classical
  have hpdata := Finset.mem_filter.mp hp
  have hphys : p ∈ su2FourDimensionalPlaquettes (2 * n) := hpdata.1
  have hneg := hpdata.2
  have hnoncross := hneg.1
  have htime := hneg.2
  have hdirections :=
    su2_even_time_reflect_plaquette_index_directions p
  have hphysRef :
      su2EvenTimeReflectPlaquetteIndex p ∈
        su2FourDimensionalPlaquettes (2 * n) := by
    simp only [su2FourDimensionalPlaquettes,
      Finset.mem_filter, Finset.mem_univ, true_and] at hphys ⊢
    simpa [hdirections] using hphys
  refine Finset.mem_filter.mpr ⟨hphysRef, ?_, ?_⟩
  · intro hcrossRef
    have hμ :
        p.2.1 = su2TimeDirection := by
      have hrefμ := hcrossRef.1
      simpa [hdirections] using hrefμ
    have htop :
        (p.1 su2TimeDirection).val ≠ 2 * n - 1 := by
      intro ht
      exact hnoncross ⟨hμ, Or.inr ht⟩
    rw [show
      su2EvenTimeReflectPlaquetteIndex p =
        (su2ShiftBackward
          (su2EvenTimeReflectSite p.1)
          su2TimeDirection, p.2.1, p.2.2) by
            simp [su2EvenTimeReflectPlaquetteIndex, hμ]] at hcrossRef
    have hrefval :=
      reflected_temporal_base_time_val_of_negative_noncross
        n p.1 htime htop
    rcases hcrossRef.2 with h | h
    · have hn : 0 < n := NeZero.pos n
      omega
    · have hn : 0 < n := NeZero.pos n
      omega
  · by_cases hμ : p.2.1 = su2TimeDirection
    · have htop :
          (p.1 su2TimeDirection).val ≠ 2 * n - 1 := by
        intro ht
        exact hnoncross ⟨hμ, Or.inr ht⟩
      rw [show
        su2EvenTimeReflectPlaquetteIndex p =
          (su2ShiftBackward
            (su2EvenTimeReflectSite p.1)
            su2TimeDirection, p.2.1, p.2.2) by
              simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
      have hv :=
        reflected_temporal_base_time_val_of_negative_noncross
          n p.1 htime htop
      have hn : 0 < n := NeZero.pos n
      omega
    · rw [show
        su2EvenTimeReflectPlaquetteIndex p =
          (su2EvenTimeReflectSite p.1, p.2.1, p.2.2) by
            simp [su2EvenTimeReflectPlaquetteIndex, hμ]]
      have hv :=
        reflected_site_time_val_of_negative n p.1 htime
      have hn : 0 < n := NeZero.pos n
      omega

/--
Global finite-set bijection: reflection sends the literal positive
noncrossing plaquette family exactly onto the negative family.
-/
theorem su2_even_time_positive_image_eq_negative
    (n : ℕ) [NeZero n] :
    (su2EvenTimePositivePlaquettes n).image
        su2EvenTimeReflectPlaquetteIndex =
      su2EvenTimeNegativePlaquettes n := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact reflected_index_positive_to_negative n p hp
  · intro q hq
    have hp := reflected_index_negative_to_positive n q hq
    refine Finset.mem_image.mpr
      ⟨su2EvenTimeReflectPlaquetteIndex q, hp, ?_⟩
    exact su2_even_time_reflect_plaquette_index_involutive q

/--
The remaining pure-Wilson global half-action identity is now unconditional.
-/
theorem su2_negative_half_eq_reflected_positive_half
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct
        (su2EvenTimePositivePlaquettes n)
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2EvenTimeNegativePlaquettes n)
        links β := by
  exact su2_negative_half_eq_reflected_positive_half_of_index_image
    n (su2_even_time_positive_image_eq_negative n) links β

end RequestProject.YangMills
