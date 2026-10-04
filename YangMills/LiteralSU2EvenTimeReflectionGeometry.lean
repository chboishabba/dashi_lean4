import Mathlib
import YangMills.LiteralSU2PlaquetteHalfHolonomyFactorization

/-!
# Literal even-period time-reflection geometry for the 4D SU(2) torus

For period 2n choose Euclidean time direction 0 and site reflection
theta(t,x)=(-t-1,x) mod 2n. The map is involutive. Spatial shifts
commute with theta, while a forward time shift is reflected to a backward
time shift.

The physical plaquette set is partitioned into positive noncrossing,
negative noncrossing, and the two periodic boundary-crossing time slabs.
The actual full finite Wilson Boltzmann product then factors exactly into
those three pieces. The crossing piece is identified with the same literal
half-holonomy positive kernel already proved reflection-positive.

The remaining same-object Wilson theorem is orientation-sensitive link
reflection: identify the negative noncrossing factor as the reflected copy
of the positive factor. No continuum claim is made here.
-/

namespace RequestProject.YangMills

def su2TimeDirection : Fin 4 := ⟨0, by decide⟩

def su2ShiftBackward {L : ℕ}
    (x : SU2TorusSite L) (direction : Fin 4) : SU2TorusSite L :=
  Function.update x direction (x direction - 1)

def su2EvenTimeReflectSite {n : ℕ}
    (x : SU2TorusSite (2 * n)) : SU2TorusSite (2 * n) :=
  Function.update x su2TimeDirection (-x su2TimeDirection - 1)

theorem su2_even_time_reflect_site_involutive
    {n : ℕ} (x : SU2TorusSite (2 * n)) :
    su2EvenTimeReflectSite (su2EvenTimeReflectSite x) = x := by
  classical
  funext i
  by_cases hi : i = su2TimeDirection
  · subst i
    simp [su2EvenTimeReflectSite]
    ring
  · simp [su2EvenTimeReflectSite, Function.update_noteq hi]

theorem su2_even_time_reflect_spatial_shift
    {n : ℕ} (x : SU2TorusSite (2 * n))
    (direction : Fin 4) (hSpatial : direction ≠ su2TimeDirection) :
    su2EvenTimeReflectSite (su2Shift x direction) =
      su2Shift (su2EvenTimeReflectSite x) direction := by
  classical
  funext i
  by_cases hiTime : i = su2TimeDirection
  · subst i
    simp [su2EvenTimeReflectSite, su2Shift,
      Function.update_noteq hSpatial]
  · by_cases hiDir : i = direction
    · subst i
      simp [su2EvenTimeReflectSite, su2Shift,
        Function.update_same, Function.update_noteq hSpatial,
        Function.update_noteq hiTime]
    · simp [su2EvenTimeReflectSite, su2Shift,
        Function.update_noteq hiTime, Function.update_noteq hiDir]

theorem su2_even_time_reflect_forward_time_shift
    {n : ℕ} (x : SU2TorusSite (2 * n)) :
    su2EvenTimeReflectSite (su2Shift x su2TimeDirection) =
      su2ShiftBackward (su2EvenTimeReflectSite x) su2TimeDirection := by
  classical
  funext i
  by_cases hi : i = su2TimeDirection
  · subst i
    simp [su2EvenTimeReflectSite, su2Shift, su2ShiftBackward]
    ring
  · simp [su2EvenTimeReflectSite, su2Shift, su2ShiftBackward,
      Function.update_noteq hi]

theorem su2_temporal_plaquette_first_direction
    {n : ℕ} [NeZero n]
    {p : SU2LiteralPlaquetteIndex (2 * n)}
    (hp : p ∈ su2FourDimensionalPlaquettes (2 * n))
    (hTemporal :
      p.2.1 = su2TimeDirection ∨ p.2.2 = su2TimeDirection) :
    p.2.1 = su2TimeDirection := by
  simp only [su2FourDimensionalPlaquettes,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hTemporal with h | h
  · exact h
  · rw [h] at hp
    have : p.2.1.val < 0 := by simpa [su2TimeDirection] using hp
    omega

def su2EvenTimeCrossingPlaquette
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) : Prop :=
  p.2.1 = su2TimeDirection ∧
    ((p.1 su2TimeDirection).val = n - 1 ∨
     (p.1 su2TimeDirection).val = 2 * n - 1)

def su2EvenTimePositiveNoncrossingPlaquette
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) : Prop :=
  ¬ su2EvenTimeCrossingPlaquette n p ∧
    (p.1 su2TimeDirection).val < n

def su2EvenTimeNegativeNoncrossingPlaquette
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) : Prop :=
  ¬ su2EvenTimeCrossingPlaquette n p ∧
    n ≤ (p.1 su2TimeDirection).val

def su2EvenTimeCrossingPlaquettes
    (n : ℕ) [NeZero n] :
    Finset (SU2LiteralPlaquetteIndex (2 * n)) :=
  (su2FourDimensionalPlaquettes (2 * n)).filter
    (su2EvenTimeCrossingPlaquette n)

def su2EvenTimePositivePlaquettes
    (n : ℕ) [NeZero n] :
    Finset (SU2LiteralPlaquetteIndex (2 * n)) :=
  (su2FourDimensionalPlaquettes (2 * n)).filter
    (su2EvenTimePositiveNoncrossingPlaquette n)

def su2EvenTimeNegativePlaquettes
    (n : ℕ) [NeZero n] :
    Finset (SU2LiteralPlaquetteIndex (2 * n)) :=
  (su2FourDimensionalPlaquettes (2 * n)).filter
    (su2EvenTimeNegativeNoncrossingPlaquette n)

theorem su2_even_time_cut_pairwise_disjoint
    (n : ℕ) [NeZero n] :
    Disjoint (su2EvenTimePositivePlaquettes n)
      (su2EvenTimeNegativePlaquettes n) ∧
    Disjoint (su2EvenTimePositivePlaquettes n)
      (su2EvenTimeCrossingPlaquettes n) ∧
    Disjoint (su2EvenTimeNegativePlaquettes n)
      (su2EvenTimeCrossingPlaquettes n) := by
  classical
  constructor
  · refine Finset.disjoint_left.mpr ?_
    intro p hp hn
    simp only [su2EvenTimePositivePlaquettes,
      su2EvenTimeNegativePlaquettes, Finset.mem_filter] at hp hn
    exact (Nat.not_lt_of_ge hn.2.2) hp.2.2
  constructor
  · refine Finset.disjoint_left.mpr ?_
    intro p hp hc
    simp only [su2EvenTimePositivePlaquettes,
      su2EvenTimeCrossingPlaquettes, Finset.mem_filter] at hp hc
    exact hp.2.1 hc.2
  · refine Finset.disjoint_left.mpr ?_
    intro p hn hc
    simp only [su2EvenTimeNegativePlaquettes,
      su2EvenTimeCrossingPlaquettes, Finset.mem_filter] at hn hc
    exact hn.2.1 hc.2

theorem su2_even_time_cut_partition
    (n : ℕ) [NeZero n] :
    (su2EvenTimePositivePlaquettes n ∪
      su2EvenTimeNegativePlaquettes n) ∪
        su2EvenTimeCrossingPlaquettes n =
      su2FourDimensionalPlaquettes (2 * n) := by
  classical
  ext p
  simp only [Finset.mem_union, su2EvenTimePositivePlaquettes,
    su2EvenTimeNegativePlaquettes, su2EvenTimeCrossingPlaquettes,
    Finset.mem_filter]
  constructor
  · intro h
    rcases h with (hp | hn) | hc
    · exact hp.1
    · exact hn.1
    · exact hc.1
  · intro hp
    by_cases hc : su2EvenTimeCrossingPlaquette n p
    · exact Or.inr ⟨hp, hc⟩
    · by_cases ht : (p.1 su2TimeDirection).val < n
      · exact Or.inl (Or.inl ⟨hp, hc, ht⟩)
      · exact Or.inl (Or.inr ⟨hp, hc, Nat.le_of_not_gt ht⟩)

def su2LiteralWilsonProduct
    {L : ℕ}
    (plaquettes : Finset (SU2LiteralPlaquetteIndex L))
    (links : SU2TorusLinks L) (β : ℝ) : ℝ :=
  ∏ p ∈ plaquettes,
    Real.exp (-(β *
      su2PositivePlaquetteCost
        (su2Plaquette links p.1 p.2.1 p.2.2)))

theorem su2_even_time_cut_wilson_product_partition
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n)) (β : ℝ) :
    su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n)) links β =
      su2LiteralWilsonProduct
          (su2EvenTimePositivePlaquettes n) links β *
      su2LiteralWilsonProduct
          (su2EvenTimeNegativePlaquettes n) links β *
      su2LiteralWilsonProduct
          (su2EvenTimeCrossingPlaquettes n) links β := by
  classical
  have hdis := su2_even_time_cut_pairwise_disjoint n
  have hPN :
      Disjoint (su2EvenTimePositivePlaquettes n)
        (su2EvenTimeNegativePlaquettes n) := hdis.1
  have hUnionCross :
      Disjoint
        (su2EvenTimePositivePlaquettes n ∪
          su2EvenTimeNegativePlaquettes n)
        (su2EvenTimeCrossingPlaquettes n) :=
    Finset.disjoint_union_left.mpr ⟨hdis.2.1, hdis.2.2⟩
  unfold su2LiteralWilsonProduct
  rw [← su2_even_time_cut_partition n,
    Finset.prod_union hUnionCross,
    Finset.prod_union hPN]
  ring

theorem su2_even_time_crossing_product_is_positive_kernel
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n)) (β : ℝ) :
    su2LiteralWilsonProduct
        (su2EvenTimeCrossingPlaquettes n) links β =
      su2WilsonCrossingPlaneKernel
        (su2EvenTimeCrossingPlaquettes n) β
        (su2LiteralCrossingFirstBoundary links)
        (su2LiteralCrossingSecondBoundary links) := by
  exact su2_literal_crossing_wilson_product_eq_kernel
    (su2EvenTimeCrossingPlaquettes n) links β

end RequestProject.YangMills
