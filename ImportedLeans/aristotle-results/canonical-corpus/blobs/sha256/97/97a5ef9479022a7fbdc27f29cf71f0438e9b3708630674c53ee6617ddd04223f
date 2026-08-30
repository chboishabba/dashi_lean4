/-
# Row A1a — reduction of the whole near/far input to one scalar form factor

The one-loop vacuum polarisation of the lattice theory is transverse, so on the
literal lattice momentum atoms it has the form

    N_{μν}(p)  =  K_{μν}(p) · Π(p),      K_{μν}(p) = δ_{μν} p̂² − p̂_μ p̂_ν,

with `K` the literal Wilson inverse propagator of `LatticeMomentum.lean` and `Π`
a scalar form factor.  (`N = N_W + N_FP + N_H`: the three channels are summed
*before* this factorisation, which is exactly the "cancellation before absolute
values" discipline — the individual channels are not transverse, only the sum
is.)

The content of this file is the estimate `|K_{μν}(p)| ≤ p̂²`, valid on all of
`ℝ⁴` with no region restriction, and its two consequences:

* near box: `|Π(p)| ≤ A p̂²` with `A ≤ 1/40` gives the per-orbit near bound
  `2/5` demanded by the shell budget;
* far shell: `|Π(p)| ≤ 25/128` gives the per-orbit far bound `25/64`; and in
  fact on the far shell one may alternatively use the proved denominator floor.

So the entire remaining A1a physical input is *one* scalar inequality on *one*
scalar function, rather than separate near-cofactor and far-numerator data.
-/
import RequestProject.YangMills.NearFarRegions

namespace YangMills

open Finset

/-- Two distinct axes are dominated by the full `p̂²`. -/
lemma phat_sq_pair_le_phatSq (p : Fin 4 → ℝ) {μ ν : Fin 4} (h : μ ≠ ν) :
    (phat (p μ)) ^ 2 + (phat (p ν)) ^ 2 ≤ phatSq p := by
  have hpair : ∑ i ∈ ({μ, ν} : Finset (Fin 4)), (phat (p i)) ^ 2
      = (phat (p μ)) ^ 2 + (phat (p ν)) ^ 2 := Finset.sum_pair h
  have hsub : ({μ, ν} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i : Fin 4 => (phat (p i)) ^ 2)
    hsub (fun i _ _ => sq_nonneg _)
  rw [hpair] at this
  exact this

/-- **The literal transverse tensor is bounded by the literal denominator.**
`|K_{μν}(p)| ≤ p̂²` for every `p` and every pair of indices. -/
theorem abs_wilsonInversePropagator_le (p : Fin 4 → ℝ) (μ ν : Fin 4) :
    |wilsonInversePropagator p μ ν| ≤ phatSq p := by
  by_cases h : μ = ν
  · subst h
    have h1 : (phat (p μ)) ^ 2 ≤ phatSq p := phat_sq_le_phatSq p μ
    have h2 : wilsonInversePropagator p μ μ = phatSq p - (phat (p μ)) ^ 2 := by
      simp [wilsonInversePropagator]; ring
    rw [h2, abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (phat (p μ))]
  · have h2 : wilsonInversePropagator p μ ν = -(phat (p μ) * phat (p ν)) := by
      simp [wilsonInversePropagator, h]
    have hpair := phat_sq_pair_le_phatSq p h
    have hamgm : |phat (p μ) * phat (p ν)|
        ≤ ((phat (p μ)) ^ 2 + (phat (p ν)) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|phat (p μ)| - |phat (p ν)|), sq_abs (phat (p μ)),
        sq_abs (phat (p ν)), abs_nonneg (phat (p μ)), abs_nonneg (phat (p ν))]
    rw [h2, abs_neg]
    linarith [phatSq_nonneg p]
/-- The transverse factorisation of the joint one-loop numerator. -/
def IsTransverseFactorisation (N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (Pi : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ p μ ν, N p μ ν = wilsonInversePropagator p μ ν * Pi p

/-- A transversely factorised numerator inherits the Ward identity. -/
theorem transverse_factorisation_ward {N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {Pi : (Fin 4 → ℝ) → ℝ} (hN : IsTransverseFactorisation N Pi) (p : Fin 4 → ℝ)
    (μ : Fin 4) : ∑ ν : Fin 4, phat (p ν) * N p μ ν = 0 := by
  have : ∀ ν : Fin 4, phat (p ν) * N p μ ν
      = (phat (p ν) * wilsonInversePropagator p μ ν) * Pi p := by
    intro ν; rw [hN p μ ν]; ring
  rw [Finset.sum_congr rfl (fun ν _ => this ν), ← Finset.sum_mul,
    wilsonInversePropagator_transverse p μ, zero_mul]

/-- **Near reduction.**  A form-factor bound `|Π(p)| ≤ A p̂²` gives the
Ward-compensated quartic bound for every tensor component. -/
theorem quartic_bound_of_formFactor {N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {Pi : (Fin 4 → ℝ) → ℝ} (hN : IsTransverseFactorisation N Pi)
    {A : ℝ} {p : Fin 4 → ℝ} (hPi : |Pi p| ≤ A * phatSq p) (μ ν : Fin 4) :
    |N p μ ν| ≤ A * (phatSq p) ^ 2 := by
  have hK := abs_wilsonInversePropagator_le p μ ν
  have hnn := phatSq_nonneg p
  have hPinn : 0 ≤ A * phatSq p := le_trans (abs_nonneg _) hPi
  rw [hN p μ ν, abs_mul]
  calc |wilsonInversePropagator p μ ν| * |Pi p|
      ≤ phatSq p * (A * phatSq p) := by
        apply mul_le_mul hK hPi (abs_nonneg _) hnn
    _ = A * (phatSq p) ^ 2 := by ring

/-- **The near per-orbit bound from the form factor alone.**  `A ≤ 1/40` gives
exactly the near per-orbit density bound `2/5` used by the shell budget. -/
theorem near_perOrbit_bound_of_formFactor {N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {Pi : (Fin 4 → ℝ) → ℝ} (hN : IsTransverseFactorisation N Pi)
    {A : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1 / 40) {p : Fin 4 → ℝ}
    (hPi : |Pi p| ≤ A * phatSq p) (μ ν : Fin 4) :
    |N p μ ν / phatSq p| ≤ 2 / 5 :=
  near_quotient_bound_two_fifths hA hA' (quartic_bound_of_formFactor hN hPi μ ν)

/-- **The far per-orbit bound from the form factor alone.**  On the far shell no
denominator floor is even needed: `|Π| ≤ 25/128` already gives `25/64`. -/
theorem far_perOrbit_bound_of_formFactor {N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {Pi : (Fin 4 → ℝ) → ℝ} (hN : IsTransverseFactorisation N Pi)
    {p : Fin 4 → ℝ} (hPi : |Pi p| ≤ 25 / 128) (μ ν : Fin 4) :
    |N p μ ν / phatSq p| ≤ 25 / 64 := by
  rcases eq_or_lt_of_le (phatSq_nonneg p) with hz | hpos
  · have hz0 : phatSq p = 0 := hz.symm
    simp [hz0]
    norm_num
  · have hK := abs_wilsonInversePropagator_le p μ ν
    rw [hN p μ ν, abs_div, abs_of_pos hpos, abs_mul, div_le_iff₀ hpos]
    have h1 : |wilsonInversePropagator p μ ν| * |Pi p| ≤ phatSq p * (25 / 128) :=
      mul_le_mul hK hPi (abs_nonneg _) (phatSq_nonneg p)
    linarith

/-- **Far route through the proved denominator floor.**  If instead one only
knows a numerator sup `|N| ≤ 1` on the far shell, the proved sine gap floors the
denominator and gives the same per-orbit bound `25/64`. -/
theorem far_perOrbit_bound_of_numerator_sup {N : ℝ} {p : Fin 4 → ℝ}
    (hBZ : InBZ p) (hfar : FarRegion (2 / 5) p) (hN : |N| ≤ 1) :
    |N / phatSq p| ≤ 25 / 64 :=
  far_quotient_bound_unit hBZ hfar hN

end YangMills
