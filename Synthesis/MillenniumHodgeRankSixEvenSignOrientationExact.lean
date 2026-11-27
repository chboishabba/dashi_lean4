import Mathlib

/-!
# Rank-six orientation: proper support has an even-sign annihilator

On a diagonal orthogonal basis of the relative rank-six space, changing
signs at two distinct axes is in SO, over any characteristic-zero splitting
field. A coefficient on a proper nonempty set of distinct basis addresses
is therefore zero in any SO-invariant tensor. This is the elementary
coefficient proof used for the lower-codimension product obstruction on
the actual cubic RM K3 sixth power. It needs no invariant-theory black box.
The algebraic cycle existence and Hodge group assumptions are not proved
by this finite coordinate lemma.
-/

namespace DASHI.Hodge.Orientation

def evenFlip (i j k : Fin 6) : ℚ :=
  if k = i ∨ k = j then -1 else 1

theorem evenFlip_prod_proper (s : Finset (Fin 6)) (i j : Fin 6)
    (hi : i ∈ s) (hj : j ∉ s) :
    (∏ k ∈ s, evenFlip i j k) = -1 := by
  have hij : i ≠ j := by
    intro he
    exact hj (he ▸ hi)
  have hone : (∏ k ∈ s.erase i, evenFlip i j k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    have hkj : k ≠ j := by
      intro he
      exact hj (he ▸ (Finset.mem_erase.mp hk).2)
    simp [evenFlip, hki, hkj]
  have hp := Finset.prod_erase_mul (s := s) (f := evenFlip i j) hi
  rw [hone] at hp
  simpa [evenFlip] using hp.symm

/-- Exact annihilation of a distinct-address coefficient using an even sign
flip at one used and one unused axis. -/
theorem coefficient_zero_of_evenFlip
    (s : Finset (Fin 6)) (i j : Fin 6) (hi : i ∈ s) (hj : j ∉ s)
    (c : ℚ) (hinv : c = (∏ k ∈ s, evenFlip i j k) * c) :
    c = 0 := by
  rw [evenFlip_prod_proper s i j hi hj] at hinv
  linarith

/-- All proper nonempty supports are killed. There is no such flip for full
support, so the six-form orientation is not erroneously annihilated. -/
theorem proper_support_coefficient_zero (s : Finset (Fin 6))
    (hne : s.Nonempty) (hproper : s ≠ Finset.univ) (c : ℚ)
    (hinv : ∀ i j : Fin 6, i ≠ j →
      c = (∏ k ∈ s, evenFlip i j k) * c) :
    c = 0 := by
  obtain ⟨i, hi⟩ := hne
  have hout : ∃ j : Fin 6, j ∉ s := by
    by_contra hn
    push_neg at hn
    apply hproper
    ext j
    simp [hn j]
  obtain ⟨j, hj⟩ := hout
  have hij : i ≠ j := by
    intro he
    exact hj (he ▸ hi)
  exact coefficient_zero_of_evenFlip s i j hi hj c (hinv i j hij)

/-- Full orientation survives every distinct two-axis sign change. -/
theorem full_support_evenFlip (i j : Fin 6) (hij : i ≠ j) :
    (∏ k : Fin 6, evenFlip i j k) = 1 := by
  have hi : i ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset (Fin 6)).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hp := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin 6)))
    (f := evenFlip i j) hi
  have hq : (∏ k ∈ (Finset.univ : Finset (Fin 6)).erase i, evenFlip i j k) = -1 := by
    have he : (∏ k ∈ ((Finset.univ : Finset (Fin 6)).erase i).erase j,
        evenFlip i j k) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [evenFlip, hki, hkj]
    have hh := Finset.prod_erase_mul
      (s := (Finset.univ : Finset (Fin 6)).erase i) (f := evenFlip i j) hj
    rw [he] at hh
    simpa [evenFlip] using hh.symm
  rw [hq] at hp
  simpa [evenFlip] using hp.symm

end DASHI.Hodge.Orientation
