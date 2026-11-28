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


/-- On the selected K3^k × C × D Kunneth chart, every algebraic
factor has even degree. A degree-one curve slot cannot be split
from the other degree-one curve slot by such a factor. -/
theorem mixedCurveSlotsTogether (a c x y : ℕ)
    (hx : x ≤ 1) (hy : y ≤ 1) (h : 2*a+x+y = 2*c) :
    x = y := by omega

/-- With two or three primitive K3 slots, a positive pure K3
factor is odd or consists of one symmetric pair. In the actual
SO6 representation odd factors vanish, and alternation kills the
symmetric pair. This arithmetic lemma retains the degree constraint. -/
theorem mixedPureFactorShape (n : ℕ) (hn : 0 < n) (hmax : n ≤ 3) :
    n % 2 = 1 ∨ n = 2 := by omega

/-- Newton's formula, followed by an actual linear cohomology
projector that annihilates the lower-codimension products.
The existence of a bundle with nonzero projected fourth Chern
class is not supplied by this identity. -/
theorem mixed_ch4_projection
    {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module ℚ V]
    (P : R →ₗ[ℚ] V) (c1 c2 c3 c4 : R)
    (h1 : P (c1^4) = 0)
    (h2 : P (c1^2*c2) = 0)
    (h3 : P (c2^2) = 0)
    (h4 : P (c1*c3) = 0) :
    P ((1/24 : ℚ) • c1^4 + (-1/6 : ℚ) • (c1^2*c2) +
      (1/12 : ℚ) • c2^2 + (1/6 : ℚ) • (c1*c3) +
      (-1/6 : ℚ) • c4) = (-1/6 : ℚ) • P c4 := by
  simp [h1, h2, h3, h4]

theorem mixed_ch4_nonzero_iff {V : Type*} [AddCommGroup V] [Module ℚ V]
    (c : V) : (-1/6 : ℚ) • c ≠ 0 ↔ c ≠ 0 := by
  simp [smul_eq_zero]

end DASHI.Hodge.Orientation
