import RequestProject.FrobeniusOrbit

/-!
# Hilbert 90 for finite fields: the elements of norm one

This is the multiplicative counterpart of `ArtinSchreier.lean`.  For a finite field `K` with
`p ^ n` elements the Frobenius orbit product (norm) `frobNorm p n x = ∏_{k<n} x ^ (p ^ k)` is a
homomorphism `Kˣ → 𝔽_pˣ`; here we determine its kernel:

* `range_pow_eq_ker_pow` : in a finite cyclic group of order `d * s`, the image of `x ↦ x ^ d` is
  exactly the kernel of `x ↦ x ^ s`;
* `frobNorm_eq_one_iff` / `frobNorm_eq_one_iff_div` : **`frobNorm p n x = 1` if and only if
  `x = y ^ (p-1) = y ^ p / y = σ(y)/y` for some `y ≠ 0`**, where `σ` is the Frobenius — the
  finite-field case of Hilbert's Theorem 90.

Compare `ArtinSchreier.range_asHom_eq_ker_traceHom`: there the image of `y ↦ y ^ p - y = σ(y) - y`
is the kernel of the trace, here the image of `y ↦ y ^ p / y = σ(y)/y` is the kernel of the norm.
-/

open Finset

namespace FrobeniusPrimeSubfield

/-- **In a finite cyclic group of order `d * s`, the image of the `d`-th power map is exactly the
kernel of the `s`-th power map.** -/
theorem range_pow_eq_ker_pow {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {d s : ℕ}
    (hd0 : 0 < d) (h : d * s = Nat.card G) :
    (powMonoidHom d : G →* G).range = (powMonoidHom s : G →* G).ker := by
  classical
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [Nat.mul_zero] at h
      exact absurd h.symm Nat.card_pos.ne'
    · exact hs
  have hcard_range : Nat.card ((powMonoidHom d : G →* G).range) = s := by
    rw [IsCyclic.card_powMonoidHom_range, ← h, Nat.gcd_eq_right ⟨s, rfl⟩,
      Nat.mul_div_cancel_left _ hd0]
  have hcard_ker : Nat.card ((powMonoidHom s : G →* G).ker) = s :=
    card_ker_pow_of_dvd G ⟨d, by rw [← h, mul_comm]⟩ hs0
  exact Subgroup.eq_of_le_of_card_ge
    (by
      rintro x ⟨y, rfl⟩
      simp only [MonoidHom.mem_ker, powMonoidHom_apply] at *
      rw [← pow_mul, h]
      exact pow_card_eq_one')
    (by rw [hcard_range, hcard_ker])

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Fintype K] {n : ℕ}

omit [CharP K p] in
/-- **Hilbert 90 for a finite field.**  A nonzero element has Frobenius orbit product (norm) `1`
if and only if it is a `(p-1)`-st power. -/
theorem frobNorm_eq_one_iff (hK : Nat.card K = p ^ n) {x : K} (hx : x ≠ 0) :
    frobNorm p n x = 1 ↔ ∃ y : K, y ≠ 0 ∧ y ^ (p - 1) = x := by
  classical
  set s : ℕ := ∑ k ∈ range n, p ^ k with hs
  have hcardU : Nat.card Kˣ = p ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hmul : (p - 1) * s = Nat.card Kˣ := by
    rw [hcardU, mul_comm]
    exact geom_sum_mul_pred p n hp.out.pos
  have hkey := range_pow_eq_ker_pow (G := Kˣ) (d := p - 1) (s := s)
    (by have := hp.out.two_le; omega) hmul
  set u : Kˣ := Units.mk0 x hx with hu
  constructor
  · intro h
    have hus : u ^ s = 1 := by
      apply Units.ext
      have : (u : K) ^ s = x ^ s := rfl
      rw [Units.val_pow_eq_pow_val, this, ← frobNorm_eq_pow, h, Units.val_one]
    have hmem : u ∈ (powMonoidHom s : Kˣ →* Kˣ).ker := by
      simpa [MonoidHom.mem_ker] using hus
    rw [← hkey] at hmem
    obtain ⟨v, hv⟩ := hmem
    refine ⟨(v : K), v.ne_zero, ?_⟩
    have := congrArg (fun w : Kˣ => (w : K)) hv
    simpa [powMonoidHom, hu] using this
  · rintro ⟨y, hy, rfl⟩
    set v : Kˣ := Units.mk0 y hy with hv
    have hmem : u ∈ (powMonoidHom (p - 1) : Kˣ →* Kˣ).range := by
      refine ⟨v, ?_⟩
      apply Units.ext
      simp [powMonoidHom, hu, hv]
    rw [hkey, MonoidHom.mem_ker] at hmem
    have hus : (u : K) ^ s = 1 := by
      have := congrArg (fun w : Kˣ => (w : K)) hmem
      simpa [powMonoidHom] using this
    rw [frobNorm_eq_pow]
    exact hus

omit [CharP K p] in
/-- **Hilbert 90, in the form `x = σ(y)/y`.**  A nonzero element of a finite field has norm `1`
if and only if it is of the form `y ^ p / y`, the ratio of `y` and its Frobenius image. -/
theorem frobNorm_eq_one_iff_div (hK : Nat.card K = p ^ n) {x : K} (hx : x ≠ 0) :
    frobNorm p n x = 1 ↔ ∃ y : K, y ≠ 0 ∧ y ^ p / y = x := by
  have hpow : ∀ y : K, y ≠ 0 → y ^ p / y = y ^ (p - 1) := fun y hy => by
    rw [div_eq_iff hy, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  rw [frobNorm_eq_one_iff hK hx]
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by rw [hpow y hy]⟩

end FrobeniusPrimeSubfield
