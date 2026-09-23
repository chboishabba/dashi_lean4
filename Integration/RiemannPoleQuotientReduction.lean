import Integration.RiemannPoleQuotientTerminal

/-!
# From the high theorem to RH (§§2, 9 of the manuscript)

This module carries out, for Mathlib's *actual* Riemann zeta function, the
low/high compilation of `Riemann_Pole_Quotient_Reduction_2026.pdf` §9.

What is genuinely proved here:

* `zeta_zero_one_sub` — the functional-equation symmetry of the zero set inside
  the critical strip, deduced from `completedRiemannZeta_one_sub`;
* `re_lt_one_of_zeta_eq_zero`, `re_pos_of_zeta_eq_zero` — every zero of `ζ`
  other than the trivial ones and the pole lies in the open critical strip
  (the second uses the functional equation, `Γ ≠ 0`, the zeros of `cos`, and
  Mathlib's nonvanishing theorem on `Re s ≥ 1`);
* `riemannHypothesis_of_low_and_high` — **Theorem 9.1**: the published
  low-region statement plus the high-ordinate contradiction imply Mathlib's
  `RiemannHypothesis`;
* `riemannHypothesis_of_low_and_poleQuotient` — the same with the high side
  supplied in the manuscript's pole–quotient form (Theorem 8.1 data at every
  high off-line zero).

What is **not** proved here, and is carried as an explicit hypothesis of every
theorem below:

* `LowRegionVerified` — the Platt–Trudgian computation (a published verified
  computation, not formalized in this corpus);
* `HighOrdinateContradiction` / the pole–quotient realization hypothesis —
  Hypothesis 10.1 of the manuscript, the remaining analytic wall.

No unconditional proof of the Riemann hypothesis is claimed or obtained.
-/

namespace Integration.RiemannPoleQuotient

open Complex

/-! ## 1. The exact low/high partition -/

/-- The Platt–Trudgian verified height `T_PT = 3,000,175,332,800`
(Definition 2.1 of the manuscript). -/
def plattTrudgianHeight : ℝ := 3000175332800

theorem plattTrudgianHeight_pos : 0 < plattTrudgianHeight := by
  unfold plattTrudgianHeight; norm_num

/-- A nontrivial zero is *low* when its ordinate lies in the verified region. -/
def IsLowZero (s : ℂ) : Prop := |s.im| ≤ plattTrudgianHeight

/-- The published low-region statement: every zero of `ζ` in the open critical
strip with ordinate in the verified region lies on the critical line.  This is
Platt–Trudgian's verified computation; it is a hypothesis here. -/
def LowRegionVerified : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → IsLowZero s → s.re = 1 / 2

/-- The high-ordinate theorem the manuscript reduces to: no zero of `ζ` in the
open critical strip with `Re s > 1/2` has ordinate beyond the verified region.
This is the remaining analytic content (Hypothesis 10.1); it is a hypothesis
here. -/
def HighOrdinateContradiction : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 1 / 2 < s.re → s.re < 1 → ¬ IsLowZero s → False

/-! ## 2. Zeros of `ζ` and the critical strip -/

/-- Inside the right half plane `Re s > 0`, the zeros of `ζ` are exactly the
zeros of the completed zeta `Λ`. -/
theorem zeta_eq_zero_iff_completed {s : ℂ} (h0 : 0 < s.re) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs : s ≠ 0 := fun h => by simp [h] at h0
  rw [riemannZeta_def_of_ne_zero hs, div_eq_zero_iff]
  simp [Gammaℝ_ne_zero_of_re_pos h0]

/-- **Functional-equation symmetry of the zero set in the strip.**  If `s` is a
zero of `ζ` in the open critical strip, then so is `1 - s`. -/
theorem zeta_zero_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have h0' : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  rw [zeta_eq_zero_iff_completed h0', completedRiemannZeta_one_sub,
    ← zeta_eq_zero_iff_completed h0]
  exact hz

/-- Every zero of `ζ` has `Re s < 1` (Mathlib's nonvanishing theorem). -/
theorem re_lt_one_of_zeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0) : s.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz

/-- Every zero of `ζ` other than the trivial zeros `-2(n+1)` has `Re s > 0`.

The proof uses the functional equation `ζ(1-w) = 2 (2π)^{-w} Γ(w) cos(πw/2) ζ(w)`
at `w = 1 - s`: all factors except the cosine are nonvanishing for `Re w ≥ 1`,
so the cosine must vanish, which forces `w` to be an odd positive integer and
`s = -2k`.  The value `s = 0` is excluded by `ζ(0) = -1/2`, and `k ≥ 1` is a
trivial zero. -/
theorem re_pos_of_zeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hle
  push_neg at hle
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have h1 : w.re = -(n : ℝ) := by rw [h]; simp
    have h2 : (1 : ℝ) ≤ -(n : ℝ) := h1 ▸ hwre
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have hs : s = 1 - w := by rw [hw]; ring
    rw [hs, h]; ring
  have hfe := riemannZeta_one_sub hwn hw1
  have hsw : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [hsw, hz] at hfe
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpow : ((2 : ℂ) * Real.pi) ^ (-w) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push_neg
    intro h
    exfalso
    simp at h
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact absurd h3 hpow
        · exact absurd h'' hΓ
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hk
  have hsk : s = -2 * (k : ℂ) := by rw [hw] at hk; linear_combination -hk
  have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
  have hkpos : 0 ≤ (k : ℝ) := by rw [hkre] at hle; linarith
  have hkne : k ≠ 0 := by
    intro h; apply hs0; rw [hsk, h]; simp
  have hk1 : 1 ≤ k := by
    have : (0 : ℤ) ≤ k := by exact_mod_cast hkpos
    omega
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    have h : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h
  rw [hsk, hcast]; ring

/-! ## 3. Theorem 9.1 -/

/-- **Theorem 9.1 (terminal reduction to RH).**  Assume the published
low-region verification and the high-ordinate contradiction.  Then Mathlib's
`RiemannHypothesis` holds.

Both assumptions are genuine inputs: `LowRegionVerified` is the Platt–Trudgian
computation and `HighOrdinateContradiction` is the manuscript's remaining
analytic wall.  Neither is proved in this corpus, so this theorem is a
*reduction*, not a proof of RH. -/
theorem riemannHypothesis_of_low_and_high
    (hLow : LowRegionVerified) (hHigh : HighOrdinateContradiction) :
    RiemannHypothesis := by
  intro s hz htriv _
  have h0 : 0 < s.re := re_pos_of_zeta_eq_zero hz htriv
  have h1 : s.re < 1 := re_lt_one_of_zeta_eq_zero hz
  by_contra hne
  by_cases hlow : IsLowZero s
  · exact hne (hLow s hz h0 h1 hlow)
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- reflect through the critical line with the functional equation
      have hz' : riemannZeta (1 - s) = 0 := zeta_zero_one_sub h0 h1 hz
      have hre' : (1 - s).re = 1 - s.re := by simp
      have hlow' : ¬ IsLowZero (1 - s) := by
        unfold IsLowZero at hlow ⊢
        simpa [abs_neg] using hlow
      exact hHigh (1 - s) hz' (by rw [hre']; linarith) (by rw [hre']; linarith) hlow'
    · exact hHigh s hz hgt h1 hlow

/-! ## 4. The high side in pole–quotient form -/

/-- The manuscript's realization hypothesis (Hypothesis 10.1 in scalar form):
to every high off-critical-line zero one can attach pole–quotient response data
satisfying the exact balance (1), the near/far split (2) and the strict high
inequality (3). -/
def PoleQuotientRealization : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 1 / 2 < s.re → s.re < 1 → ¬ IsLowZero s →
    ∃ R : PoleQuotientResponse, R.Balance ∧ R.NearFarSplit ∧ R.StrictHigh

/-- The pole–quotient realization implies the high-ordinate contradiction
(Theorem 8.1 applied at each high off-line zero). -/
theorem highOrdinateContradiction_of_realization (h : PoleQuotientRealization) :
    HighOrdinateContradiction := by
  intro s hz hre h1 hlow
  obtain ⟨R, hbal, hsplit, hstrict⟩ := h s hz hre h1 hlow
  exact terminal_contradiction hbal hsplit hstrict

/-- **The manuscript's architecture, end to end.**  Published low region plus
pole–quotient realization at every high off-line zero gives RH.  The second
hypothesis is precisely the unproved analytic wall of the programme. -/
theorem riemannHypothesis_of_low_and_poleQuotient
    (hLow : LowRegionVerified) (hReal : PoleQuotientRealization) :
    RiemannHypothesis :=
  riemannHypothesis_of_low_and_high hLow (highOrdinateContradiction_of_realization hReal)

end Integration.RiemannPoleQuotient
