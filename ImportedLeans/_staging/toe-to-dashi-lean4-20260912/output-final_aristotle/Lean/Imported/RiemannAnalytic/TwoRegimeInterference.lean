/-
**A two-regime interference envelope with no minimum-gap hypothesis.**

`TransverseDecay.lean` bounds the interference of a target zero with the rest of
the family by `2 y² K² / δ²`, where `δ` is an assumed *uniform* lower bound on
the ordinate separations.  Such a `δ` is the wrong normalization for `ζ`: the
mean spacing of the ordinates is `2π / log T → 0`, so a fixed positive `δ` is
not available.

This file removes the hypothesis.  Two bounds hold simultaneously for the
imaginary part of the extension of a real even taper:

* the flat (transverse Lipschitz) bound `|Im Φ(x+iy)| ≤ |y| · 2 M₁`, valid for
  *all* `x`, including `x = 0` (`abs_im_PhiExt_le_transverse`), and
* the decay bound `|Im Φ(x+iy)| ≤ |y| · K / |x|` (`abs_im_PhiExt_le_transverse_decay`),

whence the joint two-regime estimate

    |Im Φ(x+iy)| ≤ |y| · min (2 M₁, K / |x|)

(`abs_im_PhiKernel_le_two_regime`), which is finite even for arbitrarily close
ordinates.  Summing it against a *local counting* hypothesis — at most `N`
members of the family in each unit window of the ordinate difference, which is
what the Riemann–von Mangoldt count actually supplies — gives

    ∑ (Im Φ(w n))² ≤ N y² (4 M₁² + 2 K²)

(`mixedInterference_envelope_localCount`), with no separation hypothesis at all.
Combined with the one-sided Gram floor this yields the `δ`-free localization
ratio `interference_le_ratio_mul_gramDefect_localCount`.
-/
import RiemannAnalytic.TransverseDecay

namespace RiemannAnalytic

open MeasureTheory Complex

/-! ### The joint two-regime pointwise bound -/

/-- **Two-regime transverse bound.**  For a `C¹` real even taper the imaginary
part of the extension of `φ²` off the real axis obeys *both* a flat bound and a
`1/|x|` decay bound:

    |Im Φ_{φ²}(x+iy)| ≤ |y| · min (2 M₁, K / |x|),

with `M₁ = momentMass (φ²)` and `K = transverseDecayConst (φ²)`.  Unlike the
pure decay bound this is finite at `x = 0`. -/
theorem abs_im_PhiKernel_le_two_regime {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) {w : ℂ} (hy1 : |w.im| ≤ 1) (hyR : |w.im| * R ≤ 1)
    (hx : w.re ≠ 0) :
    |(PhiExt (fun t => φ t ^ 2) w).im|
      ≤ |w.im| * min (2 * momentMass (fun t => φ t ^ 2))
          (transverseDecayConst (fun t => φ t ^ 2) / |w.re|) := by
  have hflat : |(PhiExt (fun t => φ t ^ 2) w).im|
      ≤ |w.im| * (2 * momentMass (fun t => φ t ^ 2)) := by
    have := abs_im_PhiKernel_le_transverse hφ hev hyR
    linarith [this]
  have hdecay : |(PhiExt (fun t => φ t ^ 2) w).im|
      ≤ |w.im| * (transverseDecayConst (fun t => φ t ^ 2) / |w.re|) := by
    have := abs_im_PhiKernel_le_transverse_decay hφ hev hy1 hyR hx
    calc |(PhiExt (fun t => φ t ^ 2) w).im|
        ≤ |w.im| * transverseDecayConst (fun t => φ t ^ 2) / |w.re| := this
      _ = |w.im| * (transverseDecayConst (fun t => φ t ^ 2) / |w.re|) := by ring
  rw [mul_min_of_nonneg _ _ (abs_nonneg w.im)]
  exact le_min hflat hdecay

/-! ### Summation against a local counting hypothesis -/

/-- **Interference envelope from local counts, with no minimum gap.**

Let `s` be a finite family of coordinate differences `w n` whose transverse
parts are at most `y ≤ 1`, and suppose that each unit window of the ordinate
difference contains at most `N` members:

    #{ n ∈ s : k ≤ |Re w n| < k+1 } ≤ N   for every `k : ℕ`.

Then the total mixed interference obeys

    ∑_{n ∈ s} (Im Φ_{φ²}(w n))² ≤ N y² (4 M₁² + 2 K²),

quadratic in the transverse offset and *independent of any separation between
the ordinates*.  Members lying in the central window `|Re w n| < 1` are
controlled by the flat bound, the rest by the `1/|x|` decay. -/
theorem mixedInterference_envelope_localCount {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hR : 0 ≤ R) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hyR : y * R ≤ 1) {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℂ)
    (him : ∀ n ∈ s, |(w n).im| ≤ y) {N : ℕ}
    (hcount : ∀ k : ℕ,
      (s.filter (fun n => (k : ℝ) ≤ |(w n).re| ∧ |(w n).re| < (k : ℝ) + 1)).card ≤ N) :
    ∑ n ∈ s, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ (N : ℝ) * y ^ 2 * (4 * momentMass (fun t => φ t ^ 2) ^ 2
          + 2 * transverseDecayConst (fun t => φ t ^ 2) ^ 2) := by
  classical
  set M₁ := momentMass (fun t => φ t ^ 2) with hM₁
  set K := transverseDecayConst (fun t => φ t ^ 2) with hK
  have hM₁0 : 0 ≤ M₁ := momentMass_nonneg _
  have hK0 : 0 ≤ K := transverseDecayConst_nonneg _
  set f : ι → ℝ := fun n => (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2 with hf
  -- the per-window bound
  set c : ℕ → ℝ := fun k => if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else y ^ 2 * K ^ 2 / (k : ℝ) ^ 2
    with hc
  have hc0 : ∀ k, 0 ≤ c k := by
    intro k
    by_cases hk : k = 0 <;> simp [hc, hk] <;> positivity
  -- each member of the `k`-th window obeys `f n ≤ c k`
  have hmem : ∀ n ∈ s, ∀ k : ℕ, (k : ℝ) ≤ |(w n).re| → |(w n).re| < (k : ℝ) + 1 → f n ≤ c k := by
    intro n hn k hk1 _
    have hyn : |(w n).im| ≤ y := him n hn
    have hyn1 : |(w n).im| ≤ 1 := le_trans hyn hy1
    have hynR : |(w n).im| * R ≤ 1 := by
      have : |(w n).im| * R ≤ y * R := mul_le_mul_of_nonneg_right hyn hR
      linarith
    by_cases hk : k = 0
    · -- flat regime
      subst hk
      have hflat := abs_im_PhiKernel_le_transverse hφ hev hynR
      have habs : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ y * (2 * M₁) := by
        have : 2 * |(w n).im| * M₁ ≤ 2 * y * M₁ := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hyn (by norm_num : (0:ℝ) ≤ 2)) hM₁0
          linarith
        calc |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ 2 * |(w n).im| * M₁ := hflat
          _ ≤ 2 * y * M₁ := this
          _ = y * (2 * M₁) := by ring
      have hsq : f n ≤ (y * (2 * M₁)) ^ 2 := by
        have h1 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ^ 2 = f n := sq_abs _
        nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w n)).im,
          mul_nonneg hy0 (by linarith : (0:ℝ) ≤ 2 * M₁)]
      have : (y * (2 * M₁)) ^ 2 = y ^ 2 * (2 * M₁) ^ 2 := by ring
      simp only [hc, if_pos rfl]
      linarith [hsq, this.le, this.ge]
    · -- decay regime
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk
        exact_mod_cast this
      have hrepos : 0 < |(w n).re| := lt_of_lt_of_le hkpos hk1
      have hx : (w n).re ≠ 0 := fun h0 => by simp [h0] at hrepos
      have hdecay := abs_im_PhiKernel_le_transverse_decay hφ hev hyn1 hynR hx
      have hstep : |(w n).im| * K / |(w n).re| ≤ y * K / (k : ℝ) := by
        calc |(w n).im| * K / |(w n).re| ≤ y * K / |(w n).re| := by
              gcongr
          _ ≤ y * K / (k : ℝ) := by
              refine div_le_div_of_nonneg_left ?_ hkpos hk1
              exact mul_nonneg hy0 hK0
      have habs : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ≤ y * K / (k : ℝ) := hdecay.trans hstep
      have hsq : f n ≤ (y * K / (k : ℝ)) ^ 2 := by
        have h1 : |(PhiExt (fun t => φ t ^ 2) (w n)).im| ^ 2 = f n := sq_abs _
        nlinarith [abs_nonneg (PhiExt (fun t => φ t ^ 2) (w n)).im,
          div_nonneg (mul_nonneg hy0 hK0) hkpos.le]
      have hval : (y * K / (k : ℝ)) ^ 2 = y ^ 2 * K ^ 2 / (k : ℝ) ^ 2 := by
        rw [div_pow]; ring_nf
      simp only [hc, if_neg hk]
      linarith [hsq, hval.le, hval.ge]
  -- group the family by the integer part of the ordinate difference
  set g : ι → ℕ := fun n => ⌊|(w n).re|⌋₊ with hg
  set Mx : ℕ := (s.sup g) + 1 with hMx
  have hmaps : ∀ n ∈ s, g n ∈ Finset.range Mx := by
    intro n hn
    have : g n ≤ s.sup g := Finset.le_sup hn
    simpa [hMx, Nat.lt_succ_iff] using this
  have hgroup : ∑ k ∈ Finset.range Mx, ∑ n ∈ s.filter (fun n => g n = k), f n = ∑ n ∈ s, f n :=
    Finset.sum_fiberwise_of_maps_to hmaps f
  -- bound each fibre by `N · c k`
  have hfibre : ∀ k ∈ Finset.range Mx,
      ∑ n ∈ s.filter (fun n => g n = k), f n ≤ (N : ℝ) * c k := by
    intro k _
    have hfilter : s.filter (fun n => g n = k)
        = s.filter (fun n => (k : ℝ) ≤ |(w n).re| ∧ |(w n).re| < (k : ℝ) + 1) := by
      refine Finset.filter_congr fun n _ => ?_
      constructor
      · intro h
        have := (Nat.floor_eq_iff (abs_nonneg ((w n).re))).1 h
        exact this
      · intro h
        exact (Nat.floor_eq_iff (abs_nonneg ((w n).re))).2 h
    have hb : ∀ n ∈ s.filter (fun n => g n = k), f n ≤ c k := by
      intro n hn
      rw [hfilter] at hn
      obtain ⟨hns, hcond⟩ := Finset.mem_filter.1 hn
      exact hmem n hns k hcond.1 hcond.2
    calc ∑ n ∈ s.filter (fun n => g n = k), f n
        ≤ ∑ _n ∈ s.filter (fun n => g n = k), c k := Finset.sum_le_sum hb
      _ = ((s.filter (fun n => g n = k)).card : ℝ) * c k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * c k := by
          have hcard : ((s.filter (fun n => g n = k)).card : ℝ) ≤ (N : ℝ) := by
            rw [hfilter]
            exact_mod_cast hcount k
          exact mul_le_mul_of_nonneg_right hcard (hc0 k)
  have hsum : ∑ n ∈ s, f n ≤ ∑ k ∈ Finset.range Mx, (N : ℝ) * c k := by
    rw [← hgroup]
    exact Finset.sum_le_sum hfibre
  -- and sum the windows
  have htail : ∑ k ∈ Finset.range Mx, c k ≤ y ^ 2 * (2 * M₁) ^ 2 + 2 * (y ^ 2 * K ^ 2) := by
    have hsplit : ∑ k ∈ Finset.range Mx, c k
        ≤ y ^ 2 * (2 * M₁) ^ 2 + ∑ k ∈ Finset.range Mx, y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) := by
      have hpt : ∀ k ∈ Finset.range Mx,
          c k ≤ (if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else 0)
            + y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) := by
        intro k _
        by_cases hk : k = 0
        · subst hk
          simp [hc]
        · have : c k = y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) := by
            simp [hc, hk]
            ring
          rw [this]
          simp [hk]
      calc ∑ k ∈ Finset.range Mx, c k
          ≤ ∑ k ∈ Finset.range Mx, ((if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else 0)
              + y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2)) := Finset.sum_le_sum hpt
        _ = (∑ k ∈ Finset.range Mx, if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else 0)
              + ∑ k ∈ Finset.range Mx, y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) := Finset.sum_add_distrib
        _ ≤ y ^ 2 * (2 * M₁) ^ 2
              + ∑ k ∈ Finset.range Mx, y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) := by
            have hind : (∑ k ∈ Finset.range Mx, if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else 0)
                ≤ y ^ 2 * (2 * M₁) ^ 2 := by
              have heq : (∑ k ∈ Finset.range Mx, if k = 0 then y ^ 2 * (2 * M₁) ^ 2 else 0)
                  = if (0 : ℕ) ∈ Finset.range Mx then y ^ 2 * (2 * M₁) ^ 2 else 0 := by
                simp [Finset.sum_ite_eq']
              rw [heq]
              split_ifs with hmem0
              · exact le_rfl
              · positivity
            linarith
    have hser : ∑ k ∈ Finset.range Mx, y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2) ≤ 2 * (y ^ 2 * K ^ 2) := by
      have hsummable : Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ)) ^ 2 :=
        Real.summable_one_div_nat_pow.2 (by norm_num)
      have hnn : ∀ k : ℕ, 0 ≤ (1 : ℝ) / ((k : ℝ)) ^ 2 := fun k => by positivity
      have hfin : ∑ k ∈ Finset.range Mx, (1 : ℝ) / ((k : ℝ)) ^ 2
          ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ)) ^ 2 :=
        hsummable.sum_le_tsum _ (fun k _ => hnn k)
      have hle2 := tsum_nat_inv_sq_le
      have hcoef : (0 : ℝ) ≤ y ^ 2 * K ^ 2 := by positivity
      calc ∑ k ∈ Finset.range Mx, y ^ 2 * K ^ 2 * (1 / (k : ℝ) ^ 2)
          = y ^ 2 * K ^ 2 * ∑ k ∈ Finset.range Mx, (1 : ℝ) / ((k : ℝ)) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ y ^ 2 * K ^ 2 * 2 := by
            exact mul_le_mul_of_nonneg_left (le_trans hfin hle2) hcoef
        _ = 2 * (y ^ 2 * K ^ 2) := by ring
    linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc ∑ n ∈ s, f n ≤ ∑ k ∈ Finset.range Mx, (N : ℝ) * c k := hsum
    _ = (N : ℝ) * ∑ k ∈ Finset.range Mx, c k := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (y ^ 2 * (2 * M₁) ^ 2 + 2 * (y ^ 2 * K ^ 2)) :=
        mul_le_mul_of_nonneg_left htail hNnn
    _ = (N : ℝ) * y ^ 2 * (4 * M₁ ^ 2 + 2 * K ^ 2) := by ring

/-! ### The `δ`-free localization ratio -/

/-- **Localization without a minimum-gap hypothesis.**

Under the source-window hypotheses of `interference_le_ratio_mul_gramDefect`,
but with the ordinate separation `δ` replaced by a *local count* `N` per unit
window, the total mixed interference is at most `η · ΔGram` with

    η = 16384 N (4 M₁² + 2 K²) / (81 L⁶),

again free of the transverse offset `α`. -/
theorem interference_le_ratio_mul_gramDefect_localCount {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) (hR : 0 ≤ R) {L : ℝ} (hL : 0 < L)
    (h2R : 2 * R ≤ L) {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ)
    {m : ℕ} (hm : 1 ≤ m)
    (htail : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2)
    (hα1 : |α| ≤ 1) (hαR : |α| * R ≤ 1) {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℂ)
    (him : ∀ n ∈ s, |(w n).im| ≤ |α|) {N : ℕ}
    (hcount : ∀ k : ℕ,
      (s.filter (fun n => (k : ℝ) ≤ |(w n).re| ∧ |(w n).re| < (k : ℝ) + 1)).card ≤ N) :
    ∑ n ∈ s, (PhiExt (fun t => φ t ^ 2) (w n)).im ^ 2
      ≤ 16384 * (N : ℝ) * (4 * momentMass (fun t => φ t ^ 2) ^ 2
            + 2 * transverseDecayConst (fun t => φ t ^ 2) ^ 2) / (81 * L ^ 6)
        * finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  set M₁ := momentMass (fun t => φ t ^ 2) with hM₁
  set K := transverseDecayConst (fun t => φ t ^ 2) with hK
  have henv := mixedInterference_envelope_localCount hφ hev hR (abs_nonneg α) hα1 hαR s w him
    hcount
  rw [sq_abs α] at henv
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hstep : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
    nlinarith [htail, hL2]
  have hgram : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by linarith
  have hcoef : (0 : ℝ) ≤ 16384 * (N : ℝ) * (4 * M₁ ^ 2 + 2 * K ^ 2) / (81 * L ^ 6) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : (0 : ℝ) ≤ 4 * M₁ ^ 2 + 2 * K ^ 2 := by positivity
    have h3 : (0 : ℝ) < 81 * L ^ 6 := by positivity
    positivity
  have hmul := mul_le_mul_of_nonneg_left hgram hcoef
  have hval : 16384 * (N : ℝ) * (4 * M₁ ^ 2 + 2 * K ^ 2) / (81 * L ^ 6)
        * (81 / 16384 * L ^ 6 * α ^ 2)
      = (N : ℝ) * α ^ 2 * (4 * M₁ ^ 2 + 2 * K ^ 2) := by
    field_simp
  rw [hval] at hmul
  linarith [henv, hmul]

end RiemannAnalytic
