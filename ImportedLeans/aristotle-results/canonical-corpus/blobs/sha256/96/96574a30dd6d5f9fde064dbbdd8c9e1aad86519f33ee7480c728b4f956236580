/-
# The off-ordinate zero tail: an explicit envelope from the companion's own machinery

`LiteralWeilSameOrdinateEvenCone.lean` split the literal Weil zero sum along the
ordinate fibre of the target,

    Q_cluster + Q_offOrd + Q_prime + Q_Γ + Q_pole = 0,

and produced a positive linear functional `ℓ` on the parity quotient with
`ℓ(Q_pole) = 0` and `ℓ(Q_cluster) > 0`.  The next channel to control is
`Q_offOrd`, the zeros whose ordinate differs from the target's.

This module produces the bound

    ‖Q_offOrd‖ ≤ ε_zero(g, Λ, t, r)

with a completely explicit `ε_zero`, assembled out of machinery that is already
machine-checked in the companion `Zeta23` library — no new zeta argument:

* `Zeta23.norm_paperFT_le` and `Zeta23.norm_paperFT_mul_sq_le` (the two halves of
  the paper's `[eq:hfbound]`) combine into a *strip envelope*: for a `C²` test
  function supported in `[-Λ, Λ]` and any point `z` of the strip `|Im z| ≤ 1/2`,

      ‖h_k(z)‖ · (1 + |z|²)  ≤  e^{Λ/2} (‖k‖₁ + ‖k''‖₁)  =:  stripConst k Λ.

* `Zeta23.WeilEF.zero_sum_inv_sq` (the unit-window/dyadic summation of the
  Riemann–von Mangoldt local zero count) makes

      W(t) = ∑_{Im ρ ≠ t} m_ρ / (1 + |γ_ρ|²)

  a finite number.

Multiplying the two gives, for each of the four samples, a genuine finite
envelope for the off-ordinate fibre, and hence

    |ℓ(Q_offOrd)| ≤ ε_zero := 2 (C_r + C_{-r}) · W(t).

The capstone `clusterConeBoundedByResidualChannels` then records exactly where the
programme now stands: the strictly positive cluster value is bounded by the sum of
the off-ordinate envelope and the prime and gamma cone values,

    0 < ℓ(Q_cluster) ≤ ε_zero + |ℓ(Q_prime)| + |ℓ(Q_Γ)|.

**What is *not* claimed.**  Nothing here shows `ε_zero < ℓ(Q_cluster)`; the
envelope `W(t)` is the *whole* zero-side weight sum minus the fibre, and it is not
small.  The bound is an honest, unconditional envelope, not a smallness statement.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOffOrdinateTail

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

/-! ## A support radius for a compactly supported taper -/

/-- Every compactly supported function has a nonnegative support radius `Λ`. -/
theorem exists_support_radius {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ u, g u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨rad, hrad⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max rad 0, le_max_right _ _, fun u hu => ?_⟩
  have hmem : u ∈ Metric.closedBall (0 : ℝ) rad :=
    hrad (subset_tsupport _ (Function.mem_support.mpr hu))
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  exact hmem.trans (le_max_left _ _)

/-- The sample test function inherits the support radius of its profile. -/
theorem sampleTest_support_radius {g : ℝ → ℝ} {Λ : ℝ} (h : ∀ u, g u ≠ 0 → |u| ≤ Λ) (t s : ℝ) :
    ∀ u, sampleTest g t s u ≠ 0 → |u| ≤ Λ := by
  intro u hu
  refine h u fun hg => hu ?_
  simp [sampleTest, hg]

/-! ## The strip envelope of a test function -/

/-- **The strip envelope constant** `e^{Λ/2} (‖k‖₁ + ‖k''‖₁)`.  Both integrals are
literal `L¹` norms of the test function and of its second derivative; the
exponential is the companion's `[eq:hfbound]` factor at the edge of the critical
strip. -/
def stripConst (k : ℝ → ℂ) (Λ : ℝ) : ℝ :=
  Real.exp (Λ / 2) * ((∫ u : ℝ, ‖k u‖) + ∫ u : ℝ, ‖deriv (deriv k) u‖)

theorem stripConst_nonneg (k : ℝ → ℂ) (Λ : ℝ) : 0 ≤ stripConst k Λ := by
  have h1 : (0 : ℝ) ≤ ∫ u : ℝ, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ u : ℝ, ‖deriv (deriv k) u‖ := integral_nonneg fun _ => norm_nonneg _
  unfold stripConst
  positivity

/-- **The strip envelope.**  Both halves of the companion's `[eq:hfbound]` — the
crude `L¹` bound and the second-derivative decay bound — are valid at once, so
their sum controls `‖h_k(z)‖ (1 + |z|²)` uniformly on the strip `|Im z| ≤ 1/2`.
This is exactly the shape needed to sum against the zero-count weight. -/
theorem norm_paperFT_mul_le_stripConst {k : ℝ → ℂ} {Λ : ℝ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT k z‖ * (1 + Complex.normSq z) ≤ stripConst k Λ := by
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hexp : Real.exp (|z.im| * Λ) ≤ Real.exp (Λ / 2) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h0 : (0 : ℝ) ≤ ∫ u : ℝ, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ u : ℝ, ‖deriv (deriv k) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hA : ‖paperFT k z‖ ≤ Real.exp (Λ / 2) * ∫ u : ℝ, ‖k u‖ :=
    (Zeta23.norm_paperFT_le hki hsupp z).trans (by nlinarith)
  have hB : ‖paperFT k z‖ * ‖z‖ ^ 2 ≤ Real.exp (Λ / 2) * ∫ u : ℝ, ‖deriv (deriv k) u‖ :=
    (Zeta23.norm_paperFT_mul_sq_le hk hsupp z).trans (by nlinarith)
  have hns : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [hns, stripConst]
  nlinarith

/-- The strip envelope in divided form. -/
theorem norm_paperFT_le_stripConst_div {k : ℝ → ℂ} {Λ : ℝ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT k z‖ ≤ stripConst k Λ / (1 + Complex.normSq z) := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq z := by
    have := Complex.normSq_nonneg z; linarith
  rw [le_div_iff₀ hpos]
  exact norm_paperFT_mul_le_stripConst hk hkc hsupp hΛ hz

/-! ## The zero-count weight of the companion -/

/-- The companion's zero-side weight `m_ρ / (1 + |γ_ρ|²)`. -/
def zeroWeight (ρ : Zeros) : ℝ :=
  ((Zeta23.zetaZeroConfig).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))

theorem zeroWeight_nonneg (ρ : Zeros) : 0 ≤ zeroWeight ρ := by
  have := Complex.normSq_nonneg (gammaOf (ρ : ℂ))
  unfold zeroWeight
  positivity

/-- **The zero-side weight sum converges** — this is `Zeta23.WeilEF.zero_sum_inv_sq`,
the unit-window summation of the Riemann–von Mangoldt local zero count.  Nothing is
re-proved here; the companion result is used literally. -/
theorem summable_zeroWeight : Summable zeroWeight :=
  Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam

/-- **The off-ordinate weight** `W(t) = ∑_{Im ρ ≠ t} m_ρ / (1 + |γ_ρ|²)`. -/
def offOrdWeight (t : ℝ) : ℝ := ∑' ρ : ((SameOrd t)ᶜ : Set Zeros), zeroWeight (ρ : Zeros)

theorem summable_offOrdWeight (t : ℝ) :
    Summable fun ρ : ((SameOrd t)ᶜ : Set Zeros) => zeroWeight (ρ : Zeros) :=
  summable_zeroWeight.subtype _

theorem offOrdWeight_nonneg (t : ℝ) : 0 ≤ offOrdWeight t :=
  tsum_nonneg fun _ => zeroWeight_nonneg _

/-! ## The envelope for a single zero and for the whole off-ordinate fibre -/

/-- Every zero of the configuration lies in the closed critical strip, hence its
`γ_ρ` lies in `|Im| ≤ 1/2`, where the strip envelope applies. -/
theorem abs_im_gammaOf_le (ρ : Zeros) : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
  Zeta23.WeilEF.abs_gammaOf_im_le ((Zeta23.zetaZeroConfig).strip _ ρ.2)

/-- **The envelope for one zero.** -/
theorem norm_zeroTerm_le {k : ℝ → ℂ} {Λ : ℝ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (ρ : Zeros) :
    ‖zeroTerm k ρ‖ ≤ stripConst k Λ * zeroWeight ρ := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith
  have hm : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := Nat.cast_nonneg _
  have hFT := norm_paperFT_le_stripConst_div hk hkc hsupp hΛ (abs_im_gammaOf_le ρ)
  calc ‖zeroTerm k ρ‖
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * ‖paperFT k (gammaOf (ρ : ℂ))‖ := by
        rw [zeroTerm, norm_mul, Complex.norm_natCast]
    _ ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * (stripConst k Λ / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left hFT hm
    _ = stripConst k Λ * zeroWeight ρ := by unfold zeroWeight; field_simp

/-- The off-ordinate family is absolutely summable, with the explicit envelope. -/
theorem summable_norm_offOrd {k : ℝ → ℂ} {Λ : ℝ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t : ℝ) :
    Summable fun ρ : ((SameOrd t)ᶜ : Set Zeros) => ‖zeroTerm k (ρ : Zeros)‖ := by
  refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _)
    (fun ρ => norm_zeroTerm_le hk hkc hsupp hΛ (ρ : Zeros))
    ((summable_offOrdWeight t).mul_left (stripConst k Λ))

/-- **`offOrdinateTailEnvelope`.**  The off-ordinate contribution to any single
sample is bounded by the strip envelope of the test function times the companion's
off-ordinate zero weight.  Both factors are finite and explicit. -/
theorem offOrdinateTailEnvelope {k : ℝ → ℂ} {Λ : ℝ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t : ℝ) :
    ‖offOrdTerm k t‖ ≤ stripConst k Λ * offOrdWeight t := by
  have hnorm := summable_norm_offOrd hk hkc hsupp hΛ t
  calc ‖offOrdTerm k t‖
      ≤ ∑' ρ : ((SameOrd t)ᶜ : Set Zeros), ‖zeroTerm k (ρ : Zeros)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' ρ : ((SameOrd t)ᶜ : Set Zeros), stripConst k Λ * zeroWeight (ρ : Zeros) :=
        hnorm.tsum_le_tsum (fun ρ => norm_zeroTerm_le hk hkc hsupp hΛ _)
          ((summable_offOrdWeight t).mul_left _)
    _ = stripConst k Λ * offOrdWeight t := (summable_offOrdWeight t).tsum_mul_left _

/-! ## From the envelope to the four-sample vector and the even cone -/

theorem abs_reim_le (z : ℂ) : |reim z| ≤ 2 * ‖z‖ := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  have := abs_add_le z.re z.im
  unfold reim
  linarith

/-- **Every coordinate of `Q_offOrd` obeys the envelope.** -/
theorem abs_offOrdVec_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) (i : Fin 4) :
    |offOrdVec (sampleFam g t r) t i| ≤ 2 * stripConst (sampleFam g t r i) Λ * offOrdWeight t := by
  have hsi : ∀ u, sampleFam g t r i u ≠ 0 → |u| ≤ Λ := by
    fin_cases i <;> exact sampleTest_support_radius hsupp _ _
  have hki : ContDiff ℝ 2 (sampleFam g t r i) := sampleFam_contDiff hgs t r i
  have hkci : HasCompactSupport (sampleFam g t r i) := sampleFam_hasCompactSupport hgc t r i
  have h1 : |offOrdVec (sampleFam g t r) t i| ≤ 2 * ‖offOrdTerm (sampleFam g t r i) t‖ :=
    abs_reim_le _
  have h2 := offOrdinateTailEnvelope hki hkci hsi hΛ t
  nlinarith [stripConst_nonneg (sampleFam g t r i) Λ, offOrdWeight_nonneg t,
    norm_nonneg (offOrdTerm (sampleFam g t r i) t)]

/-- **`epsZero`** — the explicit off-ordinate envelope for the even cone functional:
twice the sum of the two base-radius strip constants, times the companion's
off-ordinate zero weight. -/
def epsZero (g : ℝ → ℝ) (Λ t r : ℝ) : ℝ :=
  2 * (stripConst (sampleTest g t r) Λ + stripConst (sampleTest g t (-r)) Λ) * offOrdWeight t

theorem epsZero_nonneg (g : ℝ → ℝ) (Λ t r : ℝ) : 0 ≤ epsZero g Λ t r := by
  have h1 := stripConst_nonneg (sampleTest g t r) Λ
  have h2 := stripConst_nonneg (sampleTest g t (-r)) Λ
  have h3 := offOrdWeight_nonneg t
  unfold epsZero
  positivity

/-- **`offOrdinateConeEnvelope`.**  `|ℓ(Q_offOrd)| ≤ ε_zero(g, Λ, t, r)`, the bound
requested for step 3, assembled entirely from already machine-checked companion
machinery: `[eq:hfbound]` for the taper side, `zero_sum_inv_sq` for the zero side. -/
theorem offOrdinateConeEnvelope {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ epsZero g Λ t r := by
  have hval : evenConeFunctional (offOrdVec (sampleFam g t r) t)
      = reim (offOrdTerm (sampleTest g t r) t) + reim (offOrdTerm (sampleTest g t (-r)) t) := rfl
  have hs1 : ∀ u, sampleTest g t r u ≠ 0 → |u| ≤ Λ := sampleTest_support_radius hsupp _ _
  have hs2 : ∀ u, sampleTest g t (-r) u ≠ 0 → |u| ≤ Λ := sampleTest_support_radius hsupp _ _
  have hb1 : |reim (offOrdTerm (sampleTest g t r) t)|
      ≤ 2 * stripConst (sampleTest g t r) Λ * offOrdWeight t := by
    have h1 := abs_reim_le (offOrdTerm (sampleTest g t r) t)
    have h2 := offOrdinateTailEnvelope (sampleTest_contDiff hgs t r)
      (sampleTest_hasCompactSupport hgc t r) hs1 hΛ t
    nlinarith [norm_nonneg (offOrdTerm (sampleTest g t r) t)]
  have hb2 : |reim (offOrdTerm (sampleTest g t (-r)) t)|
      ≤ 2 * stripConst (sampleTest g t (-r)) Λ * offOrdWeight t := by
    have h1 := abs_reim_le (offOrdTerm (sampleTest g t (-r)) t)
    have h2 := offOrdinateTailEnvelope (sampleTest_contDiff hgs t (-r))
      (sampleTest_hasCompactSupport hgc t (-r)) hs2 hΛ t
    nlinarith [norm_nonneg (offOrdTerm (sampleTest g t (-r)) t)]
  rw [hval]
  refine (abs_add_le _ _).trans ?_
  unfold epsZero
  linarith

/-! ## Where the programme now stands -/

/-- **`clusterConeBoundedByResidualChannels`.**  For an actual nontrivial zero of
`riemannZeta` at a nonzero ordinate `t`, the strictly positive same-ordinate
cluster value is bounded by the off-ordinate envelope plus the prime and gamma cone
values:

    0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + |ℓ(Q_prime)| + |ℓ(Q_Γ)|.

Every ingredient on the right is explicit; the remaining obligations are exactly to
make the three of them jointly smaller than the left-hand side.  Nothing here
asserts that they are. -/
theorem clusterConeBoundedByResidualChannels {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ) ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ 0 < evenConeFunctional (clusterVec (sampleFam g t r) t)
      ∧ |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ epsZero g Λ t r
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ epsZero g Λ t r + |evenConeFunctional (primeVec (sampleFam g t r))|
            + |evenConeFunctional (gammaVec (sampleFam g t r))| := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, -, -, hpole, hA, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  obtain ⟨Λ, hΛ, hsupp⟩ := exists_support_radius hgc
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hpos : 0 < evenConeFunctional (clusterVec (sampleFam g t r) t) :=
    sameOrdinateClusterConePositive hgs hgc heven hA ⟨ρstar, him⟩
  have hoff := offOrdinateConeEnvelope hgs hgc hsupp hΛ t r
  -- the balance, read by the even cone functional
  have hlin : evenConeFunctional (clusterVec (sampleFam g t r) t)
      + evenConeFunctional (offOrdVec (sampleFam g t r) t)
      + evenConeFunctional (primeVec (sampleFam g t r))
      + evenConeFunctional (gammaVec (sampleFam g t r))
      + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  have hpolezero : evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    have hmem := poleVec_mem_poleSpace hgs.continuous hgc heven t r
    have := evenConeFunctional_poleSpace_le_ker (g := g) (t := t) (r := r) hpole hmem
    simpa using this
  rw [hpolezero, add_zero] at hlin
  refine ⟨g, r, Λ, hgs, hgc, heven, hrpos, hΛ, hsupp, hpole, hA, hpos, hoff, ?_⟩
  have h1 := abs_le.mp hoff
  have h4 := neg_abs_le (evenConeFunctional (primeVec (sampleFam g t r)))
  have h6 := neg_abs_le (evenConeFunctional (gammaVec (sampleFam g t r)))
  linarith [h1.1, h1.2]

end LiteralWeilOffOrdinateTail
end Zeta23Bridge
