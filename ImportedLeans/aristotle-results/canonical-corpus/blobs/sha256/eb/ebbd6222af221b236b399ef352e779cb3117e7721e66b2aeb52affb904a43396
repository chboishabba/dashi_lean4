/-
# Row A1a — the mixed-component patch: a computed, not budgeted, floor

This is the assembly the corrected A1a route asks for.  On a *mixed* Lorentz
component `α ≠ β` of the constrained first background variation

    V = W + Q + R,

the two error pieces are no longer paid by absolute values:

* `Q` (the averaging variation) vanishes identically — the block-averaging
  operator is Lorentz block diagonal, `AveragingLorentzDiagonal`;
* the constrained part of `R` (the elimination of the constrained coordinates)
  vanishes identically — the projection onto `ker Q` inherits Lorentz block
  diagonality, `LorentzBlockDiagonal`;
* only the *gauge* part of `R` survives, and it is computed in
  `GaugeProjectionVariation`, with the crucial `1/|k|²` suppression.

So on a mixed component the literal symbol is

    V_{α β; ρ}(x) = W_{α β; ρ}(x) + R^{gauge}_{α β; ρ}(x)

with `β = ρ`, `α ≠ ρ`,

    W = − sin(π x_α) cos(π x_ρ),
    R^{gauge} = f k_α (|k|² − 2k_ρ²)/|k|⁴,   k_μ = p̂_μ = 2 sin(π x_μ).

**The patch is then chosen to exploit the momentum suppression of the gauge
term**: push the two spectator directions towards the Brillouin corner, where
`|k|²` is maximal, and keep `x_ρ` small, where the Wilson cosine is maximal.
On the box

    x_α ∈ [1/4−δ, 1/4+δ],  x_ρ ∈ [0, δ],  x_2, x_3 ∈ [1/2−δ, 1/2]

the whole estimate follows from one elementary inequality, `2t ≤ sin(π t)` on
`[0,1/2]`, and gives the explicit floor

    |V| ≥ (1/2 − 2δ)·((1 − 2δ) − F/(4(1−2δ)²)),   F ≥ |f|.

At `δ = 1/16` and `F = 1` this is `≥ 1/5`, and the patch has volume
`2δ⁴ = 1/32768 > 0`, so the Gaussian floor `b_patch > 0` follows from the
positive-volume compiler.  Notably the criterion on the gauge amplitude is
`F < 4(1−2δ)³`, i.e. roughly `F < 4` — vastly weaker than the dimension-counted
fallback budget of `ConnectionBudget`.

The two vanishing statements are position-space facts about the averaging
kernel and the constrained projection; they transfer to the momentum symbol
because the Fourier transform acts on the site index only and leaves the Lorentz
index untouched.

**Honest status.**  What is *proved* here is the estimate for the literal
symbols defined in this project: the Wilson cubic vertex, and the longitudinal
gauge projector's first variation on the lattice momentum vector `p̂`.  The
identification of these with the corresponding objects of Bałaban's
construction — in particular the relative normalisation `f` of the background
perturbation — remains a source obligation and is carried explicitly as the
parameter `F`.  Row A1 is not closed by this file.
-/
import RequestProject.YangMills.GaugeProjectionVariation
import RequestProject.YangMills.AveragingLorentzDiagonal
import RequestProject.YangMills.LorentzBlockDiagonal
import RequestProject.YangMills.WilsonCubicVertex
import RequestProject.YangMills.FirstVariationDecomposition
import RequestProject.YangMills.PositivePatchEnclosure

namespace YangMills

open Real Finset MeasureTheory Set

/-! ## 1. Jordan's inequality in the project's normalisation -/

/-- Jordan's inequality (`two_mul_le_sinAtom`) read as a lower bound for the
cosine: `1 − 2t ≤ cos(π t)` on `[0,1/2]`. -/
theorem one_sub_two_mul_le_cos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    1 - 2 * t ≤ Real.cos (π * t) := by
  have h := two_mul_le_sinAtom (x := 1 / 2 - t) (by linarith) (by linarith)
  have hrw : sinAtom (1 / 2 - t) = Real.cos (π * t) := by
    rw [sinAtom]
    have : π * (1 / 2 - t) = π / 2 - π * t := by ring
    rw [this, Real.sin_pi_div_two_sub]
  rw [hrw] at h
  linarith

/-! ## 2. The literal mixed component of the constrained first variation -/

/-- The lattice momentum vector `k_μ = p̂_μ = 2 sin(π x_μ)`. -/
noncomputable def latticeMomentumVector (x : Fin 4 → ℝ) : Fin 4 → ℝ := fun mu => phat (x mu)

theorem sum_sq_latticeMomentumVector (x : Fin 4 → ℝ) :
    (∑ ga : Fin 4, (latticeMomentumVector x ga) ^ 2) = phatSq x := rfl

/-- The Wilson piece of the mixed component: with the background index `ρ` equal
to the second fluctuation index and `α ≠ ρ`, the Wilson cubic vertex is
`−sin(π x_α) cos(π x_ρ)`. -/
theorem wilsonCubicBgZero_mixed_eq {al rho : Fin 4} (hne : al ≠ rho) (x : Fin 4 → ℝ) :
    wilsonCubicBgZero x al rho rho = -sinAtom (x al) * Real.cos (π * x rho) := by
  have h1 : π * (-x al - 0) = -(π * x al) := by ring
  simp only [wilsonCubicBgZero, wilsonCubic, if_neg hne, if_neg (Ne.symm hne),
    h1, Real.sin_neg, sinAtom, if_true]
  ring

/-- **The literal mixed component of the constrained first variation.**  The
averaging piece `Q` and the constrained part of `R` vanish on a mixed Lorentz
component (`averagingKernel_mixed_zero`, `kerProjection_mixed_zero`), so `V` is
the Wilson cubic vertex plus the gauge-projection variation. -/
noncomputable def mixedConstrainedSymbol (f : ℝ) (x : Fin 4 → ℝ) (al rho : Fin 4) : ℝ :=
  wilsonCubicBgZero x al rho rho + gaugeVariationSymbol f (latticeMomentumVector x) rho al rho

/-- Triangle inequality form: the Wilson piece minus the computed gauge piece is
a lower bound for the mixed component. -/
theorem abs_mixedConstrainedSymbol_ge (f : ℝ) (x : Fin 4 → ℝ) (al rho : Fin 4) :
    |wilsonCubicBgZero x al rho rho| - |gaugeVariationSymbol f (latticeMomentumVector x) rho al rho|
      ≤ |mixedConstrainedSymbol f x al rho| := by
  have := abs_add_le (mixedConstrainedSymbol f x al rho)
    (-gaugeVariationSymbol f (latticeMomentumVector x) rho al rho)
  have hsimp : mixedConstrainedSymbol f x al rho
      + -gaugeVariationSymbol f (latticeMomentumVector x) rho al rho
      = wilsonCubicBgZero x al rho rho := by
    rw [mixedConstrainedSymbol]; ring
  rw [hsimp, abs_neg] at this
  linarith

/-! ## 2b. The exact assembly `V = W + Q + R` on a mixed component -/

/-- A vertex symbol has no mixed Lorentz components. -/
def MixedVanishing {color : Type*} (S : VertexSymbol color) : Prop :=
  ∀ al be rho : Fin 4, ∀ a b c : color, ∀ q : Fin 4 → ℝ,
    al ≠ be → S al be rho a b c q = 0

/-- **The exact assembly.**  If the averaging variation has no mixed components
(`averagingKernel_mixed_zero`), and the constraint/gauge variation splits into a
constrained part with no mixed components (`kerProjection_mixed_zero`) and the
computed gauge part, then on a mixed component `α ≠ ρ` with the background index
equal to the second fluctuation index the constrained first variation is exactly
`mixedConstrainedSymbol`: Wilson cubic vertex plus gauge-projection variation,
with nothing estimated away. -/
theorem constrainedFirstVariation_total_mixed_eq {color : Type*}
    (V : ConstrainedFirstVariation color) {Rconstr Rgauge : VertexSymbol color} {f : ℝ}
    (hQ : MixedVanishing V.Q)
    (hRsplit : ∀ al be rho : Fin 4, ∀ a b c : color, ∀ q : Fin 4 → ℝ,
      V.R al be rho a b c q = Rconstr al be rho a b c q + Rgauge al be rho a b c q)
    (hRc : MixedVanishing Rconstr)
    {al rho : Fin 4} {a b c : color} (hne : al ≠ rho) (x : Fin 4 → ℝ)
    (hW : V.W al rho rho a b c x = wilsonCubicBgZero x al rho rho)
    (hRg : Rgauge al rho rho a b c x
      = gaugeVariationSymbol f (latticeMomentumVector x) rho al rho) :
    V.total al rho rho a b c x = mixedConstrainedSymbol f x al rho := by
  rw [ConstrainedFirstVariation.total_apply, hW, hQ al rho rho a b c x hne,
    hRsplit, hRc al rho rho a b c x hne, hRg, mixedConstrainedSymbol]
  ring

/-! ## 3. The patch -/

/-- **The chosen patch.**  Fluctuation index `α = 0`, background index
`ρ = β = 1`.  The spectator directions `2, 3` are pushed to the Brillouin
corner, where the `1/|k|²` gauge suppression is strongest; `x_1` is kept small,
where the Wilson cosine is largest. -/
def mixedPatch (delta : ℝ) : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun mu => if mu = 0 then Icc (1 / 4 - delta) (1 / 4 + delta)
    else if mu = 1 then Icc (0 : ℝ) delta else Icc (1 / 2 - delta) (1 / 2)

theorem measurableSet_mixedPatch (delta : ℝ) : MeasurableSet (mixedPatch delta) := by
  refine MeasurableSet.univ_pi fun mu => ?_
  by_cases h0 : mu = 0
  · simp [h0, measurableSet_Icc]
  · by_cases h1 : mu = 1 <;> simp [h0, h1, measurableSet_Icc]

theorem mixedPatch_subset {delta : ℝ} (h1 : delta ≤ 1 / 4) :
    mixedPatch delta ⊆ momentumCell := by
  refine Set.pi_mono fun mu _ => ?_
  by_cases hz : mu = 0
  · simp only [hz]
    exact Icc_subset_Icc (by linarith) (by linarith)
  · by_cases ho : mu = 1
    · simp only [ho]
      exact Icc_subset_Icc le_rfl (by linarith)
    · simp only [if_neg hz, if_neg ho]
      exact Icc_subset_Icc (by linarith) le_rfl

/-- **The patch has positive volume `2δ⁴`.** -/
theorem mixedPatch_volume {delta : ℝ} (h0 : 0 ≤ delta) :
    volume (mixedPatch delta) = ENNReal.ofReal (2 * delta ^ 4) := by
  rw [mixedPatch, volume_pi_pi, Fin.prod_univ_four]
  rw [if_pos rfl, if_neg (by decide : ¬((1 : Fin 4) = 0)), if_pos rfl,
    if_neg (by decide : ¬((2 : Fin 4) = 0)), if_neg (by decide : ¬((2 : Fin 4) = 1)),
    if_neg (by decide : ¬((3 : Fin 4) = 0)), if_neg (by decide : ¬((3 : Fin 4) = 1))]
  simp only [Real.volume_Icc]
  rw [show (1 / 4 + delta - (1 / 4 - delta) : ℝ) = 2 * delta by ring,
    show (delta - 0 : ℝ) = delta by ring,
    show (1 / 2 - (1 / 2 - delta) : ℝ) = delta by ring]
  rw [← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 2 * delta),
    ← ENNReal.ofReal_mul (by nlinarith : (0:ℝ) ≤ 2 * delta * delta),
    ← ENNReal.ofReal_mul
      (by nlinarith [mul_nonneg (mul_nonneg h0 h0) h0] : (0:ℝ) ≤ 2 * delta * delta * delta)]
  congr 1
  ring

theorem mixedPatch_volume_real {delta : ℝ} (h0 : 0 ≤ delta) :
    (volume (mixedPatch delta)).toReal = 2 * delta ^ 4 := by
  rw [mixedPatch_volume h0, ENNReal.toReal_ofReal (by positivity)]

theorem mixedPatch_volume_ne_top {delta : ℝ} (h0 : 0 ≤ delta) :
    volume (mixedPatch delta) ≠ ⊤ := by
  rw [mixedPatch_volume h0]; exact ENNReal.ofReal_ne_top

/-! ## 4. The estimates on the patch -/

variable {delta : ℝ}

theorem mixedPatch_mem_zero {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch delta) :
    x 0 ∈ Icc (1 / 4 - delta) (1 / 4 + delta) := by
  simpa [mixedPatch] using hx 0 (mem_univ 0)

theorem mixedPatch_mem_one {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch delta) :
    x 1 ∈ Icc (0 : ℝ) delta := by
  simpa [mixedPatch] using hx 1 (mem_univ 1)

theorem mixedPatch_mem_spectator {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch delta) (mu : Fin 4)
    (h0 : mu ≠ 0) (h1 : mu ≠ 1) : x mu ∈ Icc (1 / 2 - delta) (1 / 2) := by
  simpa [mixedPatch, h0, h1] using hx mu (mem_univ mu)

/-- The Wilson sine factor on the patch. -/
theorem sinAtom_zero_ge {x : Fin 4 → ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hx : x ∈ mixedPatch delta) : 1 / 2 - 2 * delta ≤ sinAtom (x 0) := by
  obtain ⟨hl, hu⟩ := mixedPatch_mem_zero hx
  have := two_mul_le_sinAtom (x := x 0) (by linarith) (by linarith)
  linarith

/-- The Wilson cosine factor on the patch. -/
theorem cos_one_ge {x : Fin 4 → ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hx : x ∈ mixedPatch delta) : 1 - 2 * delta ≤ Real.cos (π * x 1) := by
  obtain ⟨hl, hu⟩ := mixedPatch_mem_one hx
  have := one_sub_two_mul_le_cos (t := x 1) hl (by linarith)
  linarith

/-- **The momentum suppression on the patch:** the two spectator directions
alone give `|k|² ≥ 8(1−2δ)²`. -/
theorem phatSq_ge_on_mixedPatch {x : Fin 4 → ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hx : x ∈ mixedPatch delta) : 8 * (1 - 2 * delta) ^ 2 ≤ phatSq x := by
  have h2 : 1 - 2 * delta ≤ sinAtom (x 2) := by
    obtain ⟨hl, hu⟩ := mixedPatch_mem_spectator hx 2 (by decide) (by decide)
    have := two_mul_le_sinAtom (x := x 2) (by linarith) (by linarith)
    linarith
  have h3 : 1 - 2 * delta ≤ sinAtom (x 3) := by
    obtain ⟨hl, hu⟩ := mixedPatch_mem_spectator hx 3 (by decide) (by decide)
    have := two_mul_le_sinAtom (x := x 3) (by linarith) (by linarith)
    linarith
  have hpos : (0 : ℝ) < 1 - 2 * delta := by linarith
  have e2 : 4 * (1 - 2 * delta) ^ 2 ≤ (phat (x 2)) ^ 2 := by
    rw [phat_sq_eq]; nlinarith
  have e3 : 4 * (1 - 2 * delta) ^ 2 ≤ (phat (x 3)) ^ 2 := by
    rw [phat_sq_eq]; nlinarith
  have hsum : phatSq x = (phat (x 0)) ^ 2 + (phat (x 1)) ^ 2 + (phat (x 2)) ^ 2
      + (phat (x 3)) ^ 2 := by
    rw [phatSq, Fin.sum_univ_four]
  rw [hsum]
  nlinarith [sq_nonneg (phat (x 0)), sq_nonneg (phat (x 1))]

/-! ## 5. The floor -/

/-- The floor produced by the patch: `(1/2 − 2δ)·((1 − 2δ) − F/(4(1−2δ)²))`. -/
noncomputable def mixedPatchFloor (delta F : ℝ) : ℝ :=
  (1 / 2 - 2 * delta) * ((1 - 2 * delta) - F / (4 * (1 - 2 * delta) ^ 2))

/-- **The computed mixed-component floor on the patch.**  No absolute-value
budget for `Q` or for the constrained part of `R`: they vanish.  The gauge part
is computed and paid by the `1/|k|²` suppression of the corner momentum. -/
theorem mixedPatch_floor {f F : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hF : |f| ≤ F)
    (hbr : 0 ≤ (1 - 2 * delta) - F / (4 * (1 - 2 * delta) ^ 2))
    {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch delta) :
    mixedPatchFloor delta F ≤ |mixedConstrainedSymbol f x 0 1| := by
  have hne : (0 : Fin 4) ≠ 1 := by decide
  have hpos : (0 : ℝ) < 1 - 2 * delta := by linarith
  set s : ℝ := sinAtom (x 0) with hs
  have hs0 : 1 / 2 - 2 * delta ≤ s := sinAtom_zero_ge hd0 hd1 hx
  have hspos : 0 < s := by linarith
  have hc : 1 - 2 * delta ≤ Real.cos (π * x 1) := cos_one_ge hd0 hd1 hx
  have hcpos : 0 < Real.cos (π * x 1) := by linarith
  have hk : 8 * (1 - 2 * delta) ^ 2 ≤ phatSq x := phatSq_ge_on_mixedPatch hd0 hd1 hx
  have hkpos : 0 < phatSq x := by nlinarith
  -- the Wilson piece
  have hW : |wilsonCubicBgZero x 0 1 1| = s * Real.cos (π * x 1) := by
    rw [wilsonCubicBgZero_mixed_eq hne x, abs_mul, abs_neg, abs_of_pos hspos,
      abs_of_pos hcpos]
  -- the gauge piece
  have hkvec : (∑ ga : Fin 4, (latticeMomentumVector x ga) ^ 2) = phatSq x := rfl
  have hR : |gaugeVariationSymbol f (latticeMomentumVector x) 1 0 1|
      ≤ |f| * (2 * s) / phatSq x := by
    have hb := abs_gaugeVariationSymbol_mixed_le f (latticeMomentumVector x) hne
      (by rw [hkvec]; exact hkpos)
    rw [hkvec] at hb
    have : |latticeMomentumVector x 0| = 2 * s := by
      rw [latticeMomentumVector, phat, abs_of_pos (by positivity)]
    rwa [this] at hb
  have hRle : |gaugeVariationSymbol f (latticeMomentumVector x) 1 0 1|
      ≤ F * s / (4 * (1 - 2 * delta) ^ 2) := by
    refine hR.trans ?_
    have hnum : |f| * (2 * s) ≤ F * (2 * s) := by
      have : (0 : ℝ) ≤ 2 * s := by linarith
      nlinarith
    have hden : 0 < 8 * (1 - 2 * delta) ^ 2 := by positivity
    have hF : 0 ≤ F := le_trans (abs_nonneg f) hF
    have h1 : |f| * (2 * s) / phatSq x ≤ F * (2 * s) / (8 * (1 - 2 * delta) ^ 2) := by
      gcongr ?_ / ?_
    have h2 : F * (2 * s) / (8 * (1 - 2 * delta) ^ 2) = F * s / (4 * (1 - 2 * delta) ^ 2) := by
      field_simp
      ring
    rw [← h2]; exact h1
  have hmain := abs_mixedConstrainedSymbol_ge f x 0 1
  rw [hW] at hmain
  have hbig : mixedPatchFloor delta F ≤ s * Real.cos (π * x 1)
      - F * s / (4 * (1 - 2 * delta) ^ 2) := by
    have hfac : s * Real.cos (π * x 1) - F * s / (4 * (1 - 2 * delta) ^ 2)
        = s * (Real.cos (π * x 1) - F / (4 * (1 - 2 * delta) ^ 2)) := by
      field_simp
    rw [hfac, mixedPatchFloor]
    have hb1 : (1 - 2 * delta) - F / (4 * (1 - 2 * delta) ^ 2)
        ≤ Real.cos (π * x 1) - F / (4 * (1 - 2 * delta) ^ 2) := by linarith
    have hs1 : 0 < 1 / 2 - 2 * delta := by linarith
    nlinarith
  linarith

/-- **The concrete instance.**  Half-width `δ = 1/16`, gauge amplitude
`|f| ≤ 1`: the mixed component of the constrained first variation is at least
`1/5` on the whole patch. -/
theorem mixedPatch_floor_concrete {f : ℝ} (hf : |f| ≤ 1) {x : Fin 4 → ℝ}
    (hx : x ∈ mixedPatch (1 / 16)) :
    (1 : ℝ) / 5 ≤ |mixedConstrainedSymbol f x 0 1| := by
  have h := mixedPatch_floor (delta := 1 / 16) (f := f) (F := 1) (by norm_num) le_rfl hf
    (by norm_num) hx
  have hval : mixedPatchFloor (1 / 16) 1 = 645 / 3136 := by
    rw [mixedPatchFloor]; norm_num
  rw [hval] at h
  linarith

/-- **The floor for the constrained first variation itself.**  With the three
structural inputs — no mixed averaging component, no mixed constrained
component, and the computed gauge component — the constrained first variation
`V = W + Q + R` is at least `1/5` in modulus on the whole box, for any gauge
amplitude `|f| ≤ 1`. -/
theorem constrainedFirstVariation_mixedPatch_floor {color : Type*}
    (V : ConstrainedFirstVariation color) {Rconstr Rgauge : VertexSymbol color} {f : ℝ}
    (hQ : MixedVanishing V.Q)
    (hRsplit : ∀ al be rho : Fin 4, ∀ a b c : color, ∀ q : Fin 4 → ℝ,
      V.R al be rho a b c q = Rconstr al be rho a b c q + Rgauge al be rho a b c q)
    (hRc : MixedVanishing Rconstr) (hf : |f| ≤ 1) {a b c : color}
    (hW : ∀ x : Fin 4 → ℝ, V.W 0 1 1 a b c x = wilsonCubicBgZero x 0 1 1)
    (hRg : ∀ x : Fin 4 → ℝ, Rgauge 0 1 1 a b c x
      = gaugeVariationSymbol f (latticeMomentumVector x) 1 0 1)
    {x : Fin 4 → ℝ} (hx : x ∈ mixedPatch (1 / 16)) :
    (1 : ℝ) / 5 ≤ |V.total 0 1 1 a b c x| := by
  rw [constrainedFirstVariation_total_mixed_eq V hQ hRsplit hRc (by decide) x (hW x) (hRg x)]
  exact mixedPatch_floor_concrete hf hx

/-- **The criterion is `F < 4(1−2δ)³`.**  Whenever the gauge amplitude obeys it,
the bracket is positive and the patch floor is strictly positive. -/
theorem mixedPatchFloor_pos {F : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hF : F < 4 * (1 - 2 * delta) ^ 3) : 0 < mixedPatchFloor delta F := by
  have hpos : (0 : ℝ) < 1 - 2 * delta := by linarith
  have hbr : 0 < (1 - 2 * delta) - F / (4 * (1 - 2 * delta) ^ 2) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith
  have : (0 : ℝ) < 1 / 2 - 2 * delta := by linarith
  exact mul_pos this hbr

/-! ## 6. The Gaussian floor from the patch -/

/-- **The Gaussian floor produced by the mixed-component patch.**  An integrand
nonnegative on the cell and at least `c` on the patch has cell integral at least
`2δ⁴·c`. -/
theorem cellIntegral_ge_mixedPatch {g : (Fin 4 → ℝ) → ℝ} {c : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hg : IntegrableOn g momentumCell)
    (hpatch : ∀ x ∈ mixedPatch delta, c ≤ g x)
    (hrest : ∀ x ∈ momentumCell \ mixedPatch delta, 0 ≤ g x) :
    2 * delta ^ 4 * c ≤ ∫ x in momentumCell, g x := by
  have h := setIntegral_ge_patch (measurableSet_mixedPatch delta)
    (mixedPatch_subset (by linarith)) (mixedPatch_volume_ne_top hd0.le) hg
    measurableSet_momentumCell hpatch hrest
  rwa [Measure.real, mixedPatch_volume_real hd0.le] at h

/-- **A strictly positive Gaussian coefficient.**  Positive floor on a
positive-volume patch, sign on the complement. -/
theorem cellIntegral_pos_of_mixedPatch {g : (Fin 4 → ℝ) → ℝ} {c : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16) (hc : 0 < c)
    (hg : IntegrableOn g momentumCell)
    (hpatch : ∀ x ∈ mixedPatch delta, c ≤ g x)
    (hrest : ∀ x ∈ momentumCell \ mixedPatch delta, 0 ≤ g x) :
    0 < ∫ x in momentumCell, g x := by
  have h := cellIntegral_ge_mixedPatch hd0 hd1 hg hpatch hrest
  nlinarith [pow_pos hd0 4]

end YangMills
