import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Synthesis.RiemannG21WeightedHyperbolicCarrier

/-!
# G21 positive-plateau continuum moment compiler

A nonnegative taper with a nontrivial positive plateau turns the pointwise
strict hyperbolic TP2 carriers into strict continuum moment cross-products.

For the ODD sector this file now uses the literal historical moments

  N1(y) = ∫ u phi(u) sinh(yu) du,
  N3(y) = ∫ u^3 phi(u) sinh(yu) du,

so the low response is `u*phi(u)*sinh(yu)` and the score is `u^2`.
The EVEN/cosh lane keeps its M0/M2 carrier.

The weight is clipped to `[0,R]`; inside a plateau `(l,r)` choose `l<m<r`.
The rectangle `(l,m) × (m,r)` has positive product Lebesgue measure and every
point has `0<u<v`, giving strict carrier positivity.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

classical

/-- Zero extension of a taper restricted to the positive support interval. -/
def g21ClippedWeight (R : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) R then w x else 0

private theorem clippedWeight_nonneg
    {w : ℝ → ℝ} {R x : ℝ}
    (hw : ∀ t ∈ Icc (0 : ℝ) R, 0 <= w t) :
    0 <= g21ClippedWeight R w x := by
  by_cases hx : x ∈ Icc (0 : ℝ) R
  · simpa [g21ClippedWeight, hx] using hw x hx
  · simp [g21ClippedWeight, hx]

private theorem plateauRectangle_posMeasure
    {l m r : ℝ} (hlm : l < m) (hmr : m < r) :
    0 < (volume.prod volume) (Ioo l m ×ˢ Ioo m r) := by
  simp [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos, hlm, hmr]

/-- Literal positive-half odd N1 response weight. -/
def g21OddMomentWeight (R : ℝ) (w : ℝ → ℝ) (y x : ℝ) : ℝ :=
  x * g21ClippedWeight R w x * Real.sinh (y*x)

/-- Strict literal N1/N3 odd moment cross-product. -/
theorem oddMomentCrossProduct_pos_of_positivePlateau
    {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0 : ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hA : Integrable (g21OddMomentWeight R w a) volume)
    (hP : Integrable (g21OddMomentWeight R w p) volume)
    (hqA : Integrable (fun x => x^2 * g21OddMomentWeight R w a x) volume)
    (hqP : Integrable (fun x => x^2 * g21OddMomentWeight R w p x) volume) :
    0 < moment0 (g21OddMomentWeight R w a) volume
          * momentQ (fun x => x^2) (g21OddMomentWeight R w p) volume
        - momentQ (fun x => x^2) (g21OddMomentWeight R w a) volume
          * moment0 (g21OddMomentWeight R w p) volume := by
  let wc : ℝ → ℝ := g21ClippedWeight R w
  let A : ℝ → ℝ := fun x => x * wc x * Real.sinh (a*x)
  let P : ℝ → ℝ := fun x => x * wc x * Real.sinh (p*x)
  let q : ℝ → ℝ := fun x => x^2
  let s : Set (ℝ × ℝ) := Ioo l m ×ˢ Ioo m r
  have hFnonneg : ∀ z : ℝ × ℝ, 0 <= symmetrizedMomentIntegrand A P q z := by
    intro z
    rw [← oddWeightedSymmCarrier_eq_generic wc a p z.1 z.2]
    by_cases hu : z.1 ∈ Icc (0 : ℝ) R
    · by_cases hv : z.2 ∈ Icc (0 : ℝ) R
      · exact oddWeightedSymmCarrier_nonneg ha hap hu.1 hv.1
          (clippedWeight_nonneg hwNonneg) (clippedWeight_nonneg hwNonneg)
      · simp [oddWeightedSymmCarrier, wc, g21ClippedWeight, hv]
    · simp [oddWeightedSymmCarrier, wc, g21ClippedWeight, hu]
  have hs : 0 < (volume.prod volume) s := by
    dsimp [s]
    exact plateauRectangle_posMeasure hlm hmr
  have hFpos : ∀ z ∈ s, 0 < symmetrizedMomentIntegrand A P q z := by
    intro z hz
    rcases hz with ⟨hu, hv⟩
    have huv : z.1 < z.2 := hu.2.trans hv.1
    have huR : z.1 < R := hu.2.trans (hmr.trans hrR)
    have hvR : z.2 < R := hv.2.trans hrR
    have huI : z.1 ∈ Icc (0 : ℝ) R := ⟨(hl.trans hu.1).le, huR.le⟩
    have hvI : z.2 ∈ Icc (0 : ℝ) R := ⟨(hl.trans (hlm.trans hv.1)).le, hvR.le⟩
    have hwu0 : 0 < w z.1 := hwPos z.1 ⟨hu.1, hu.2.trans hmr⟩
    have hwv0 : 0 < w z.2 := hwPos z.2 ⟨hlm.trans hv.1, hv.2⟩
    have hwu : 0 < wc z.1 := by simpa [wc, g21ClippedWeight, huI] using hwu0
    have hwv : 0 < wc z.2 := by simpa [wc, g21ClippedWeight, hvI] using hwv0
    rw [← oddWeightedSymmCarrier_eq_generic wc a p z.1 z.2]
    exact oddWeightedSymmCarrier_pos ha hap (hl.trans hu.1) huv hwu hwv
  change 0 < moment0 A volume * momentQ q P volume - momentQ q A volume * moment0 P volume
  exact strictMomentCrossProduct_of_symmetrizedCarrier hA hP hqA hqP hFnonneg hs hFpos

/-- Even/cosh M0/M2 companion. -/
theorem evenMomentCrossProduct_pos_of_positivePlateau
    {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0 : ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hA : Integrable (fun x => g21ClippedWeight R w x * Real.cosh (a*x)) volume)
    (hP : Integrable (fun x => g21ClippedWeight R w x * Real.cosh (p*x)) volume)
    (hqA : Integrable (fun x => x^2 * (g21ClippedWeight R w x * Real.cosh (a*x))) volume)
    (hqP : Integrable (fun x => x^2 * (g21ClippedWeight R w x * Real.cosh (p*x))) volume) :
    0 < moment0 (fun x => g21ClippedWeight R w x * Real.cosh (a*x)) volume
          * momentQ (fun x => x^2) (fun x => g21ClippedWeight R w x * Real.cosh (p*x)) volume
        - momentQ (fun x => x^2) (fun x => g21ClippedWeight R w x * Real.cosh (a*x)) volume
          * moment0 (fun x => g21ClippedWeight R w x * Real.cosh (p*x)) volume := by
  let wc : ℝ → ℝ := g21ClippedWeight R w
  let A : ℝ → ℝ := fun x => wc x * Real.cosh (a*x)
  let P : ℝ → ℝ := fun x => wc x * Real.cosh (p*x)
  let q : ℝ → ℝ := fun x => x^2
  let s : Set (ℝ × ℝ) := Ioo l m ×ˢ Ioo m r
  have hFnonneg : ∀ z : ℝ × ℝ, 0 <= symmetrizedMomentIntegrand A P q z := by
    intro z
    rw [← evenWeightedSymmCarrier_eq_generic wc a p z.1 z.2]
    by_cases hu : z.1 ∈ Icc (0 : ℝ) R
    · by_cases hv : z.2 ∈ Icc (0 : ℝ) R
      · exact evenWeightedSymmCarrier_nonneg ha hap hu.1 hv.1
          (clippedWeight_nonneg hwNonneg) (clippedWeight_nonneg hwNonneg)
      · simp [evenWeightedSymmCarrier, wc, g21ClippedWeight, hv]
    · simp [evenWeightedSymmCarrier, wc, g21ClippedWeight, hu]
  have hs : 0 < (volume.prod volume) s := by
    dsimp [s]
    exact plateauRectangle_posMeasure hlm hmr
  have hFpos : ∀ z ∈ s, 0 < symmetrizedMomentIntegrand A P q z := by
    intro z hz
    rcases hz with ⟨hu, hv⟩
    have huv : z.1 < z.2 := hu.2.trans hv.1
    have huR : z.1 < R := hu.2.trans (hmr.trans hrR)
    have hvR : z.2 < R := hv.2.trans hrR
    have huI : z.1 ∈ Icc (0 : ℝ) R := ⟨(hl.trans hu.1).le, huR.le⟩
    have hvI : z.2 ∈ Icc (0 : ℝ) R := ⟨(hl.trans (hlm.trans hv.1)).le, hvR.le⟩
    have hwu0 : 0 < w z.1 := hwPos z.1 ⟨hu.1, hu.2.trans hmr⟩
    have hwv0 : 0 < w z.2 := hwPos z.2 ⟨hlm.trans hv.1, hv.2⟩
    have hwu : 0 < wc z.1 := by simpa [wc, g21ClippedWeight, huI] using hwu0
    have hwv : 0 < wc z.2 := by simpa [wc, g21ClippedWeight, hvI] using hwv0
    rw [← evenWeightedSymmCarrier_eq_generic wc a p z.1 z.2]
    exact evenWeightedSymmCarrier_pos ha hap (hl.trans hu.1) huv hwu hwv
  change 0 < moment0 A volume * momentQ q P volume - momentQ q A volume * moment0 P volume
  exact strictMomentCrossProduct_of_symmetrizedCarrier hA hP hqA hqP hFnonneg hs hFpos

end Synthesis
