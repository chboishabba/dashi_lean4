/-
# Row A1a — the positive-volume patch compiler

The corrected A1a route does **not** ask for global control of the one-loop
integrand over the Brillouin zone, and it does not ask for a value at a single
momentum either (`SingleModeWeight` shows a single mode carries vanishing
normalised weight; `WilsonCubicVertex` shows the corner momentum kills the
diagonal first variation anyway).  What it asks for is:

* a *positive-volume* momentum patch `P` on which the integrand has a strict
  lower bound `c > 0`, and
* merely a **sign** on the complement.

This file proves the resulting compiler for the literal Lebesgue integral over
the project's momentum cell `[0,1/2]^4 ⊆ (Fin 4 → ℝ)`:

* `setIntegral_ge_patch` : patch bound plus complement sign gives
  `∫_Ω f ≥ c · vol(P)`.  This is the correctly normalised object: the patch
  enters with its *volume*, not with a bare value.
* `patch_lowerContribution_le` : the "lower sum" form used by the enclosure
  machinery, `vol(P)·c − err ≤ ∫_Ω f`, i.e. patch lower contribution plus a
  nonnegative complement.
* `nullPatch_lowerContribution_nonpos` : if the patch has measure zero the lower
  contribution is `−err ≤ 0`, so nothing is gained — the quantitative statement
  of why a single-momentum witness cannot work.
* `quarterSlab_volume`, `cellIntegral_ge_quarterSlab`,
  `cellIntegral_pos_of_quarterSlab` : the concrete instantiation at the
  candidate patch, a slab of half-width `δ` around the normalised momentum
  `1/4` in one direction (the momentum at which the literal Wilson cubic vertex
  is nonzero, `wilsonCubic_bgZero_diag_quarter_eq_one`).  Its volume is exactly
  `δ/4`, so the resulting floor is `c·δ/4 > 0`.

Nothing here asserts that Bałaban's constrained first variation has a positive
lower bound on such a patch; that is the remaining source datum.  What is proved
is that *one* such patch bound plus a complement sign suffices.
-/
import Mathlib

namespace YangMills

open MeasureTheory Set

/-! ## 1. The abstract patch compiler -/

/-- **Patch bound plus complement sign.**  If `f` is integrable on `Ω`, bounded
below by `c` on a measurable patch `P ⊆ Ω` of finite measure, and nonnegative on
the complement `Ω \ P`, then `∫_Ω f ≥ vol(P)·c`. -/
theorem setIntegral_ge_patch {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} {Omega P : Set X} {c : ℝ}
    (hP : MeasurableSet P) (hPsub : P ⊆ Omega) (hPfin : mu P ≠ ⊤)
    (hf : IntegrableOn f Omega mu) (hOmega : MeasurableSet Omega)
    (hpatch : ∀ x ∈ P, c ≤ f x) (hrest : ∀ x ∈ Omega \ P, 0 ≤ f x) :
    mu.real P * c ≤ ∫ x in Omega, f x ∂mu := by
  have hsplit : (∫ x in Omega ∩ P, f x ∂mu) + ∫ x in Omega \ P, f x ∂mu
      = ∫ x in Omega, f x ∂mu := integral_inter_add_diff hP hf
  have hinter : Omega ∩ P = P := Set.inter_eq_self_of_subset_right hPsub
  have hP' : mu.real P * c ≤ ∫ x in P, f x ∂mu := by
    have := setIntegral_ge_of_const_le (μ := mu) (f := f) (s := P) (c := c)
      hP hPfin hpatch (hf.mono_set hPsub)
    simpa [smul_eq_mul, mul_comm] using this
  have hrest' : 0 ≤ ∫ x in Omega \ P, f x ∂mu :=
    setIntegral_nonneg (hOmega.diff hP) hrest
  rw [← hsplit, hinter]
  linarith

/-- The lower contribution of a patch, in the shape produced by an enclosure:
`volume · (integrand lower bound) − (quadrature error)`. -/
noncomputable def lowerContribution {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (P : Set X) (c err : ℝ) : ℝ :=
  mu.real P * c - err

/-- **The enclosure compiler.**  A patch lower contribution, plus a nonnegative
complement, bounds the whole integral from below — provided the patch enclosure
is valid, i.e. the quadrature error is nonnegative. -/
theorem patch_lowerContribution_le {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} {Omega P : Set X} {c err : ℝ}
    (hP : MeasurableSet P) (hPsub : P ⊆ Omega) (hPfin : mu P ≠ ⊤)
    (hf : IntegrableOn f Omega mu) (hOmega : MeasurableSet Omega)
    (hpatch : ∀ x ∈ P, c ≤ f x) (hrest : ∀ x ∈ Omega \ P, 0 ≤ f x)
    (herr : 0 ≤ err) :
    lowerContribution mu P c err ≤ ∫ x in Omega, f x ∂mu := by
  have := setIntegral_ge_patch hP hPsub hPfin hf hOmega hpatch hrest
  unfold lowerContribution
  linarith

/-- **A measure-zero patch buys nothing.**  Its lower contribution is `−err ≤ 0`
whatever the integrand value on it.  So a witness at a single momentum — a set
of Lebesgue measure zero — cannot produce a positive floor, no matter how large
the integrand is there. -/
theorem nullPatch_lowerContribution_nonpos {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {P : Set X} {c err : ℝ} (hP : mu P = 0) (herr : 0 ≤ err) :
    lowerContribution mu P c err ≤ 0 := by
  have : mu.real P = 0 := by simp [Measure.real, hP]
  simp [lowerContribution, this, herr]

/-! ## 2. The concrete candidate patch on the momentum cell -/

/-- The project's positive-orthant momentum cell `[0,1/2]^4`. -/
def momentumCell : Set (Fin 4 → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) (1 / 2)

/-- The candidate patch: the slab of half-width `δ` around the normalised
momentum `1/4` in direction `ρ`, full cell in the other directions. -/
def quarterSlab (rho : Fin 4) (delta : ℝ) : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun mu => if mu = rho then Icc (1 / 4 - delta) (1 / 4 + delta)
    else Icc (0 : ℝ) (1 / 2)

theorem measurableSet_momentumCell : MeasurableSet momentumCell :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem measurableSet_quarterSlab (rho : Fin 4) (delta : ℝ) :
    MeasurableSet (quarterSlab rho delta) := by
  refine MeasurableSet.univ_pi fun mu => ?_
  by_cases h : mu = rho <;> simp [h, measurableSet_Icc]

theorem quarterSlab_subset {delta : ℝ} (h1 : delta ≤ 1 / 4)
    (rho : Fin 4) : quarterSlab rho delta ⊆ momentumCell := by
  refine Set.pi_mono fun mu _ => ?_
  by_cases h : mu = rho
  · simp only [if_pos h]
    exact Icc_subset_Icc (by linarith) (by linarith)
  · simp [h]

/-- **The candidate patch has positive volume, computed exactly:** `δ/4`. -/
theorem quarterSlab_volume (rho : Fin 4) (delta : ℝ) :
    volume (quarterSlab rho delta)
      = ENNReal.ofReal (2 * delta) * ENNReal.ofReal (1 / 2) ^ 3 := by
  rw [quarterSlab, volume_pi_pi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ rho)]
  simp only [if_true]
  have h1 : volume (Icc (1 / 4 - delta) (1 / 4 + delta)) = ENNReal.ofReal (2 * delta) := by
    rw [Real.volume_Icc]; ring_nf
  have h2 : ∀ mu ∈ Finset.univ.erase rho,
      volume (if mu = rho then Icc (1 / 4 - delta) (1 / 4 + delta) else Icc (0 : ℝ) (1 / 2))
        = ENNReal.ofReal (1 / 2) := by
    intro mu hmu
    rw [if_neg (Finset.mem_erase.1 hmu).1, Real.volume_Icc]
    norm_num
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_const]
  congr 1
  simp

theorem quarterSlab_volume_real {delta : ℝ} (h0 : 0 ≤ delta) (rho : Fin 4) :
    (volume (quarterSlab rho delta)).toReal = delta / 4 := by
  rw [quarterSlab_volume]
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by linarith)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

theorem quarterSlab_volume_ne_top (rho : Fin 4) (delta : ℝ) :
    volume (quarterSlab rho delta) ≠ ⊤ := by
  rw [quarterSlab_volume]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)

/-- **The concrete patch bound.**  An integrand that is nonnegative on the
momentum cell and at least `c` on the slab of half-width `δ` around normalised
momentum `1/4` has cell integral at least `(δ/4)·c`. -/
theorem cellIntegral_ge_quarterSlab {f : (Fin 4 → ℝ) → ℝ} {c delta : ℝ}
    (rho : Fin 4) (h0 : 0 ≤ delta) (h1 : delta ≤ 1 / 4)
    (hf : IntegrableOn f momentumCell)
    (hpatch : ∀ x ∈ quarterSlab rho delta, c ≤ f x)
    (hrest : ∀ x ∈ momentumCell \ quarterSlab rho delta, 0 ≤ f x) :
    (delta / 4) * c ≤ ∫ x in momentumCell, f x := by
  have := setIntegral_ge_patch (measurableSet_quarterSlab rho delta)
    (quarterSlab_subset h1 rho) (quarterSlab_volume_ne_top rho delta) hf
    measurableSet_momentumCell hpatch hrest
  rwa [Measure.real, quarterSlab_volume_real h0 rho] at this

/-- Strict positivity of the cell integral from one positive-volume patch. -/
theorem cellIntegral_pos_of_quarterSlab {f : (Fin 4 → ℝ) → ℝ} {c delta : ℝ}
    (rho : Fin 4) (h0 : 0 < delta) (h1 : delta ≤ 1 / 4) (hc : 0 < c)
    (hf : IntegrableOn f momentumCell)
    (hpatch : ∀ x ∈ quarterSlab rho delta, c ≤ f x)
    (hrest : ∀ x ∈ momentumCell \ quarterSlab rho delta, 0 ≤ f x) :
    0 < ∫ x in momentumCell, f x := by
  have h := cellIntegral_ge_quarterSlab rho (le_of_lt h0) h1 hf hpatch hrest
  nlinarith

end YangMills
