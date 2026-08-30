/-
# `L²` toolkit for the periodicity cell

The quantitative half of the increment programme is an `L²` calculation on the
periodicity cell: Cauchy–Schwarz for the pressure pairing, Young's inequality
for the absorption into the dissipation, and the elementary bookkeeping
(finite sums, absolute values) that both need.  This file collects those tools
in the `cellInt` carrier already used by the development.

## What is proved here

* `ClayNS.cellInt_sum` — the cell integral of a finite sum is the sum of the
  cell integrals.
* `ClayNS.abs_cellInt_le` — `|∫ f| ≤ ∫ |f|`.
* `ClayNS.cellInt_cauchy_schwarz` — `(∫ f g)² ≤ (∫ f²)(∫ g²)`, proved from
  scratch by the discriminant argument.
* `ClayNS.cellInt_mul_le_young` — the weighted Young inequality
  `∫ w·a·b ≤ η ∫ w a² + (1/(4η)) ∫ w b²` for a nonnegative weight `w`, which is
  the exact shape consumed by the pressure absorption.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CellShift

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- Continuity of the divergence of a smooth field. -/
lemma continuous_divg {W : STime → E3} (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    Continuous (fun z : STime => divg W z) := by
  have hrw : (fun z : STime => divg W z) = fun z => ∑ i, dvec (0, ee i) (fun w => W w i) z := by
    funext z
    refine Finset.sum_congr rfl fun i _ => ?_
    exact dvec_coord _ z (differentiable_of_contDiffTop hW z) (0, ee i) i
  rw [hrw]
  exact continuous_finset_sum _ fun i _ =>
    continuous_dvec _ (contDiff_coord _ hW i) (0, ee i)

/-- The cell integral of a finite sum of continuous fields. -/
lemma cellInt_sum {ι : Type*} (S : Finset ι) (f : ι → E3 → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    cellInt (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, cellInt (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [cellInt]
  | insert a S ha ih =>
      have hcont : Continuous (fun x : E3 => ∑ i ∈ S, f i x) :=
        continuous_finset_sum _ fun i _ => hf i
      rw [show (fun x : E3 => ∑ i ∈ insert a S, f i x)
          = fun x : E3 => f a x + ∑ i ∈ S, f i x from by
        funext x; rw [Finset.sum_insert ha]]
      rw [cellInt_add (hf a) hcont, ih, Finset.sum_insert ha]

/-- `|∫_cell f| ≤ ∫_cell |f|`. -/
lemma abs_cellInt_le {f : E3 → ℝ} (hf : Continuous f) :
    |cellInt f| ≤ cellInt (fun x => |f x|) := by
  have h1 : cellInt f ≤ cellInt (fun x => |f x|) :=
    cellInt_mono hf hf.abs fun x => le_abs_self _
  have h2 : -cellInt f ≤ cellInt (fun x => |f x|) := by
    have := cellInt_mono hf.neg hf.abs (fun x => neg_le_abs (f x))
    rwa [cellInt_neg] at this
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- **Cauchy–Schwarz on the periodicity cell.** -/
theorem cellInt_cauchy_schwarz {f g : E3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (cellInt (fun x => f x * g x)) ^ 2
      ≤ cellInt (fun x => (f x) ^ 2) * cellInt (fun x => (g x) ^ 2) := by
  set A := cellInt (fun x => (f x) ^ 2) with hA
  set B := cellInt (fun x => (g x) ^ 2) with hB
  set C := cellInt (fun x => f x * g x) with hC
  have hexp : ∀ lam : ℝ, 0 ≤ A + 2 * lam * C + lam ^ 2 * B := by
    intro lam
    have hnn : (0:ℝ) ≤ cellInt (fun x => (f x + lam * g x) ^ 2) :=
      cellInt_nonneg fun x => sq_nonneg _
    have hsplit : cellInt (fun x => (f x + lam * g x) ^ 2)
        = A + 2 * lam * C + lam ^ 2 * B := by
      have hcongr : ∀ x : E3, (f x + lam * g x) ^ 2
          = (f x) ^ 2 + (2 * lam) * (f x * g x) + (lam ^ 2) * (g x) ^ 2 := by
        intro x; ring
      rw [cellInt_congr hcongr]
      have hc1 : Continuous (fun x : E3 => (f x) ^ 2) := hf.pow 2
      have hc2 : Continuous (fun x : E3 => (2 * lam) * (f x * g x)) :=
        continuous_const.mul (hf.mul hg)
      have hc3 : Continuous (fun x : E3 => (lam ^ 2) * (g x) ^ 2) :=
        continuous_const.mul (hg.pow 2)
      rw [cellInt_add (f := fun x : E3 => (f x) ^ 2 + (2 * lam) * (f x * g x))
          (g := fun x : E3 => (lam ^ 2) * (g x) ^ 2) (hc1.add hc2) hc3,
        cellInt_add (f := fun x : E3 => (f x) ^ 2)
          (g := fun x : E3 => (2 * lam) * (f x * g x)) hc1 hc2,
        cellInt_const_mul (2 * lam) (fun x => f x * g x),
        cellInt_const_mul (lam ^ 2) (fun x => (g x) ^ 2)]
    rw [hsplit] at hnn
    exact hnn
  have hBnn : 0 ≤ B := cellInt_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · -- degenerate case: `B = 0` forces `C = 0`
    have hCzero : C = 0 := by
      by_contra hne
      have hlam := hexp (-(A + 1) / (2 * C))
      rw [← hB0] at hlam
      have h2C : (2 : ℝ) * C ≠ 0 := by
        simpa using hne
      have : 2 * (-(A + 1) / (2 * C)) * C = -(A + 1) := by
        field_simp
      rw [this] at hlam
      simp at hlam
      linarith
    rw [hCzero, ← hB0]
    simp
  · have hlam := hexp (-C / B)
    have hkey : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hkey] at hlam
    have hdiv : C ^ 2 / B ≤ A := by linarith
    calc C ^ 2 = (C ^ 2 / B) * B := by field_simp
      _ ≤ A * B := mul_le_mul_of_nonneg_right hdiv hBpos.le

/-- **Weighted Young inequality on the cell.**  For a nonnegative continuous
weight `w` and `η > 0`, `∫ w·a·b ≤ η ∫ w a² + (1/(4η)) ∫ w b²`. -/
theorem cellInt_mul_le_young {w a b : E3 → ℝ} (hw : Continuous w) (ha : Continuous a)
    (hb : Continuous b) (hwnn : ∀ x, 0 ≤ w x) {eta : ℝ} (heta : 0 < eta) :
    cellInt (fun x => w x * (a x * b x))
      ≤ eta * cellInt (fun x => w x * (a x) ^ 2)
        + (1 / (4 * eta)) * cellInt (fun x => w x * (b x) ^ 2) := by
  have hpt : ∀ x : E3, w x * (a x * b x)
      ≤ eta * (w x * (a x) ^ 2) + (1 / (4 * eta)) * (w x * (b x) ^ 2) := by
    intro x
    have hkey : a x * b x ≤ eta * (a x) ^ 2 + (1 / (4 * eta)) * (b x) ^ 2 := by
      have hid : eta * (a x) ^ 2 + (1 / (4 * eta)) * (b x) ^ 2 - a x * b x
          = (1 / (4 * eta)) * (2 * eta * a x - b x) ^ 2 := by
        field_simp
        ring
      have hnn : 0 ≤ (1 / (4 * eta)) * (2 * eta * a x - b x) ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      linarith [hid ▸ hnn]
    have := mul_le_mul_of_nonneg_left hkey (hwnn x)
    nlinarith [this]
  have hcont1 : Continuous (fun x : E3 => w x * (a x * b x)) := hw.mul (ha.mul hb)
  have hcont2 : Continuous (fun x : E3 => eta * (w x * (a x) ^ 2) +
      (1 / (4 * eta)) * (w x * (b x) ^ 2)) :=
    (continuous_const.mul (hw.mul (ha.pow 2))).add (continuous_const.mul (hw.mul (hb.pow 2)))
  have hmono := cellInt_mono hcont1 hcont2 hpt
  have hc1 : Continuous (fun x : E3 => eta * (w x * (a x) ^ 2)) :=
    continuous_const.mul (hw.mul (ha.pow 2))
  have hc2 : Continuous (fun x : E3 => (1 / (4 * eta)) * (w x * (b x) ^ 2)) :=
    continuous_const.mul (hw.mul (hb.pow 2))
  have hsplit : cellInt (fun x => eta * (w x * (a x) ^ 2) + (1 / (4 * eta)) * (w x * (b x) ^ 2))
      = eta * cellInt (fun x => w x * (a x) ^ 2)
        + (1 / (4 * eta)) * cellInt (fun x => w x * (b x) ^ 2) := by
    rw [cellInt_add (f := fun x : E3 => eta * (w x * (a x) ^ 2))
      (g := fun x : E3 => (1 / (4 * eta)) * (w x * (b x) ^ 2)) hc1 hc2,
      cellInt_const_mul eta (fun x => w x * (a x) ^ 2),
      cellInt_const_mul (1 / (4 * eta)) (fun x => w x * (b x) ^ 2)]
  rw [hsplit] at hmono
  exact hmono

end ClayNS
