import Mathlib
import YangMills.FiniteGibbsResidualOscillation

/-!
# CMP119/T5 dyadic localized-residual oscillation arithmetic

Source-facing motivation:
Bałaban CMP119 §2, Eq. (2.31) gives exponential diameter decay for
localized R-terms; the Agda T5 lane packages the post-entropy numerical
tail as

  shell(d) = (1/4) (1/2)^d,
  tail(d)  = (1/2) (1/2)^d.

This file proves the REAL finite-sum mathematics needed to turn such
localized shell oscillation estimates into a bound on the complete
residual oscillation.  It does not assert the remaining source dictionary:
the selected CMP119 distance d_j(X), the literal 4D support geometry,
and the repository shell depth must still be identified on the same action.

The point is quantitative: if the selected source supplies the existing
shell estimate, the complete/Wilson Gibbs comparison loses only
exp(tail(d)), and that factor tends to one as the physical separation
depth tends to infinity.
-/

namespace RequestProject.YangMills

def cmp119DyadicShell (depth : ℕ) : ℝ :=
  (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ depth

def cmp119DyadicTailMajorant (depth : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ depth

theorem cmp119_dyadic_shell_nonnegative (depth : ℕ) :
    0 ≤ cmp119DyadicShell depth := by
  positivity

theorem cmp119_dyadic_tail_nonnegative (depth : ℕ) :
    0 ≤ cmp119DyadicTailMajorant depth := by
  positivity

/-- Exact source-aligned recurrence tail(d)=shell(d)+tail(d+1). -/
theorem cmp119_dyadic_tail_step (depth : ℕ) :
    cmp119DyadicTailMajorant depth =
      cmp119DyadicShell depth +
        cmp119DyadicTailMajorant (depth + 1) := by
  unfold cmp119DyadicTailMajorant cmp119DyadicShell
  rw [pow_succ]
  ring

/-- A finite physical tail beginning at shell depth. -/
def cmp119FiniteDyadicTail : ℕ → ℕ → ℝ
  | _, 0 => 0
  | depth, count + 1 =>
      cmp119DyadicShell depth +
        cmp119FiniteDyadicTail (depth + 1) count

/--
Every finite partial residual tail is bounded by the explicit infinite
dyadic majorant used by the T5 source lane.
-/
theorem cmp119_finite_dyadic_tail_le_majorant
    (depth count : ℕ) :
    cmp119FiniteDyadicTail depth count ≤
      cmp119DyadicTailMajorant depth := by
  induction count generalizing depth with
  | zero =>
      simp [cmp119FiniteDyadicTail,
        cmp119_dyadic_tail_nonnegative]
  | succ count ih =>
      rw [cmp119FiniteDyadicTail]
      calc
        cmp119DyadicShell depth +
            cmp119FiniteDyadicTail (depth + 1) count ≤
          cmp119DyadicShell depth +
            cmp119DyadicTailMajorant (depth + 1) :=
              add_le_add_left (ih (depth + 1)) _
        _ = cmp119DyadicTailMajorant depth :=
          (cmp119_dyadic_tail_step depth).symm

/-- A shell-resolved localized effective residual. -/
def finiteLocalizedResidualTail
    {Ω : Type*}
    (shellContribution : ℕ → Ω → ℝ) :
    ℕ → ℕ → Ω → ℝ
  | _, 0, _ => 0
  | depth, count + 1, x =>
      shellContribution depth x +
        finiteLocalizedResidualTail shellContribution
          (depth + 1) count x

/--
If each physical shell oscillates by at most its configured CMP119/T5
dyadic budget, then EVERY finite collection of more distant shells has
oscillation at most the corresponding finite dyadic tail.
-/
theorem finite_localized_residual_oscillation_le_dyadic_tail
    {Ω : Type*}
    (shellContribution : ℕ → Ω → ℝ)
    (hShell :
      ∀ depth x y,
        |shellContribution depth x -
          shellContribution depth y| ≤
            cmp119DyadicShell depth)
    (depth count : ℕ) (x y : Ω) :
    |finiteLocalizedResidualTail shellContribution depth count x -
      finiteLocalizedResidualTail shellContribution depth count y| ≤
        cmp119FiniteDyadicTail depth count := by
  induction count generalizing depth with
  | zero =>
      simp [finiteLocalizedResidualTail, cmp119FiniteDyadicTail]
  | succ count ih =>
      rw [finiteLocalizedResidualTail,
        finiteLocalizedResidualTail,
        cmp119FiniteDyadicTail]
      calc
        |(shellContribution depth x +
              finiteLocalizedResidualTail shellContribution
                (depth + 1) count x) -
            (shellContribution depth y +
              finiteLocalizedResidualTail shellContribution
                (depth + 1) count y)| =
          |(shellContribution depth x -
              shellContribution depth y) +
            (finiteLocalizedResidualTail shellContribution
                (depth + 1) count x -
              finiteLocalizedResidualTail shellContribution
                (depth + 1) count y)| := by ring
        _ ≤ |shellContribution depth x -
              shellContribution depth y| +
            |finiteLocalizedResidualTail shellContribution
                (depth + 1) count x -
              finiteLocalizedResidualTail shellContribution
                (depth + 1) count y| := abs_add _ _
        _ ≤ cmp119DyadicShell depth +
            cmp119FiniteDyadicTail (depth + 1) count :=
              add_le_add (hShell depth x y)
                (ih (depth + 1))
        _ = _ := rfl

/--
The physically useful version: the same oscillation is bounded by
(1/2)2^{-depth}, uniformly in how many finite distant shells are retained.
-/
theorem finite_localized_residual_oscillation_le_majorant
    {Ω : Type*}
    (shellContribution : ℕ → Ω → ℝ)
    (hShell :
      ∀ depth x y,
        |shellContribution depth x -
          shellContribution depth y| ≤
            cmp119DyadicShell depth)
    (depth count : ℕ) (x y : Ω) :
    |finiteLocalizedResidualTail shellContribution depth count x -
      finiteLocalizedResidualTail shellContribution depth count y| ≤
        cmp119DyadicTailMajorant depth := by
  exact (finite_localized_residual_oscillation_le_dyadic_tail
    shellContribution hShell depth count x y).trans
      (cmp119_finite_dyadic_tail_le_majorant depth count)

/--
A one-point anchor turns pairwise oscillation into an interval suitable
for the sharp normalized Gibbs comparison.  The anchor is arbitrary:
a large configuration-independent vacuum energy changes center but not
the width.
-/
theorem finite_localized_residual_interval_from_anchor
    {Ω : Type*}
    (shellContribution : ℕ → Ω → ℝ)
    (hShell :
      ∀ depth x y,
        |shellContribution depth x -
          shellContribution depth y| ≤
            cmp119DyadicShell depth)
    (depth count : ℕ)
    (anchor x : Ω) :
    finiteLocalizedResidualTail shellContribution depth count anchor -
        cmp119DyadicTailMajorant depth ≤
      finiteLocalizedResidualTail shellContribution depth count x ∧
    finiteLocalizedResidualTail shellContribution depth count x ≤
      finiteLocalizedResidualTail shellContribution depth count anchor +
        cmp119DyadicTailMajorant depth := by
  have h := finite_localized_residual_oscillation_le_majorant
    shellContribution hShell depth count x anchor
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/--
The resulting normalized Gibbs comparison exponent is twice the anchored
radius, namely 2*tail(depth)=2^{-depth}. This tends to zero with depth.
The theorem is arithmetic only; applying it to literal CMP119 requires
the physical shell decomposition and source-distance dictionary.
-/
theorem cmp119_anchored_interval_oscillation_width (depth : ℕ) :
    (cmp119DyadicTailMajorant depth +
        cmp119DyadicTailMajorant depth) =
      (1 / 2 : ℝ) ^ depth := by
  unfold cmp119DyadicTailMajorant
  ring

/-- The dyadic comparison loss converges to one at increasing separation depth. -/
theorem cmp119_dyadic_gibbs_loss_tendsto_one :
    Filter.Tendsto
      (fun depth : ℕ =>
        Real.exp ((1 / 2 : ℝ) ^ depth))
      Filter.atTop
      (nhds 1) := by
  have hpow :
      Filter.Tendsto
        (fun depth : ℕ => (1 / 2 : ℝ) ^ depth)
        Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by norm_num : |(1 / 2 : ℝ)| < 1)
  simpa using (Real.continuous_exp.tendsto 0).comp hpow

end RequestProject.YangMills
