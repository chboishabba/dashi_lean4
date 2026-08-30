/-
# The two-zero window instance: three narrow windows with a nonsingular response matrix

`ThreeWindowPointGate` produces three *point* window centres whose point-window response
matrix is nonsingular at three prescribed distinct positive heights.  This module
transports that to actual tapers.

The tapers are the ones already used in the one-zero lane: unit-mass tent tapers in
symmetric modulus windows of a common half-width `e`, one shared window at `c_p` and one
each at `c₀ < c₁ < c₂`, combined as `g_j = p + q_j`.  By
`targetLeadingCoeff_add_smul` the leading response of `g_j` at height `x` is

    T_j(x) = A(x) + 2 B_j(x) + D_j(x),

with `A`, `D_j` the *within-window self responses* and `B_j` the cross response.  The
unit-mass endpoint bounds of `LiteralWeilNormalizedWindowBounds` give

    0 ≤ A(x) ≤ cap(x, c_p−e, c_p+e),   0 ≤ D_j(x) ≤ cap(x, c_j−e, c_j+e),
    cap(x, c_p+e, c_j−e) ≤ B_j(x) ≤ cap(x, c_p−e, c_j+e),

and all four brackets collapse to the point value `cap(x, c_p, c_j)` as `e → 0`.  So the
whole `3 × 3` matrix converges entrywise to twice the point-window matrix, whose
determinant is nonzero; an explicit entrywise perturbation bound
(`ThreeTaperCrossDetLeading.det3_ne_zero_of_close`) plus continuity in `e` then makes the
actual determinant nonzero for all sufficiently narrow windows.

Feeding that into `LiteralWeilThreeTaperCoefficientGate` gives the **inhabited two-zero
Schur admission**: for three literal zeros of pairwise distinct positive heights and
positive multiplicities there is an explicitly constructed positive taper triple and a
radius threshold below which the target response survives the *exact* elimination of
both nuisance responses.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilNarrowWindowDomination
import Zeta23Bridge.ThreeWindowPointGate
import Zeta23Bridge.LiteralWeilThreeTaperCoefficientGate

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace LiteralWeilThreeWindowNarrowInstance

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilNormalizedWindowBounds
open Zeta23Bridge.LiteralWeilNarrowWindowDomination
open Zeta23Bridge.LiteralWeilWindowSeparationInstance
open Zeta23Bridge.LiteralWeilThreeTaperCoefficientGate
open Zeta23Bridge.CoshWindowSeparation
open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.ThreeTaperCrossDetLeading
open Zeta23Bridge.ThreeWindowPointGate
open Zeta23Bridge.MultiTaperSchurCore

/-! ## Monotonicity of the endpoint kernel -/

theorem responseFloor_eq_responseCap (x u v : ℝ) : responseFloor x u v = responseCap x u v :=
  rfl

theorem responseCap_self (x u : ℝ) : responseCap x u u = 0 := by
  unfold responseCap
  ring

/-- The endpoint kernel is monotone under widening of the modulus bracket. -/
theorem responseCap_mono {x u v u' v' : ℝ} (hx : 0 < x) (hu' : 0 < u') (h1 : u' ≤ u)
    (h2 : u ≤ v) (h3 : v ≤ v') : responseCap x u v ≤ responseCap x u' v' := by
  have hu : 0 < u := lt_of_lt_of_le hu' h1
  have hc1 : Real.cosh (x * v) ≤ Real.cosh (x * v') := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ x * v),
      abs_of_nonneg (by nlinarith : (0:ℝ) ≤ x * v')]
    nlinarith
  have hc2 : Real.cosh (x * u') ≤ Real.cosh (x * u) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x * u'),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x * u)]
    nlinarith
  have hd1 : 0 ≤ coshDiff x u v := by
    unfold coshDiff
    have : Real.cosh (x * u) ≤ Real.cosh (x * v) := by
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x * u),
        abs_of_nonneg (by nlinarith : (0:ℝ) ≤ x * v)]
      nlinarith
    linarith
  have hd2 : coshDiff x u v ≤ coshDiff x u' v' := by
    unfold coshDiff at *
    linarith
  have hsq1 : 0 ≤ v ^ 2 - u ^ 2 := by nlinarith
  have hsq2 : v ^ 2 - u ^ 2 ≤ v' ^ 2 - u' ^ 2 := by nlinarith
  unfold responseCap
  nlinarith [hd1, hd2, hsq1, hsq2]

/-! ## The entrywise deviation budget of the narrow windows -/

/-- The entrywise deviation of the actual `(i, j)` response from twice the point-window
value: the two self-response caps plus twice the width of the cross-response bracket. -/
def entryDev (x cp c e : ℝ) : ℝ :=
  responseCap x (cp - e) (cp + e) + responseCap x (c - e) (c + e)
    + 2 * (responseCap x (cp - e) (c + e) - responseCap x (cp + e) (c - e))

/-- The total deviation budget of the `3 × 3` response matrix. -/
def devBudget (a₁ a₂ a₃ cp c₀ c₁ c₂ e : ℝ) : ℝ :=
  entryDev a₁ cp c₀ e + entryDev a₁ cp c₁ e + entryDev a₁ cp c₂ e
    + entryDev a₂ cp c₀ e + entryDev a₂ cp c₁ e + entryDev a₂ cp c₂ e
    + entryDev a₃ cp c₀ e + entryDev a₃ cp c₁ e + entryDev a₃ cp c₂ e

/-- The reference (point-window) entry: twice the point cross response. -/
def refEntry (x cp c : ℝ) : ℝ := 2 * responseCap x cp c

/-- A common bound for the reference entries. -/
def refBound (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) : ℝ :=
  |refEntry a₁ cp c₀| + |refEntry a₁ cp c₁| + |refEntry a₁ cp c₂|
    + |refEntry a₂ cp c₀| + |refEntry a₂ cp c₁| + |refEntry a₂ cp c₂|
    + |refEntry a₃ cp c₀| + |refEntry a₃ cp c₁| + |refEntry a₃ cp c₂|

/-- The reference determinant of the point-window response matrix. -/
def refDet (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) : ℝ :=
  det3 ![refEntry a₁ cp c₀, refEntry a₁ cp c₁, refEntry a₁ cp c₂]
    ![refEntry a₂ cp c₀, refEntry a₂ cp c₁, refEntry a₂ cp c₂]
    ![refEntry a₃ cp c₀, refEntry a₃ cp c₁, refEntry a₃ cp c₂]

/-- The separation defect: the reference determinant minus the perturbation bound. -/
def separationDefect (a₁ a₂ a₃ cp c₀ c₁ c₂ e : ℝ) : ℝ :=
  |refDet a₁ a₂ a₃ cp c₀ c₁ c₂|
    - 18 * devBudget a₁ a₂ a₃ cp c₀ c₁ c₂ e
        * (refBound a₁ a₂ a₃ cp c₀ c₁ c₂ + devBudget a₁ a₂ a₃ cp c₀ c₁ c₂ e) ^ 2

theorem continuous_entryDev (x cp c : ℝ) : Continuous fun e : ℝ => entryDev x cp c e := by
  unfold entryDev responseCap coshDiff
  fun_prop

theorem continuous_devBudget (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) :
    Continuous fun e : ℝ => devBudget a₁ a₂ a₃ cp c₀ c₁ c₂ e := by
  unfold devBudget
  exact ((((((((continuous_entryDev a₁ cp c₀).add (continuous_entryDev a₁ cp c₁)).add
    (continuous_entryDev a₁ cp c₂)).add (continuous_entryDev a₂ cp c₀)).add
    (continuous_entryDev a₂ cp c₁)).add (continuous_entryDev a₂ cp c₂)).add
    (continuous_entryDev a₃ cp c₀)).add (continuous_entryDev a₃ cp c₁)).add
    (continuous_entryDev a₃ cp c₂)

theorem continuous_separationDefect (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) :
    Continuous fun e : ℝ => separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ e := by
  unfold separationDefect
  exact continuous_const.sub (((continuous_const.mul
    (continuous_devBudget a₁ a₂ a₃ cp c₀ c₁ c₂)).mul
      ((continuous_const.add (continuous_devBudget a₁ a₂ a₃ cp c₀ c₁ c₂)).pow 2)))

theorem entryDev_zero (x cp c : ℝ) : entryDev x cp c 0 = 0 := by
  unfold entryDev
  simp [responseCap_self]

theorem devBudget_zero (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) :
    devBudget a₁ a₂ a₃ cp c₀ c₁ c₂ 0 = 0 := by
  unfold devBudget
  simp [entryDev_zero]

theorem separationDefect_zero_pos {a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ}
    (hdet : refDet a₁ a₂ a₃ cp c₀ c₁ c₂ ≠ 0) :
    0 < separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ 0 := by
  unfold separationDefect
  rw [devBudget_zero]
  simpa using abs_pos.mpr hdet

/-- **A narrow radius exists for the three-window configuration.** -/
theorem exists_narrow_radius3 {a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ} (hcp : 0 < cp)
    (h₀ : cp < c₀) (h₁ : c₀ < c₁) (h₂ : c₁ < c₂)
    (hdet : refDet a₁ a₂ a₃ cp c₀ c₁ c₂ ≠ 0) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℝ, 0 < e → e ≤ e0 →
      e < cp ∧ cp + e < c₀ - e ∧ c₀ + e < c₁ - e ∧ c₁ + e < c₂ - e ∧
        0 < separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ e := by
  have hopen : IsOpen {e : ℝ | 0 < separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ e} :=
    isOpen_lt continuous_const (continuous_separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂)
  have hmem : (0 : ℝ) ∈ {e : ℝ | 0 < separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ e} :=
    separationDefect_zero_pos hdet
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  refine ⟨min (min (eps / 2) (cp / 2))
    (min ((c₀ - cp) / 4) (min ((c₁ - c₀) / 4) ((c₂ - c₁) / 4))), ?_, ?_⟩
  · exact lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  · intro e hepos hele
    have he1 : e ≤ eps / 2 := hele.trans (le_trans (min_le_left _ _) (min_le_left _ _))
    have he2 : e ≤ cp / 2 := hele.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have he3 : e ≤ (c₀ - cp) / 4 :=
      hele.trans (le_trans (min_le_right _ _) (min_le_left _ _))
    have he4 : e ≤ (c₁ - c₀) / 4 :=
      hele.trans (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have he5 : e ≤ (c₂ - c₁) / 4 :=
      hele.trans (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hin : e ∈ Metric.ball (0 : ℝ) eps := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hepos]
      linarith
    exact ⟨by linarith, by linarith, by linarith, by linarith, hball hin⟩

/-! ## The actual narrow-window response matrix -/

/-- The three-taper family of the two-zero lane: a shared narrow window at `c_p` plus one
narrow window at each of `c₀ < c₁ < c₂`. -/
def windowTriple (cp c₀ c₁ c₂ e : ℝ) : Fin 3 → ℝ → ℝ :=
  ![fun u => narrowTaper cp e u + 1 * narrowTaper c₀ e u,
    fun u => narrowTaper cp e u + 1 * narrowTaper c₁ e u,
    fun u => narrowTaper cp e u + 1 * narrowTaper c₂ e u]

/-- The entrywise deviation bound for one entry of the response matrix. -/
theorem abs_targetLeadingCoeff_sub_refEntry_le {cp c e x : ℝ}
    (hx : 0 < x) (hcp : 0 < cp - e) (he : 0 < e) (hsep : cp + e < c - e) :
    |targetLeadingCoeff (fun u => narrowTaper cp e u + 1 * narrowTaper c e u) x
        - refEntry x cp c| ≤ entryDev x cp c e := by
  have hc : 0 < c - e := by linarith
  have hp : WindowTaper (narrowTaper cp e) (cp - e) (cp + e) := narrowTaper_window hcp he
  have hq : WindowTaper (narrowTaper c e) (c - e) (c + e) := narrowTaper_window hc he
  have hpm : (∫ u : ℝ, narrowTaper cp e u) = 1 := narrowTaper_mass hcp he
  have hqm : (∫ u : ℝ, narrowTaper c e u) = 1 := narrowTaper_mass hc he
  have hpw : WindowTaper (narrowTaper cp e) (cp - e) (c + e) := hp.mono le_rfl (by linarith)
  have hqw : WindowTaper (narrowTaper c e) (cp - e) (c + e) := hq.mono (by linarith) le_rfl
  -- the expansion of the leading coefficient
  have hexp : targetLeadingCoeff (fun u => narrowTaper cp e u + 1 * narrowTaper c e u) x
      = targetLeadingCoeff (narrowTaper cp e) x
        + 2 * covForm (narrowTaper cp e) (narrowTaper c e) x
        + targetLeadingCoeff (narrowTaper c e) x := by
    rw [targetLeadingCoeff_add_smul hp.cont hp.cpt hq.cont hq.cpt 1 x]
    ring
  -- the four endpoint bounds
  have hA0 : 0 ≤ targetLeadingCoeff (narrowTaper cp e) x :=
    targetLeadingCoeff_nonneg hp.cont hp.cpt hp.nonneg x
  have hA1 : targetLeadingCoeff (narrowTaper cp e) x ≤ responseCap x (cp - e) (cp + e) :=
    targetLeadingCoeff_le_unitMass hp hpm hx hcp
  have hD0 : 0 ≤ targetLeadingCoeff (narrowTaper c e) x :=
    targetLeadingCoeff_nonneg hq.cont hq.cpt hq.nonneg x
  have hD1 : targetLeadingCoeff (narrowTaper c e) x ≤ responseCap x (c - e) (c + e) :=
    targetLeadingCoeff_le_unitMass hq hqm hx hc
  have hB1 : covForm (narrowTaper cp e) (narrowTaper c e) x ≤ responseCap x (cp - e) (c + e) :=
    covForm_le_unitMass hpw hqw hpm hqm hx hcp
  have hB0 : responseCap x (cp + e) (c - e)
      ≤ covForm (narrowTaper cp e) (narrowTaper c e) x := by
    rw [← responseFloor_eq_responseCap]
    exact covForm_ge_unitMass hp hq hpm hqm hx hcp (by linarith) hsep
  -- the point value sits between the two brackets
  have hpt1 : responseCap x cp c ≤ responseCap x (cp - e) (c + e) :=
    responseCap_mono hx (by linarith) (by linarith) (by linarith) (by linarith)
  have hpt0 : responseCap x (cp + e) (c - e) ≤ responseCap x cp c :=
    responseCap_mono hx (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hexp, abs_le]
  unfold refEntry entryDev
  constructor <;> linarith

theorem refEntry_le_refBound (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) :
    (∀ j, |(![refEntry a₁ cp c₀, refEntry a₁ cp c₁, refEntry a₁ cp c₂] : Fin 3 → ℝ) j|
        ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂) ∧
      (∀ j, |(![refEntry a₂ cp c₀, refEntry a₂ cp c₁, refEntry a₂ cp c₂] : Fin 3 → ℝ) j|
        ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂) ∧
      (∀ j, |(![refEntry a₃ cp c₀, refEntry a₃ cp c₁, refEntry a₃ cp c₂] : Fin 3 → ℝ) j|
        ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂) := by
  have key : ∀ x y z : ℝ, |x| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ →
      |y| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ → |z| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ →
      ∀ j, |(![x, y, z] : Fin 3 → ℝ) j| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    intro x y z hx hy hz j
    fin_cases j
    · exact hx
    · exact hy
    · exact hz
  have n0 : (0:ℝ) ≤ |refEntry a₁ cp c₀| := abs_nonneg _
  have n1 : (0:ℝ) ≤ |refEntry a₁ cp c₁| := abs_nonneg _
  have n2 : (0:ℝ) ≤ |refEntry a₁ cp c₂| := abs_nonneg _
  have n3 : (0:ℝ) ≤ |refEntry a₂ cp c₀| := abs_nonneg _
  have n4 : (0:ℝ) ≤ |refEntry a₂ cp c₁| := abs_nonneg _
  have n5 : (0:ℝ) ≤ |refEntry a₂ cp c₂| := abs_nonneg _
  have n6 : (0:ℝ) ≤ |refEntry a₃ cp c₀| := abs_nonneg _
  have n7 : (0:ℝ) ≤ |refEntry a₃ cp c₁| := abs_nonneg _
  have n8 : (0:ℝ) ≤ |refEntry a₃ cp c₂| := abs_nonneg _
  have h0 : |refEntry a₁ cp c₀| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h1 : |refEntry a₁ cp c₁| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h2 : |refEntry a₁ cp c₂| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h3 : |refEntry a₂ cp c₀| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h4 : |refEntry a₂ cp c₁| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h5 : |refEntry a₂ cp c₂| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h6 : |refEntry a₃ cp c₀| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h7 : |refEntry a₃ cp c₁| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  have h8 : |refEntry a₃ cp c₂| ≤ refBound a₁ a₂ a₃ cp c₀ c₁ c₂ := by
    unfold refBound; linarith
  exact ⟨key _ _ _ h0 h1 h2, key _ _ _ h3 h4 h5, key _ _ _ h6 h7 h8⟩

theorem entryDev_nonneg {x cp c e : ℝ} (hx : 0 < x) (hcp : 0 < cp - e) (he : 0 < e)
    (hsep : cp + e < c - e) : 0 ≤ entryDev x cp c e := by
  have h := abs_targetLeadingCoeff_sub_refEntry_le hx hcp he hsep
  exact le_trans (abs_nonneg _) h

/-- **The narrow-window response matrix is nonsingular.**  For three distinct positive
heights and any admissible point-window configuration with nonzero reference
determinant, all sufficiently narrow windows give a nonsingular actual `3 × 3` leading
response matrix. -/
theorem det3_targetLeadingCoeff_ne_zero {a₁ a₂ a₃ cp c₀ c₁ c₂ e : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hcpe : e < cp) (he : 0 < e)
    (hs₀ : cp + e < c₀ - e) (hs₁ : c₀ + e < c₁ - e) (hs₂ : c₁ + e < c₂ - e)
    (hdefect : 0 < separationDefect a₁ a₂ a₃ cp c₀ c₁ c₂ e) :
    det3 (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₁)
      (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₂)
      (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₃) ≠ 0 := by
  have hcp : 0 < cp - e := by linarith
  have hsep₀ : cp + e < c₀ - e := hs₀
  have hsep₁ : cp + e < c₁ - e := by linarith
  have hsep₂ : cp + e < c₂ - e := by linarith
  set M : ℝ := refBound a₁ a₂ a₃ cp c₀ c₁ c₂ with hMdef
  set d : ℝ := devBudget a₁ a₂ a₃ cp c₀ c₁ c₂ e with hddef
  obtain ⟨hb₁, hb₂, hb₃⟩ := refEntry_le_refBound a₁ a₂ a₃ cp c₀ c₁ c₂
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hb₁ 0)
  -- the nine entry deviations, and their nonnegativity
  have e₁₀ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₀) (e := e) ha₁ hcp he hsep₀
  have e₁₁ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₁) (e := e) ha₁ hcp he hsep₁
  have e₁₂ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₂) (e := e) ha₁ hcp he hsep₂
  have e₂₀ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₀) (e := e) ha₂ hcp he hsep₀
  have e₂₁ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₁) (e := e) ha₂ hcp he hsep₁
  have e₂₂ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₂) (e := e) ha₂ hcp he hsep₂
  have e₃₀ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₀) (e := e) ha₃ hcp he hsep₀
  have e₃₁ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₁) (e := e) ha₃ hcp he hsep₁
  have e₃₂ := abs_targetLeadingCoeff_sub_refEntry_le (cp := cp) (c := c₂) (e := e) ha₃ hcp he hsep₂
  have n₁₀ := entryDev_nonneg ha₁ hcp he hsep₀
  have n₁₁ := entryDev_nonneg ha₁ hcp he hsep₁
  have n₁₂ := entryDev_nonneg ha₁ hcp he hsep₂
  have n₂₀ := entryDev_nonneg ha₂ hcp he hsep₀
  have n₂₁ := entryDev_nonneg ha₂ hcp he hsep₁
  have n₂₂ := entryDev_nonneg ha₂ hcp he hsep₂
  have n₃₀ := entryDev_nonneg ha₃ hcp he hsep₀
  have n₃₁ := entryDev_nonneg ha₃ hcp he hsep₁
  have n₃₂ := entryDev_nonneg ha₃ hcp he hsep₂
  have hd0 : 0 ≤ d := by
    rw [hddef]; unfold devBudget; linarith
  have hdsum : d = entryDev a₁ cp c₀ e + entryDev a₁ cp c₁ e + entryDev a₁ cp c₂ e
      + entryDev a₂ cp c₀ e + entryDev a₂ cp c₁ e + entryDev a₂ cp c₂ e
      + entryDev a₃ cp c₀ e + entryDev a₃ cp c₁ e + entryDev a₃ cp c₂ e := by
    rw [hddef]; unfold devBudget; ring
  refine det3_ne_zero_of_close (M := M) (d := d)
    (u' := ![refEntry a₁ cp c₀, refEntry a₁ cp c₁, refEntry a₁ cp c₂])
    (v' := ![refEntry a₂ cp c₀, refEntry a₂ cp c₁, refEntry a₂ cp c₂])
    (w' := ![refEntry a₃ cp c₀, refEntry a₃ cp c₁, refEntry a₃ cp c₂])
    hM0 hd0 hb₁ hb₂ hb₃ ?_ ?_ ?_ ?_
  · intro j
    fin_cases j
    · exact le_trans e₁₀ (by linarith)
    · exact le_trans e₁₁ (by linarith)
    · exact le_trans e₁₂ (by linarith)
  · intro j
    fin_cases j
    · exact le_trans e₂₀ (by linarith)
    · exact le_trans e₂₁ (by linarith)
    · exact le_trans e₂₂ (by linarith)
  · intro j
    fin_cases j
    · exact le_trans e₃₀ (by linarith)
    · exact le_trans e₃₁ (by linarith)
    · exact le_trans e₃₂ (by linarith)
  · have := hdefect
    unfold separationDefect refDet at this
    linarith


/-! ## Identification of the reference matrix with the point-window gate -/

theorem refEntry_eq_pointCross (x cp c : ℝ) : refEntry x cp c = 2 * pointCross cp c x := by
  unfold refEntry responseCap coshDiff pointCross coshDiffAt
  ring

theorem refDet_eq_pointCrossDet (a₁ a₂ a₃ cp c₀ c₁ c₂ : ℝ) :
    refDet a₁ a₂ a₃ cp c₀ c₁ c₂
      = 8 * det3 ![pointCross cp c₀ a₁, pointCross cp c₁ a₁, pointCross cp c₂ a₁]
          ![pointCross cp c₀ a₂, pointCross cp c₁ a₂, pointCross cp c₂ a₂]
          ![pointCross cp c₀ a₃, pointCross cp c₁ a₃, pointCross cp c₂ a₃] := by
  unfold refDet
  simp only [refEntry_eq_pointCross]
  rw [det3_cons, det3_cons]
  ring

/-- **The point-window gate transports to the reference determinant.** -/
theorem exists_centres_refDet_ne_zero {a₁ a₂ a₃ cp : ℝ}
    (ha₁ : 0 < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃) (hcp : 0 < cp) :
    ∃ c₀ c₁ c₂ : ℝ, cp < c₀ ∧ c₀ < c₁ ∧ c₁ < c₂ ∧ refDet a₁ a₂ a₃ cp c₀ c₁ c₂ ≠ 0 := by
  obtain ⟨c₀, c₁, c₂, h₀, h₁, h₂, hdet⟩ :=
    exists_centres_pointCrossDet_ne_zero ha₁ h₁₂ h₂₃ hcp
  refine ⟨c₀, c₁, c₂, h₀, h₁, h₂, ?_⟩
  rw [refDet_eq_pointCrossDet]
  simpa using hdet

/-! ## The taper triple is an admissible positive family -/

theorem windowTriple_cont {cp c₀ c₁ c₂ e : ℝ} (hcp : 0 < cp - e) (he : 0 < e)
    (h₀ : cp < c₀) (h₁ : c₀ < c₁) (h₂ : c₁ < c₂) (j : Fin 3) :
    Continuous (windowTriple cp c₀ c₁ c₂ e j) := by
  have hp := (narrowTaper_window hcp he).cont
  have hq₀ := (narrowTaper_window (c := c₀) (by linarith) he).cont
  have hq₁ := (narrowTaper_window (c := c₁) (by linarith) he).cont
  have hq₂ := (narrowTaper_window (c := c₂) (by linarith) he).cont
  fin_cases j
  · exact hp.add (continuous_const.mul hq₀)
  · exact hp.add (continuous_const.mul hq₁)
  · exact hp.add (continuous_const.mul hq₂)

theorem windowTriple_cpt {cp c₀ c₁ c₂ e : ℝ} (hcp : 0 < cp - e) (he : 0 < e)
    (h₀ : cp < c₀) (h₁ : c₀ < c₁) (h₂ : c₁ < c₂) (j : Fin 3) :
    HasCompactSupport (windowTriple cp c₀ c₁ c₂ e j) := by
  have hp := (narrowTaper_window hcp he).cpt
  have hq₀ := (narrowTaper_window (c := c₀) (by linarith) he).cpt
  have hq₁ := (narrowTaper_window (c := c₁) (by linarith) he).cpt
  have hq₂ := (narrowTaper_window (c := c₂) (by linarith) he).cpt
  fin_cases j
  · exact hp.add (hq₀.mul_left)
  · exact hp.add (hq₁.mul_left)
  · exact hp.add (hq₂.mul_left)

theorem windowTriple_nonneg {cp c₀ c₁ c₂ e : ℝ} (hcp : 0 < cp - e) (he : 0 < e)
    (h₀ : cp < c₀) (h₁ : c₀ < c₁) (h₂ : c₁ < c₂) (j : Fin 3) (u : ℝ) :
    0 ≤ windowTriple cp c₀ c₁ c₂ e j u := by
  have hp := (narrowTaper_window hcp he).nonneg u
  have hq₀ := (narrowTaper_window (c := c₀) (by linarith) he).nonneg u
  have hq₁ := (narrowTaper_window (c := c₁) (by linarith) he).nonneg u
  have hq₂ := (narrowTaper_window (c := c₂) (by linarith) he).nonneg u
  fin_cases j
  · exact add_nonneg hp (by linarith : (0:ℝ) ≤ 1 * narrowTaper c₀ e u)
  · exact add_nonneg hp (by linarith : (0:ℝ) ≤ 1 * narrowTaper c₁ e u)
  · exact add_nonneg hp (by linarith : (0:ℝ) ≤ 1 * narrowTaper c₂ e u)

/-! ## The constructed nonsingular window triple -/

/-- **An explicitly constructed taper triple whose actual leading response matrix at three
prescribed distinct positive heights is nonsingular.**  No hypothesis beyond the ordering
of the three heights: the centres and the common window half-width are produced by the
construction. -/
theorem exists_windowTriple_det3_targetLeadingCoeff_ne_zero {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃) :
    ∃ cp c₀ c₁ c₂ e : ℝ, 0 < cp - e ∧ 0 < e ∧ cp < c₀ ∧ c₀ < c₁ ∧ c₁ < c₂ ∧
      det3 (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₁)
        (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₂)
        (fun j => targetLeadingCoeff (windowTriple cp c₀ c₁ c₂ e j) a₃) ≠ 0 := by
  have ha₂ : 0 < a₂ := ha₁.trans h₁₂
  have ha₃ : 0 < a₃ := ha₂.trans h₂₃
  obtain ⟨c₀, c₁, c₂, h₀, h₁, h₂, hdet⟩ :=
    exists_centres_refDet_ne_zero (cp := 1) ha₁ h₁₂ h₂₃ one_pos
  obtain ⟨e0, he0, hprop⟩ := exists_narrow_radius3 (cp := 1) one_pos h₀ h₁ h₂ hdet
  obtain ⟨hlt, hs₀, hs₁, hs₂, hdefect⟩ := hprop e0 he0 le_rfl
  exact ⟨1, c₀, c₁, c₂, e0, by linarith, he0, h₀, h₁, h₂,
    det3_targetLeadingCoeff_ne_zero ha₁ ha₂ ha₃ hlt he0 hs₀ hs₁ hs₂ hdefect⟩

/-! ## The inhabited two-zero Schur admission -/

/-- **The first inhabited two-nuisance-zero literal Schur admission.**

For three literal zeros of pairwise distinct positive height moduli there is an
*explicitly constructed* triple of continuous, compactly supported, nonnegative tapers
and a positive radius threshold below which the target response survives the **exact**
removal of both nuisance responses, with strictly positive residual energy.

Nothing is assumed here beyond the ordering of the three heights: the window centres,
the window half-width and the radius threshold are all produced by the construction. -/
theorem exists_taper_triple_two_zero_admission {σ₁ σ₂ ρ : Zeros}
    (ha₁ : 0 < heightOf σ₁) (h₁₂ : heightOf σ₁ < heightOf σ₂)
    (h₂₃ : heightOf σ₂ < heightOf ρ) :
    ∃ g : Fin 3 → ℝ → ℝ, (∀ j, Continuous (g j)) ∧ (∀ j, HasCompactSupport (g j)) ∧
      (∀ j u, 0 ≤ g j u) ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
        elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ) ≠ 0 ∧
          0 < normSqP (elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂)
            (zeroRespVec3 g r ρ)) ∧
          ∀ x : Fin 3 → ℝ,
            elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂)
                (zeroRespVec3 g r σ₁ + zeroRespVec3 g r σ₂ + x)
              = elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) x := by
  obtain ⟨cp, c₀, c₁, c₂, e, hcp, he, h₀, h₁, h₂, hdet⟩ :=
    exists_windowTriple_det3_targetLeadingCoeff_ne_zero ha₁ h₁₂ h₂₃
  refine ⟨windowTriple cp c₀ c₁ c₂ e, windowTriple_cont hcp he h₀ h₁ h₂,
    windowTriple_cpt hcp he h₀ h₁ h₂, windowTriple_nonneg hcp he h₀ h₁ h₂, ?_⟩
  have hm₁ : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult σ₁ : ℝ) := by
    exact_mod_cast (Zeta23.zetaZeroConfig).one_le_mult (σ₁ : ℂ) σ₁.2
  have hm₂ : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult σ₂ : ℝ) := by
    exact_mod_cast (Zeta23.zetaZeroConfig).one_le_mult (σ₂ : ℂ) σ₂.2
  have hm₃ : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := by
    exact_mod_cast (Zeta23.zetaZeroConfig).one_le_mult (ρ : ℂ) ρ.2
  have hL : tripleLeadingDet (windowTriple cp c₀ c₁ c₂ e) σ₁ σ₂ ρ ≠ 0 := by
    rw [tripleLeadingDet_eq]
    exact mul_ne_zero (by positivity) hdet
  obtain ⟨r0, hr0, hr01, hkey⟩ :=
    exists_radius_tripleDet_ne_zero (windowTriple_cont hcp he h₀ h₁ h₂)
      (windowTriple_cpt hcp he h₀ h₁ h₂) hL
  refine ⟨r0, hr0, hr01, fun r hrpos hrle => ?_⟩
  have hd : det3 (zeroRespVec3 (windowTriple cp c₀ c₁ c₂ e) r σ₁)
      (zeroRespVec3 (windowTriple cp c₀ c₁ c₂ e) r σ₂)
      (zeroRespVec3 (windowTriple cp c₀ c₁ c₂ e) r ρ) ≠ 0 := hkey r hrpos hrle
  exact ⟨elim2_ne_zero_of_det3_ne_zero hd, normSqP_elim2_pos hd,
    fun x => elim2_add_two_nuisances_of_det3_ne_zero hd x⟩

end LiteralWeilThreeWindowNarrowInstance
end Zeta23Bridge
