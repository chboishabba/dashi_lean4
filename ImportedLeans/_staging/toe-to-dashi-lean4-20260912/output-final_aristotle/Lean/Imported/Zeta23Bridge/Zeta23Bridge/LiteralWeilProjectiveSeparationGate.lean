/-
# The projective separation gate

`LiteralWeilTwoRadiusSeparationGate` closed the old lane with the sandwich

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ E_red(t, r),

whose right-hand side was built radius by radius from absolute values and is
therefore `O(1)` as `r → 0`.  Every projective module of this tranche exists to
replace that right-hand side.

Putting them together:

* `clusterHeightDefect_eq_threeProjectiveChannels` — in the short-taper lane the
  literal cluster height defect *is* `𝔇_{Z_off} + 𝔇_Γ + 𝔇_Π` exactly;
* `offOrdProjectiveTailQuadratic`  — `|𝔇_{Z_off}| ≤ r² · 4 · projStripCoeff · W(t)`;
* `exists_gammaProjectiveEnvelope` — `|𝔇_Γ|     ≤ r² · projStripCoeff · C_Γ`;
* `abs_poleProjectiveDefect_le'`   — `|𝔇_Π|     ≤ r² · 20 Λ² cosh(Λ/2) ‖g‖₁²`.

Hence the **projective envelope**

    |D_cluster(t, r)| ≤ r² · E_proj(g, Λ, t)                (`projectiveEnvelope`)

with `E_proj` independent of `r`.  This is the structural gain the tranche was
after: the residual side now vanishes to second order in the sampling radius,
so the gate inequality becomes a comparison of *coefficients* against the
target-local defect's own small-`r` behaviour, rather than a comparison of a small
target against an `O(1)` mass of absolute zero contributions.

**What is still not proved.**  The gate inequality itself,

    r² · E_proj(g, Λ, t) < D_{ρ*}(r),

remains open; it is a hypothesis in `false_of_projectiveEnvelope_lt_targetDefect`
and in `no_offLineZero_of_projectiveEnvelope_lt_targetDefect`, never an assertion.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilGammaProjectiveBound
import Zeta23Bridge.LiteralWeilPoleProjectiveCancellation
import Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilProjectiveSeparationGate

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilPoleProjectiveCancellation
open Zeta23Bridge.LiteralWeilProjectiveStripConstant
open Zeta23Bridge.LiteralWeilGammaProjectiveBound
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-! ## The projective envelope -/

/-- **The projective envelope coefficient.**  The `r`-independent factor bounding the
whole projectivized residual: off-ordinate zeros, gamma and pole. -/
def projectiveEnvelope (g : ℝ → ℝ) (Λ t CG : ℝ) : ℝ :=
  4 * projStripCoeff g Λ t * offOrdWeight t
    + projStripCoeff g Λ t * CG
    + 20 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2

/-- **`exists_projectiveEnvelope`.**  With one absolute constant `C_Γ`, the literal
cluster height defect of every admissible gate taper obeys a *quadratic* envelope:
the projectivized residual is `O(r²)`, whereas the old radiuswise envelope is
`O(1)`. -/
theorem exists_projectiveEnvelope :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {t r Λ : ℝ}, GateData g t r Λ →
        |clusterHeightDefect g t r| ≤ r ^ 2 * projectiveEnvelope g Λ t CG := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_gammaProjectiveEnvelope
  refine ⟨CG, hCG0, ?_⟩
  intro g t r Λ hd
  have hoff := offOrdProjectiveTailQuadratic hd.smooth hd.isEven hd.supportRadius
    hd.lambdaNonneg t r
  have hgam := hCG hd.smooth hd.isEven hd.supportRadius hd.lambdaNonneg t r
  have hpole := abs_poleProjectiveDefect_le' hd.smooth.continuous hd.compactSupport hd.isEven
    hd.supportRadius t r
  have hsum := clusterHeightDefect_eq_threeProjectiveChannels hd.smooth hd.compactSupport
    hd.isEven hd.short t r
  have htri : |clusterHeightDefect g t r|
      ≤ |offOrdProjectiveDefect g t r| + |gammaProjectiveDefect g t r|
        + |poleProjectiveDefect g t r| := by
    rw [hsum]
    have h1 := abs_add_le (offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r)
      (poleProjectiveDefect g t r)
    have h2 := abs_add_le (offOrdProjectiveDefect g t r) (gammaProjectiveDefect g t r)
    linarith
  have hpole' : |poleProjectiveDefect g t r|
      ≤ r ^ 2 * (20 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2) := by
    nlinarith [hpole]
  unfold projectiveEnvelope
  nlinarith [htri, hoff, hgam, hpole']

/-! ## The gate -/

/-- **`false_of_projectiveEnvelope_lt_targetDefect`.**  The contradiction criterion in
projective form: for admissible gate data the quadratic projective envelope can never
be strictly below the target-local defect of a zero of the fibre. -/
theorem false_of_projectiveEnvelope_lt_targetDefect {g : ℝ → ℝ} {t r Λ CG : ℝ}
    (hd : GateData g t r Λ)
    (henv : |clusterHeightDefect g t r| ≤ r ^ 2 * projectiveEnvelope g Λ t CG)
    (ρ₀ : SameOrd t)
    (hsep : r ^ 2 * projectiveEnvelope g Λ t CG < zeroHeightDefect g r (ρ₀ : Zeros)) :
    False := by
  have hlo := zeroHeightDefect_le_clusterHeightDefect hd ρ₀
  have habs := le_abs_self (clusterHeightDefect g t r)
  linarith

/-- **The projective sandwich for an off-line target zero:**

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ r² · E_proj(g, Λ, t).

The right-hand side is quadratically small in the sampling radius. -/
theorem projectiveSandwich {g : ℝ → ℝ} {t r Λ CG : ℝ} (hd : GateData g t r Λ)
    (henv : |clusterHeightDefect g t r| ≤ r ^ 2 * projectiveEnvelope g Λ t CG)
    (ρ₀ : SameOrd t) (hρ₀ : heightOf (ρ₀ : Zeros) ≠ 0) :
    0 < zeroHeightDefect g r (ρ₀ : Zeros)
      ∧ zeroHeightDefect g r (ρ₀ : Zeros) ≤ clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r ≤ r ^ 2 * projectiveEnvelope g Λ t CG :=
  ⟨zeroHeightDefect_pos_of_offLine hd hρ₀, zeroHeightDefect_le_clusterHeightDefect hd ρ₀,
    le_trans (le_abs_self _) henv⟩

/-- **`no_offLineZero_of_projectiveEnvelope_lt_targetDefect`.**  The kill switch in the
form it would be used.  `hgate` is the single open quantitative inequality; it is a
hypothesis here, not an assertion. -/
theorem no_offLineZero_of_projectiveEnvelope_lt_targetDefect {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2)
    (hgate : ∀ (g : ℝ → ℝ) (r Λ CG : ℝ), GateData g t r Λ →
      |clusterHeightDefect g t r| ≤ r ^ 2 * projectiveEnvelope g Λ t CG →
      heightOf ρstar ≠ 0 →
      r ^ 2 * projectiveEnvelope g Λ t CG < zeroHeightDefect g r ρstar) :
    heightOf ρstar = 0 := by
  by_contra hoff
  obtain ⟨CG, -, hCG⟩ := exists_projectiveEnvelope
  obtain ⟨g, r, hd⟩ := exists_gateData ht hheight
  exact false_of_projectiveEnvelope_lt_targetDefect hd (hCG hd) ⟨ρstar, him⟩
    (hgate g r (9 * π / (4 * |t|)) CG hd (hCG hd) hoff)

/-! ## The capstone -/

/-- **`targetZeroDefect_le_projectiveEnvelope`.**  For an actual off-line nontrivial
zero of `riemannZeta` at a nonzero ordinate high enough that the literal prime
frequencies miss the taper support, there is an explicit taper for which

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ r² · E_proj(g, Λ, t),

with the prime channel absent at both sampling radii and *all three* remaining
channels — off-ordinate zeros, gamma and pole — bounded at determinant level, so
that the whole residual side is quadratically small in the sampling radius. -/
theorem targetZeroDefect_le_projectiveEnvelope {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (hoffline : heightOf ρstar ≠ 0) (ht : t ≠ 0)
    (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r Λ CG : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ) ∧ 0 ≤ CG
      ∧ evenConeFunctional (primeVec (sampleFam g t r)) = 0
      ∧ evenConeFunctional (primeVec (sampleFam g t (2 * r))) = 0
      ∧ primeProjectiveDefect g t r = 0
      ∧ clusterHeightDefect g t r
          = offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r
            + poleProjectiveDefect g t r
      ∧ 0 < zeroHeightDefect g r ρstar
      ∧ zeroHeightDefect g r ρstar ≤ clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r ≤ r ^ 2 * projectiveEnvelope g Λ t CG := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_projectiveEnvelope
  obtain ⟨g, r, hd⟩ := exists_gateData ht hheight
  obtain ⟨hpos, hlo, hhi⟩ := projectiveSandwich hd (hCG hd) ⟨ρstar, him⟩ hoffline
  exact ⟨g, r, 9 * π / (4 * |t|), CG, hd.smooth, hd.compactSupport, hd.isEven, hd.radiusPos,
    hd.lambdaNonneg, hd.supportRadius, hCG0,
    primeConeValue_eq_zero_of_short_taper hd.short t r,
    primeConeValue_eq_zero_of_short_taper hd.short t (2 * r),
    primeProjectiveDefect_eq_zero hd.short t r,
    clusterHeightDefect_eq_threeProjectiveChannels hd.smooth hd.compactSupport hd.isEven
      hd.short t r,
    hpos, hlo, hhi⟩

end LiteralWeilProjectiveSeparationGate
end Zeta23Bridge
