/-
# The two-radius separation gate

`LiteralWeilTwoRadiusResidualEnvelope` bounded the literal cluster height defect
from above by an explicit residual envelope,

    0 < D_cluster(t, r) ≤ E_residual(t, r)
      = ε(2r) |A₀(r)| + ε(r) |A₀(2r)|,
    ε(s) = ε_zero(g, Λ, t, s) + ε_Γ(g, t, s) + 4 |P_t(s)|,

and `LiteralWeilClusterTwoRadiusProfile.clusterHeightDefect_ge_zeroHeightDefect`
bounded it from below by the *target-local* defect of a single zero of the fibre,

    D_{ρ*}(r) = 2 m_{ρ*} D(a_{ρ*}, 0; r).

This module puts the two together into the **sandwich**

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ E_residual(t, r),

and reads off the resulting **contradiction criterion**: a *single explicit
inequality* between two completely explicit finite expressions,

    E_residual(t, r) < D_{ρ*}(r)   ⟹   ⊥.

Two further simplifications are made explicit.

* **Reduced envelope.**  The taper produced by `exists_positive_taper_poleEven_zero`
  kills the pole channel at the *base* radius, `P_t(r) = 0`, so `ε(r)` loses its
  pole penalty entirely and only the doubled radius retains `4 |P_t(2r)|`:

      E_red(t, r) = [ε_zero(2r) + ε_Γ(2r) + 4|P_t(2r)|] |A₀(r)|
                  + [ε_zero(r)  + ε_Γ(r)]              |A₀(2r)|.

  `reducedEnvelope_eq_residualEnvelope` proves `E_red = E_residual` under `P_t(r) = 0`,
  so `E_red` — and not `epsResidual` at both radii — is the canonical frontier
  quantity.

* **No prime channel.**  `abs_residualCone_le` applies
  `primeConeValue_eq_zero_of_short_taper` at an *arbitrary* sampling radius, so in
  this short-taper/high-ordinate regime the literal von Mangoldt channel vanishes at
  **both** sampling radii.  There is no prime-side estimate left here; the residual
  obstruction is exactly *off-ordinate zeros + Γ + the doubled-radius pole*.

**Nothing here asserts the gate inequality.**  `E_residual < D_{ρ*}` remains open;
what is proved is that it is the one quantitative inequality that would refute an
off-line zero in this regime.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTwoRadiusSeparationGate

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope

/-! ## The admissible data of the gate -/

/-- The standing hypotheses shared by every statement of this module: a nonnegative,
even, twice continuously differentiable, compactly supported taper `g` whose support
radius is at most `Λ`, radially admissible for the doubled radius `2r`, short enough
that the literal prime frequencies miss it, and killing the even pole response at the
base radius. -/
structure GateData (g : ℝ → ℝ) (t r Λ : ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  compactSupport : HasCompactSupport g
  isEven : ∀ u, g (-u) = g u
  nonneg : ∀ u, 0 ≤ g u
  radiusPos : 0 < r
  radial : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2
  supportRadius : ∀ u, g u ≠ 0 → |u| ≤ Λ
  lambdaNonneg : 0 ≤ Λ
  short : ∀ u, g u ≠ 0 → |u| < Real.log 2
  poleKilled : poleEvenResp g t r = 0
  twoPoint : ∃ u v : ℝ, 0 < g u ∧ 0 < g v ∧ |u| ≠ |v|

/-- **`exists_gateData`.**  For every nonzero ordinate high enough that the literal
prime frequencies fall outside the taper support, admissible gate data exist, with the
*explicit* support radius `Λ = 9π/(4|t|)` of the high-ordinate taper. -/
theorem exists_gateData {t : ℝ} (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r : ℝ), GateData g t r (9 * π / (4 * |t|)) := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hrad, htwo, hpole, -, hsupp9⟩ :=
    exists_positive_taper_poleEven_zero ht
  have habs : 0 < |t| := abs_pos.mpr ht
  have hpi := Real.pi_pos
  refine ⟨g, r, ⟨hgs, hgc, heven, hnn, hr, hrad, fun u hu => (hsupp9 u hu).le,
    by positivity, short_taper_of_height hsupp9 ht hheight, hpole, htwo⟩⟩

/-! ## The two envelopes -/

/-- The residual envelope `E_residual(t, r) = ε(2r)|A₀(r)| + ε(r)|A₀(2r)|`. -/
def residualEnvelope (g : ℝ → ℝ) (Λ t r : ℝ) : ℝ :=
  epsResidual g Λ t (2 * r) * |evenResp g 0 r| + epsResidual g Λ t r * |evenResp g 0 (2 * r)|

/-- The **reduced** two-radius envelope: the pole penalty appears only at the doubled
radius, because the taper kills the even pole response at the base radius. -/
def reducedEnvelope (g : ℝ → ℝ) (Λ t r : ℝ) : ℝ :=
  (epsZero g Λ t (2 * r) + epsGamma g t (2 * r) + 4 * |poleEvenResp g t (2 * r)|)
      * |evenResp g 0 r|
    + (epsZero g Λ t r + epsGamma g t r) * |evenResp g 0 (2 * r)|

/-- **`reducedEnvelope_eq_residualEnvelope`.**  At the base radius the taper kills the
pole channel, `P_t(r) = 0`, so `ε(r) = ε_zero(r) + ε_Γ(r)` and the two envelopes
agree.  Only the doubled radius carries `4|P_t(2r)|`. -/
theorem reducedEnvelope_eq_residualEnvelope {g : ℝ → ℝ} {Λ t r : ℝ}
    (hpole : poleEvenResp g t r = 0) :
    reducedEnvelope g Λ t r = residualEnvelope g Λ t r := by
  unfold reducedEnvelope residualEnvelope epsResidual
  rw [hpole]
  simp

theorem epsGamma_nonneg (g : ℝ → ℝ) (t s : ℝ) : 0 ≤ epsGamma g t s := by
  have h1 : (0 : ℝ) ≤ ∫ x : ℝ, |gammaIntegrand g t s x| :=
    MeasureTheory.integral_nonneg fun _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ x : ℝ, |gammaIntegrand g t (-s) x| :=
    MeasureTheory.integral_nonneg fun _ => abs_nonneg _
  have hpi := Real.pi_pos
  unfold epsGamma
  positivity

theorem reducedEnvelope_nonneg {g : ℝ → ℝ} {Λ t r : ℝ} :
    0 ≤ reducedEnvelope g Λ t r := by
  have h1 := epsZero_nonneg g Λ t (2 * r)
  have h2 := epsZero_nonneg g Λ t r
  have h3 := epsGamma_nonneg g t (2 * r)
  have h4 := epsGamma_nonneg g t r
  unfold reducedEnvelope
  have := abs_nonneg (poleEvenResp g t (2 * r))
  have := abs_nonneg (evenResp g 0 r)
  have := abs_nonneg (evenResp g 0 (2 * r))
  nlinarith [abs_nonneg (evenResp g 0 r), abs_nonneg (evenResp g 0 (2 * r)),
    abs_nonneg (poleEvenResp g t (2 * r))]

/-! ## The sandwich -/

/-- **Upper side.**  The cluster height defect is at most the reduced envelope. -/
theorem clusterHeightDefect_le_reducedEnvelope {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) :
    clusterHeightDefect g t r ≤ reducedEnvelope g Λ t r := by
  have hbal := twoRadiusResidualBalance hd.smooth hd.compactSupport hd.isEven t r
  have henv := twoRadiusResidualEnvelope hd.smooth hd.compactSupport hd.isEven
    hd.supportRadius hd.lambdaNonneg hd.short t r
  have hle := (abs_le.mp henv).2
  rw [reducedEnvelope_eq_residualEnvelope hd.poleKilled, residualEnvelope, hbal]
  linarith

/-- **Lower side.**  The cluster height defect is at least the target-local defect of
any single zero of the fibre. -/
theorem zeroHeightDefect_le_clusterHeightDefect {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) (ρ₀ : SameOrd t) :
    zeroHeightDefect g r (ρ₀ : Zeros) ≤ clusterHeightDefect g t r :=
  clusterHeightDefect_ge_zeroHeightDefect hd.smooth hd.compactSupport hd.isEven hd.nonneg
    hd.radiusPos hd.radial ρ₀

/-- **`targetZeroDefect_le_reducedEnvelope`.**  The composition of the two sides: the
target-local defect is bounded by the reduced envelope.  Pure composition — no new
analysis. -/
theorem targetZeroDefect_le_reducedEnvelope {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) (ρ₀ : SameOrd t) :
    zeroHeightDefect g r (ρ₀ : Zeros) ≤ reducedEnvelope g Λ t r :=
  le_trans (zeroHeightDefect_le_clusterHeightDefect hd ρ₀)
    (clusterHeightDefect_le_reducedEnvelope hd)

/-- The strict positivity of the target-local defect for an off-line zero. -/
theorem zeroHeightDefect_pos_of_offLine {g : ℝ → ℝ} {t r Λ : ℝ} (hd : GateData g t r Λ)
    {ρ₀ : Zeros} (hρ₀ : heightOf ρ₀ ≠ 0) : 0 < zeroHeightDefect g r ρ₀ := by
  obtain ⟨u₀, v₀, hu₀, hv₀, hne⟩ := hd.twoPoint
  exact zeroHeightDefect_pos hd.smooth.continuous hd.compactSupport hd.nonneg hd.radiusPos
    hd.radial hu₀ hv₀ hne hρ₀

/-- **The full sandwich for an off-line target zero:**

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ E_red(t, r). -/
theorem targetZeroDefect_sandwich {g : ℝ → ℝ} {t r Λ : ℝ} (hd : GateData g t r Λ)
    (ρ₀ : SameOrd t) (hρ₀ : heightOf (ρ₀ : Zeros) ≠ 0) :
    0 < zeroHeightDefect g r (ρ₀ : Zeros)
      ∧ zeroHeightDefect g r (ρ₀ : Zeros) ≤ clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r ≤ reducedEnvelope g Λ t r :=
  ⟨zeroHeightDefect_pos_of_offLine hd hρ₀, zeroHeightDefect_le_clusterHeightDefect hd ρ₀,
    clusterHeightDefect_le_reducedEnvelope hd⟩

/-! ## The kill switch -/

/-- **`false_of_reducedEnvelope_lt_targetDefect`.**  The contradiction criterion: for
admissible gate data, the reduced envelope can never be strictly below the
target-local defect of a zero of the fibre.  Contrapositively, *proving* that strict
inequality for some admissible taper would refute the existence of the zero it is
stated for. -/
theorem false_of_reducedEnvelope_lt_targetDefect {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) (ρ₀ : SameOrd t)
    (hsep : reducedEnvelope g Λ t r < zeroHeightDefect g r (ρ₀ : Zeros)) : False := by
  have hlo := zeroHeightDefect_le_clusterHeightDefect hd ρ₀
  have hhi := clusterHeightDefect_le_reducedEnvelope hd
  linarith

/-- **`no_offLineZero_of_reducedEnvelope_lt_targetDefect`.**  The kill switch in the
form it would be used: if the gate inequality

    E_red(t, r) < D_{ρ*}(r)

can be established for the admissible taper attached to the ordinate `t`, then the
zero `ρ*` lies on the critical line.

`hgate` is the single open quantitative inequality; it is a hypothesis here, not an
assertion. -/
theorem no_offLineZero_of_reducedEnvelope_lt_targetDefect {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2)
    (hgate : ∀ (g : ℝ → ℝ) (r Λ : ℝ), GateData g t r Λ → heightOf ρstar ≠ 0 →
      reducedEnvelope g Λ t r < zeroHeightDefect g r ρstar) :
    heightOf ρstar = 0 := by
  by_contra hoff
  obtain ⟨g, r, hd⟩ := exists_gateData ht hheight
  exact false_of_reducedEnvelope_lt_targetDefect hd ⟨ρstar, him⟩
    (hgate g r (9 * π / (4 * |t|)) hd hoff)

/-! ## The capstone in explicit form -/

/-- **`targetZeroDefect_le_residualEnvelope`.**  For an actual off-line nontrivial zero
of `riemannZeta` at a nonzero ordinate high enough that the literal prime frequencies
miss the taper support, there is an explicit taper for which

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ E_red(t, r) = E_residual(t, r),

with the prime channel absent at both sampling radii and the pole channel absent at
the base radius.  Everything on the right is an explicit finite expression. -/
theorem targetZeroDefect_le_residualEnvelope {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (hoffline : heightOf ρstar ≠ 0) (ht : t ≠ 0)
    (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ)
      ∧ poleEvenResp g t r = 0
      ∧ evenConeFunctional (primeVec (sampleFam g t r)) = 0
      ∧ evenConeFunctional (primeVec (sampleFam g t (2 * r))) = 0
      ∧ 0 < zeroHeightDefect g r ρstar
      ∧ zeroHeightDefect g r ρstar ≤ clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r ≤ reducedEnvelope g Λ t r
      ∧ reducedEnvelope g Λ t r = residualEnvelope g Λ t r := by
  obtain ⟨g, r, hd⟩ := exists_gateData ht hheight
  obtain ⟨hpos, hlo, hhi⟩ := targetZeroDefect_sandwich hd ⟨ρstar, him⟩ hoffline
  exact ⟨g, r, 9 * π / (4 * |t|), hd.smooth, hd.compactSupport, hd.isEven, hd.radiusPos, hd.lambdaNonneg,
    hd.supportRadius, hd.poleKilled,
    primeConeValue_eq_zero_of_short_taper hd.short t r,
    primeConeValue_eq_zero_of_short_taper hd.short t (2 * r),
    hpos, hlo, hhi, reducedEnvelope_eq_residualEnvelope hd.poleKilled⟩

end LiteralWeilTwoRadiusSeparationGate
end Zeta23Bridge
