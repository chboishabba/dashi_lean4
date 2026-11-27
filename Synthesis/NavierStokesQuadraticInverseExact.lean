import Synthesis.NavierStokesSignedGeometryWeld
import Mathlib.Topology.MetricSpace.Contracting

/-! Classical Banach contraction / quadratic Newton correction.
The actual PDE inverse and weighted bilinear estimates are explicit
hypotheses. The conclusion is an inhabited nonzero root, not an interface
requiring an assumed solution. -/
namespace Synthesis
open Set Metric
noncomputable section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem nsQuadraticCorrectionRoot
    (u : X) (F : X → Y) (A : Y →L[ℝ] X)
    (B : X →L[ℝ] X →L[ℝ] X) (r : ℝ) (k : ℝ≥0)
    (hr : 0 ≤ r) (hk : k < 1)
    (hnz : r < ‖u‖)
    (hinj : Function.Injective A)
    (hexpand : ∀ h : X, A (F (u+h)) = A (F u) + h + B h h)
    (hsize : ‖A (F u)‖ + ‖B‖ * r * r ≤ r)
    (hcontract : 2 * ‖B‖ * r ≤ (k : ℝ)) :
    ∃ v : X, v ≠ 0 ∧ F v = 0 ∧ ‖v-u‖ ≤ r := by
  let T : X → X := fun h => - A (F u) - B h h
  let S : Set X := closedBall 0 r
  have hzero : (0 : X) ∈ S := by simpa [S, Metric.mem_closedBall] using hr
  have hmaps : MapsTo T S S := by
    intro h hh
    have hnorm : ‖h‖ ≤ r := by simpa [S, Metric.mem_closedBall, dist_eq_norm] using hh
    have hb : ‖B h h‖ ≤ ‖B‖ * r * r := by
      calc
        ‖B h h‖ ≤ ‖B h‖ * ‖h‖ := (B h).le_opNorm h
        _ ≤ (‖B‖ * ‖h‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (B.le_opNorm h) (norm_nonneg h)
        _ ≤ ‖B‖ * r * r := by gcongr
    have ht : ‖T h‖ ≤ r := by
      calc
        ‖T h‖ ≤ ‖-A (F u)‖ + ‖B h h‖ := norm_sub_le _ _
        _ ≤ r := by rw [norm_neg]; linarith
    simpa [S, Metric.mem_closedBall, dist_eq_norm] using ht
  have hc : ContractingWith k (hmaps.restrict T S S) := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hx : ‖(x : X)‖ ≤ r := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using x.property
    have hy : ‖(y : X)‖ ≤ r := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using y.property
    change dist (T (x : X)) (T (y : X)) ≤ (k : ℝ) * dist (x : X) (y : X)
    rw [dist_eq_norm, dist_eq_norm]
    have he : T (x : X) - T (y : X) =
        -(B ((x : X)-(y : X)) (x : X) + B (y : X) ((x : X)-(y : X))) := by
      simp only [T, map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [he, norm_neg]
    have h1 : ‖B ((x : X)-(y : X)) (x : X)‖ ≤
        ‖B‖ * ‖(x : X)-(y : X)‖ * r := by
      calc
        _ ≤ ‖B ((x : X)-(y : X))‖ * ‖(x : X)‖ := (B _).le_opNorm _
        _ ≤ (‖B‖ * ‖(x : X)-(y : X)‖) * ‖(x : X)‖ :=
          mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
        _ ≤ _ := by gcongr
    have h2 : ‖B (y : X) ((x : X)-(y : X))‖ ≤
        ‖B‖ * r * ‖(x : X)-(y : X)‖ := by
      calc
        _ ≤ ‖B (y : X)‖ * ‖(x : X)-(y : X)‖ := (B _).le_opNorm _
        _ ≤ (‖B‖ * ‖(y : X)‖) * ‖(x : X)-(y : X)‖ :=
          mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
        _ ≤ _ := by gcongr
    calc
      _ ≤ ‖B ((x : X)-(y : X)) (x : X)‖ +
          ‖B (y : X) ((x : X)-(y : X))‖ := norm_add_le _ _
      _ ≤ (2 * ‖B‖ * r) * ‖(x : X)-(y : X)‖ := by
        nlinarith only [h1, h2]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcontract (norm_nonneg _)
  have hcomplete : IsComplete S := isClosed_closedBall.isComplete
  obtain ⟨h, hh, hfix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' hcomplete hmaps hc hzero (edist_ne_top _ _)
  have hnorm : ‖h‖ ≤ r := by simpa [S, Metric.mem_closedBall, dist_eq_norm] using hh
  have hfix' : T h = h := hfix
  have hres : A (F (u+h)) = 0 := by
    rw [hexpand]
    have he : h = - A (F u) - B h h := hfix'.symm
    calc
      A (F u) + h + B h h = h - (- A (F u) - B h h) := by abel
      _ = 0 := sub_eq_zero.mpr he
  refine ⟨u+h, ?_, hinj (by simpa using hres), ?_⟩
  · intro hz
    have he : h = -u := by
      calc
        h = -u + (u+h) := by abel
        _ = -u := by rw [hz, add_zero]
    rw [he, norm_neg] at hnorm
    exact (not_le_of_gt hnz) hnorm
  · simpa only [add_sub_cancel_left] using hnorm

end
end Synthesis
