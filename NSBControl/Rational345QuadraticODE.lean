import Mathlib.Tactic.Omega
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Comp
import NSBControl.Rational345LocalODE

/-!
# R830 quadratic-vector-field max-cut

Round71 already constructs the autonomous finite Galerkin vector field. Its
remaining standard analytic obligation is to exhibit the real-coordinate field
as linear plus bilinear (hence degree at most two). Mathlib's bounded-linear and
bounded-bilinear calculus then makes the field C¹ automatically, and the
Picard--Lindelöf owner supplies a local integral curve.

Thus the Navier--Stokes-specific residue after this file is only the concrete
coordinate identification and the explicit R828 bootstrap constants.
-/

namespace NSBControl
namespace Rational345QuadraticODE

/-- A linear plus bounded-bilinear diagonal field is C¹. -/
theorem contDiff_quadraticField
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear) :
    ContDiff ℝ 1 (fun x : E => linear x + bilinear (x, x)) := by
  have hdiag : ContDiff ℝ 1 (fun x : E => (x, x)) :=
    contDiff_id.prodMk contDiff_id
  have hquad : ContDiff ℝ 1 (fun x : E => bilinear (x, x)) :=
    hbilinear.contDiff.comp hdiag
  exact linear.contDiff.add hquad

/-- Local real-time solution for every linear+quadratic finite-dimensional
Galerkin template. -/
theorem exists_local_solution_quadraticField
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear)
    (u₀ : E) :
    ∃ (u : ℝ → E),
      u 0 = u₀ ∧
      ∃ ε > 0,
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt u (linear (u t) + bilinear (u t, u t)) t := by
  apply Rational345LocalODE.exists_local_solution
  exact (contDiff_quadraticField linear bilinear hbilinear).contDiffAt

end Rational345QuadraticODE
end NSBControl


namespace NSBControl
namespace Rational345QuadraticODE

/-!
## The eight-mode invariant physical Fourier support

At cutoff |k_i| ≤ 4, the six initial 3-4-5 modes generate only the
eight nonzero modes in {−3,0,3} × {−4,0,4} × {0} under p+q.
Every other pair sum is either k=0 (projected mean removed) or
outside the cutoff. This matters: a solution starting in this support
cannot excite a mode whose helical |k| contains an irrational root.
The finite interaction theorem below pays the *actual support algebra*,
not a new ODE existence premise.
-/

abbrev Mode345 := Fin 3 → ℤ

def Selected345Mode (k : Mode345) : Prop :=
  (k 0 = -3 ∨ k 0 = 0 ∨ k 0 = 3) ∧
  (k 1 = -4 ∨ k 1 = 0 ∨ k 1 = 4) ∧
  k 2 = 0 ∧ k ≠ 0

def InRadiusFour (k : Mode345) : Prop :=
  (∀ i : Fin 3, -4 ≤ k i ∧ k i ≤ 4) ∧ k ≠ 0

theorem selected345_add_closed_inside_cutoff
    {p q k : Mode345}
    (hp : Selected345Mode p)
    (hq : Selected345Mode q)
    (hadd : p + q = k)
    (hk : InRadiusFour k) :
    Selected345Mode k := by
  rcases hp with ⟨hpx,hpy,hpz,_⟩
  rcases hq with ⟨hqx,hqy,hqz,_⟩
  rcases hk with ⟨hwindow,hknonzero⟩
  have hx : p 0 + q 0 = k 0 :=
    congrArg (fun v : Mode345 => v 0) hadd
  have hy : p 1 + q 1 = k 1 :=
    congrArg (fun v : Mode345 => v 1) hadd
  have hz : p 2 + q 2 = k 2 :=
    congrArg (fun v : Mode345 => v 2) hadd
  simp only [Pi.add_apply] at hx hy hz
  refine ⟨?_, ?_, ?_, hknonzero⟩
  · have hw := hwindow 0
    rcases hpx with hpx | hpx | hpx <;>
      rcases hqx with hqx | hqx | hqx <;> omega
  · have hw := hwindow 1
    rcases hpy with hpy | hpy | hpy <;>
      rcases hqy with hqy | hqy | hqy <;> omega
  · omega

/-- Genuine finite projected Galerkin quadratic interactions do not create
    an off-support nonzero radius-four output from two supported inputs. -/
theorem inactive_output_has_no_selected345_pairs
    {p q k : Mode345}
    (hp : Selected345Mode p) (hq : Selected345Mode q)
    (hk : InRadiusFour k) (hnot : ¬ Selected345Mode k) :
    p + q ≠ k := by
  intro hsum
  exact hnot (selected345_add_closed_inside_cutoff hp hq hsum hk)

/-- Exact finite-sum version: the projected nonlinear quadratic forcing
    vanishes at any inactive nonzero output for supported velocity data,
    BEFORE applying its linear Leray projector. -/
theorem inactive_real_fourier_quadratic_sum_zero
    {R : Type*} [AddCommMonoid R]
    (pairs : Finset (Mode345 × Mode345))
    (term : Mode345 × Mode345 → R)
    (k : Mode345)
    (hk : InRadiusFour k)
    (hinactive : ¬ Selected345Mode k) :
    pairs.sum (fun pq =>
      if Selected345Mode pq.1 ∧ Selected345Mode pq.2 ∧ pq.1 + pq.2 = k
      then term pq else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro pq hpq
  have hnone :
      ¬ (Selected345Mode pq.1 ∧ Selected345Mode pq.2 ∧
          pq.1 + pq.2 = k) := by
    rintro ⟨hp, hq, hsum⟩
    exact hinactive (selected345_add_closed_inside_cutoff hp hq hsum hk)
  simp [hnone]

end Rational345QuadraticODE
end NSBControl
