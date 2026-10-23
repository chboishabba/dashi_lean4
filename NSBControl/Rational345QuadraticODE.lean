import Mathlib
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


namespace NSBControl
namespace Rational345QuadraticODE

/-- Every nonzero mode of the selected invariant eight-mode subsystem has
    squared physical Euclidean norm 9, 16 or 25. Hence all normalized
    helical projectors *on that subsystem* have exact rational 3-4-5
    denominators. This does not claim anything about all cutoff modes. -/
theorem selected345_physical_squared_norm
    {k : Mode345} (hk : Selected345Mode k) :
    (k 0)^2 + (k 1)^2 + (k 2)^2 = 9 ∨
    (k 0)^2 + (k 1)^2 + (k 2)^2 = 16 ∨
    (k 0)^2 + (k 1)^2 + (k 2)^2 = 25 := by
  rcases hk with ⟨hx, hy, hz, hnonzero⟩
  have hxy : k 0 ≠ 0 ∨ k 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hnonzero
    funext i
    fin_cases i <;> simp [h.1, h.2, hz]
  rcases hx with hx | hx | hx <;>
    rcases hy with hy | hy | hy <;>
      simp_all [pow_two] <;> omega

end Rational345QuadraticODE
end NSBControl


namespace NSBControl
namespace Rational345QuadraticODE

/-!
## Literal complex-vector finite Fourier right-hand side

Unlike the earlier term-filtering statement, these are the actual algebraic
operators of the physical projected quadratic Galerkin RHS (viscosity ν=1).
They work on arbitrary complex 3-vector mode coefficients, not only on
the specially chosen initial seed. Finite sums use the full supplied mode
set. No helical-mode defaults or irrational square roots enter the RHS.
-/

abbrev FourierVector345 := Fin 3 → ℂ

/-- Sum over q dotted into the velocity at p, multiplied by velocity at q. -/
def rawFourierTriad345 (q : Mode345)
    (atP atQ : FourierVector345) : FourierVector345 :=
  fun j => (∑ i : Fin 3, (q i : ℂ) * atP i) * atQ j

/-- Literal positive-viscosity ν=1 Fourier Laplacian multiplier. -/
def viscousFourierMode345 (k : Mode345)
    (v : FourierVector345) : FourierVector345 :=
  fun j => -(∑ i : Fin 3, (k i : ℂ) * (k i : ℂ)) * v j

/-- Leray projection followed by the physical factor -i. -/
def projectedNonlinearMode345 (k : Mode345)
    (v : FourierVector345) : FourierVector345 :=
  fun j => -Complex.I * (v j -
    (k j : ℂ) * (∑ i : Fin 3, (k i : ℂ) * v i) /
      (∑ i : Fin 3, (k i : ℂ) * (k i : ℂ)))

/-- Truncated, same-source physical Fourier right-hand side:
    F_k(u) = -|k|² u_k - i P_k Σ_(p+q=k) (q · u_p)u_q. -/
def literalProjectedGalerkinRHS345
    (modes : Finset Mode345)
    (u : Mode345 → FourierVector345)
    (k : Mode345) : FourierVector345 :=
  viscousFourierMode345 k (u k) +
    projectedNonlinearMode345 k
      ((modes.product modes).sum (fun pq =>
        if pq.1 + pq.2 = k then
          rawFourierTriad345 pq.2 (u pq.1) (u pq.2)
        else 0))

theorem rawFourierTriad345_zero_left (q : Mode345)
    (v : FourierVector345) :
    rawFourierTriad345 q 0 v = 0 := by
  funext j
  simp [rawFourierTriad345]

theorem rawFourierTriad345_zero_right (q : Mode345)
    (v : FourierVector345) :
    rawFourierTriad345 q v 0 = 0 := by
  funext j
  simp [rawFourierTriad345]

theorem viscousFourierMode345_zero (k : Mode345) :
    viscousFourierMode345 k 0 = 0 := by
  funext j
  simp [viscousFourierMode345]

theorem projectedNonlinearMode345_zero (k : Mode345) :
    projectedNonlinearMode345 k 0 = 0 := by
  funext j
  simp [projectedNonlinearMode345]

/-- Literal radius-four physical RHS preserves the selected eight-mode
    support. It uses the REAL Leray coefficient via a complex cast, both
    velocity factors and the full ungated pair sum, not an artificial
    active-support-filtered interaction. -/
theorem literalProjectedGalerkinRHS345_preserves_selected_support
    (modes : Finset Mode345)
    (u : Mode345 → FourierVector345)
    (hu : ∀ p, ¬ Selected345Mode p → u p = 0)
    (k : Mode345)
    (hk : InRadiusFour k)
    (hinactive : ¬ Selected345Mode k) :
    literalProjectedGalerkinRHS345 modes u k = 0 := by
  have hsum :
      (modes.product modes).sum (fun pq =>
        if pq.1 + pq.2 = k then
          rawFourierTriad345 pq.2 (u pq.1) (u pq.2)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro pq hpq
    by_cases heq : pq.1 + pq.2 = k
    · by_cases hp : Selected345Mode pq.1
      · by_cases hq : Selected345Mode pq.2
        · exact False.elim
            (hinactive (selected345_add_closed_inside_cutoff hp hq heq hk))
        · simp [heq, hu pq.2 hq, rawFourierTriad345_zero_right]
      · simp [heq, hu pq.1 hp, rawFourierTriad345_zero_left]
    · simp [heq]
  simp only [literalProjectedGalerkinRHS345, hu k hinactive, hsum,
    viscousFourierMode345_zero, projectedNonlinearMode345_zero, add_zero]

end Rational345QuadraticODE
end NSBControl


namespace NSBControl
namespace Rational345QuadraticODE

/-!
## Actual eight-mode chart of the literal physical Fourier field
The chart is Fin 8 -> (Fin 3 -> Complex), hence a genuine finite
real vector space. It embeds as a sparse 728-mode coefficient field.
No "RNNN" re-encoding of the analytic problem is introduced.
-/

abbrev PhysicalEightModeState := Fin 8 → FourierVector345

/-- Ordered exactly as the R829/R850 eight coherent-work outputs. -/
def selected345ModeAt (j : Fin 8) : Mode345 :=
  let x : ℤ := if j.val < 3 then -3 else if j.val < 5 then 0 else 3
  let y : ℤ :=
    if j.val = 0 ∨ j.val = 3 ∨ j.val = 5 then -4
    else if j.val = 1 ∨ j.val = 6 then 0 else 4
  ![x, y, 0]

def selected345ModeFinset : Finset Mode345 :=
  Finset.univ.image selected345ModeAt

/-- Sparse extension to actual (infinitely indexed, finitely supported)
    physical Fourier modes. Its nonzero support lies in the eight selected
    physical modes, independently of amplitudes and polarization. -/
def extendPhysicalEight
    (u : PhysicalEightModeState) (k : Mode345) : FourierVector345 :=
  ∑ j : Fin 8, if selected345ModeAt j = k then u j else 0

/-- The actual projected viscosity + convection field restricted to the
    invariant eight-mode chart, using the SAME literal RHS definition. -/
def physicalEightModeField (u : PhysicalEightModeState) :
    PhysicalEightModeState :=
  fun j =>
    literalProjectedGalerkinRHS345 selected345ModeFinset
      (extendPhysicalEight u) (selected345ModeAt j)

/-- Every one of the eight chart modes is a member of S. -/
theorem selected345ModeAt_mem (j : Fin 8) :
    Selected345Mode (selected345ModeAt j) := by
  fin_cases j <;> decide

/-- The sparse extension is zero on every nonselected physical output. -/
theorem extendPhysicalEight_off_support
    (u : PhysicalEightModeState)
    (k : Mode345)
    (hk : ¬ Selected345Mode k) :
    extendPhysicalEight u k = 0 := by
  unfold extendPhysicalEight
  apply Finset.sum_eq_zero
  intro j hj
  have hneq : selected345ModeAt j ≠ k := by
    intro h
    exact hk (h ▸ selected345ModeAt_mem j)
  simp [hneq]

/-- At EVERY admissible radius-four off-support Fourier output, the
    literal physical Galerkin RHS of the extended eight-mode field is zero.
    This is the explicit source-level invariant-subspace certificate. -/
theorem physicalEightModeField_off_support
    (u : PhysicalEightModeState)
    (k : Mode345)
    (hk : InRadiusFour k)
    (hnot : ¬ Selected345Mode k) :
    literalProjectedGalerkinRHS345 selected345ModeFinset
      (extendPhysicalEight u) k = 0 := by
  exact literalProjectedGalerkinRHS345_preserves_selected_support
    selected345ModeFinset (extendPhysicalEight u)
    (fun p hp => extendPhysicalEight_off_support u p hp)
    k hk hnot

end Rational345QuadraticODE
end NSBControl


namespace NSBControl
namespace Rational345QuadraticODE

/-!
## Real physical eight-mode Galerkin flow

The concrete field defined above is the literal viscosity-one,
Leray-projected quadratic finite Fourier field restricted to the eight
closed modes. Every sum is finite and every projector denominator
is independent of the state. It is therefore real C1 and has a
genuine local real-time trajectory through each finite state.
-/

theorem physicalEightModeField_contDiff :
    ContDiff ℝ 1 physicalEightModeField := by
  unfold physicalEightModeField literalProjectedGalerkinRHS345
    extendPhysicalEight viscousFourierMode345
    projectedNonlinearMode345 rawFourierTriad345
  fun_prop

theorem physicalEightModeField_real_local_solution
    (seed : PhysicalEightModeState) :
    ∃ (u : ℝ → PhysicalEightModeState),
      u 0 = seed ∧
      ∃ ε > 0,
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt u (physicalEightModeField (u t)) t := by
  apply Rational345LocalODE.exists_local_solution
  exact physicalEightModeField_contDiff.contDiffAt

end Rational345QuadraticODE
end NSBControl
