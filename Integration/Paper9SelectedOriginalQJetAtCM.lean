import Integration.Paper9ActualJSourceJet

/-!
Paper 9: selected actual CM163 q/Euler j-jet readout.
SOURCE-WRITTEN, KERNEL NOT EXECUTED.

Reuse the existing true analytic j, actual selected CM point, Ramanujan
q-system and theta/Eisenstein root. No second analytic j is constructed.
This is a selected specialization, not a Bishop-carrier transport.
The Bishop π ↔ Mathlib Real.pi phase weld remains an independent task.
-/
namespace Integration.Paper9SelectedOriginalQJetAtCM

open Complex Function UpperHalfPlane
open scoped Real Topology
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9SelectedCMDomain
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet

noncomputable section

def qCM : ℂ := Periodic.qParam 1 (cmTau : ℂ)

theorem qCMsmall : ‖qCM‖ < (1 : ℝ) := by
  exact lt_trans (by simpa [qCM] using cmQSmall)
    (by norm_num)

theorem qCMnonzero : qCM ≠ 0 := by
  rw [qCM,cmQPhase]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem xCMnonzero : x qCM ≠ 0 := by
  obtain ⟨hx,_⟩ := originalBands qCM
    (by simpa [qCM] using (le_of_lt cmQSmall))
  intro h
  have hl := lowerNorm (x qCM) hx
  rw [h,norm_zero] at hl
  norm_num at hl

theorem firstQJetCM :
    x qCM * euler jQ qCM = -(jQ qCM * y qCM) := by
  have h := jQEuler qCM qCMsmall qCMnonzero xCMnonzero
  calc
    x qCM * euler jQ qCM =
      x qCM * (-jQ qCM*y qCM/x qCM) := by rw [h]
    _ = -(jQ qCM*y qCM) := by
      field_simp [xCMnonzero]
      ring

-- This is exactly the second Bishop NativeJetReductionExact readout,
-- but retained here on the original Lean actual analytic q carrier.
theorem secondQJetCM :
    6 * (x qCM)^2 * secondEuler qCM =
      jQ qCM * (3*(x qCM)^3+3*(y qCM)^2-
        (y qCM)*(3*euler x qCM)) := by
  obtain ⟨_,h4,_⟩ := ramanujanQ qCM qCMsmall qCMnonzero
  have hshape :
      6 * (x qCM)^2 * secondEuler qCM =
        jQ qCM * (-e2Q qCM*x qCM*y qCM+
          3*(x qCM)^3+4*(y qCM)^2) := by
    unfold secondEuler
    field_simp [xCMnonzero]
    ring
  calc
    _ = jQ qCM * (-e2Q qCM*x qCM*y qCM+
          3*(x qCM)^3+4*(y qCM)^2) := hshape
    _ = jQ qCM * (3*(x qCM)^3+3*(y qCM)^2-
        (y qCM)*(3*euler x qCM)) := by
      linear_combination (jQ qCM * y qCM) * h4

-- The source also owns the actual second tau derivative; its
-- normalisation is (2*pi*i)^2 times the q-Euler second jet.
theorem actualTauSecondAtCM (hcoordinate : qExt cmPoint = qCM) :
    deriv (deriv jExt) cmPoint = scaleD^2 * secondEuler qCM := by
  have h := jExtSecond cmPoint
    (by simpa [hcoordinate] using qCMsmall)
    (by simpa [hcoordinate] using qCMnonzero)
    (by simpa [hcoordinate] using xCMnonzero)
  simpa [hcoordinate] using h

-- Reverse-solved selected source statement: the genuine hypergeometric
-- root and first jet are already owned by Paper9ActualCMPoint.
theorem actualSelectedHyperAndJets :
    rootF qCM = H (zCoord qCM) ∧
    L rootF qCM =
      Integration.Paper9HypergeometricSeriesODE.jet 1 (zCoord qCM) ∧
    x qCM * euler jQ qCM = -(jQ qCM * y qCM) ∧
    6 * (x qCM)^2 * secondEuler qCM =
      jQ qCM * (3*(x qCM)^3+3*(y qCM)^2-
        (y qCM)*(3*euler x qCM)) := by
  exact ⟨by simpa [qCM] using selectedHyperAtCM,
    by simpa [qCM] using selectedFirstJetAtCM,
    firstQJetCM,secondQJetCM⟩

#print axioms actualSelectedHyperAndJets
end
end Integration.Paper9SelectedOriginalQJetAtCM
