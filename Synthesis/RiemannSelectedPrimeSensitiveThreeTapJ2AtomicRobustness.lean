import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Atomic
import Synthesis.RiemannProjectiveQuarticFourWindowRobustness

/-!
# Uniform smooth-to-atomic transfer for the J2 phase coordinates

The existing four-window localization theorem applies to every continuous even
weight.  In addition to the cosine responses A1,A2, the transformed J2 phase
normal form uses
  U_s(g)=integral g(u) u sin(su) du.
The weight u sin(su) is continuous and even, so U1,U2 converge uniformly to
their atomic counterparts on the same coefficient rectangle.

This file packages the four coordinates (A1,A2,U1,U2).  No sign transfer is
asserted without an explicit perturbation margin.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real

def quarticSinFirstWeight (s u : ℝ) : ℝ :=
  u * Real.sin (s*u)

theorem quarticSinFirstWeight_continuous (s : ℝ) :
    Continuous (quarticSinFirstWeight s) := by
  unfold quarticSinFirstWeight
  fun_prop

theorem quarticSinFirstWeight_even (s u : ℝ) :
    quarticSinFirstWeight s (-u) = quarticSinFirstWeight s u := by
  unfold quarticSinFirstWeight
  rw [mul_neg, Real.sin_neg]
  ring

theorem projectiveSinFirstResp_fourWindow_eq_pairing
    {R lam mu s : ℝ}
    (hR : 0 < R) :
    projectiveSinFirstResp
      (quarticFourWindowProfile R lam mu) s
      =
    quarticFourWindowPairing R lam mu
      (quarticSinFirstWeight s) := by
  unfold projectiveSinFirstResp quarticSinFirstWeight
  rw [quarticFourWindowProfile_pairing_eq hR
    (quarticSinFirstWeight_continuous s)]

theorem quarticFourAtomicPairing_sinFirstWeight
    (lam mu s : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticSinFirstWeight s)
      =
    quarticFourAtomicSinFirstRespAt lam mu s := by
  unfold quarticFourAtomicPairingAt quarticSinFirstWeight
    quarticFourAtomicSinFirstRespAt
  ring

theorem exists_radius_quarticFourWindow_sinFirst_close_atomic
    {s eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |
          projectiveSinFirstResp
            (quarticFourWindowProfile R lam mu) s
          - quarticFourAtomicSinFirstRespAt lam mu s
        | <= eps := by
  obtain ⟨delta,hdelta,hclose⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (quarticSinFirstWeight_continuous s)
      (quarticSinFirstWeight_even s) heps
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have h := hclose R lam mu hR hRd hlam hmu
  rw [← projectiveSinFirstResp_fourWindow_eq_pairing hR,
      quarticFourAtomicPairing_sinFirstWeight] at h
  exact h

theorem exists_radius_quarticFourWindow_evenResp_close_atomic
    {s eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |
          Zeta23Bridge.LiteralWeilParityBalance.evenResp
            (quarticFourWindowProfile R lam mu) 0 s
          - quarticFourAtomicRespAt lam mu s
        | <= eps := by
  obtain ⟨delta,hdelta,hclose⟩ :=
    exists_radius_quarticFourWindowPairing_close_atomic
      (by fun_prop : Continuous (fun u : ℝ => Real.cos (s*u)))
      (by
        intro u
        simp : ∀ u : ℝ,
          Real.cos (s*(-u)) = Real.cos (s*u))
      heps
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have h := hclose R lam mu hR hRd hlam hmu
  rw [evenResp_zero_fourWindow hR]
  unfold quarticFourWindowMomentResp
  have hat :
      quarticFourAtomicPairingAt lam mu
          (fun u : ℝ => Real.cos (s*u))
        =
      quarticFourAtomicRespAt lam mu s := by
    unfold quarticFourAtomicPairingAt quarticFourAtomicRespAt
    ring
  simpa [hat] using h

/-- Uniform simultaneous control of all four scalar inputs to the normalized
three-tap J2 phase normal form. -/
theorem exists_radius_quarticFourWindow_J2phase_coordinates_close_atomic
    {eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |
          Zeta23Bridge.LiteralWeilParityBalance.evenResp
            (quarticFourWindowProfile R lam mu) 0 1
          - quarticFourAtomicRespAt lam mu 1
        | <= eps
        ∧
        |
          Zeta23Bridge.LiteralWeilParityBalance.evenResp
            (quarticFourWindowProfile R lam mu) 0 2
          - quarticFourAtomicRespAt lam mu 2
        | <= eps
        ∧
        |
          projectiveSinFirstResp
            (quarticFourWindowProfile R lam mu) 1
          - quarticFourAtomicSinFirstRespAt lam mu 1
        | <= eps
        ∧
        |
          projectiveSinFirstResp
            (quarticFourWindowProfile R lam mu) 2
          - quarticFourAtomicSinFirstRespAt lam mu 2
        | <= eps := by
  obtain ⟨dA1,hdA1,hA1⟩ :=
    exists_radius_quarticFourWindow_evenResp_close_atomic
      (s:=1) heps
  obtain ⟨dA2,hdA2,hA2⟩ :=
    exists_radius_quarticFourWindow_evenResp_close_atomic
      (s:=2) heps
  obtain ⟨dU1,hdU1,hU1⟩ :=
    exists_radius_quarticFourWindow_sinFirst_close_atomic
      (s:=1) heps
  obtain ⟨dU2,hdU2,hU2⟩ :=
    exists_radius_quarticFourWindow_sinFirst_close_atomic
      (s:=2) heps
  let delta := min dA1 (min dA2 (min dU1 dU2))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdA1 (lt_min hdA2 (lt_min hdU1 hdU2))
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have hRdA1 : R < dA1 :=
    hRd.trans_le (min_le_left _ _)
  have hrest1 : R < min dA2 (min dU1 dU2) :=
    hRd.trans_le (min_le_right _ _)
  have hRdA2 : R < dA2 :=
    hrest1.trans_le (min_le_left _ _)
  have hrest2 : R < min dU1 dU2 :=
    hrest1.trans_le (min_le_right _ _)
  have hRdU1 : R < dU1 :=
    hrest2.trans_le (min_le_left _ _)
  have hRdU2 : R < dU2 :=
    hrest2.trans_le (min_le_right _ _)
  exact
    ⟨hA1 R lam mu hR hRdA1 hlam hmu,
     hA2 R lam mu hR hRdA2 hlam hmu,
     hU1 R lam mu hR hRdU1 hlam hmu,
     hU2 R lam mu hR hRdU2 hlam hmu⟩

end Synthesis
