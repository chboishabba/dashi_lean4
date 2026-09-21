import Synthesis.RiemannProjectiveQuarticFourWindowPoleLocalization

/-!
# Positive-cone pole cancellation is impossible for narrow four-window witnesses

For every fixed t>=200, sufficiently narrow four-window profiles have strictly
positive literal projective pole defects throughout the complete coefficient
corridor.

Therefore no nontrivial nonnegative linear combination of any finite collection
of such pole channels can vanish.  In particular the positive-cone strategy
used to preserve the same-ordinate target lower bound cannot simultaneously
orthogonalize the pole channel inside this narrow four-window family.

Any surviving multi-detector route must either:
* use signed coefficients and re-prove target/same-ordinate positivity for the
  combined observable; or
* leave the sufficiently-narrow four-window regime.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

theorem three_narrow_quarticFour_poles_positive
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀
        (R1 R2 R3 lam1 lam2 lam3 mu1 mu2 mu3 : ℝ),
        0 < R1 -> R1 < delta ->
        0 < R2 -> R2 < delta ->
        0 < R3 -> R3 < delta ->
        lam1 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        lam2 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        lam3 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu1| <= 1/10 -> |mu2| <= 1/10 -> |mu3| <= 1/10 ->
        0 <
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
            (quarticFourPhysicalDetector R1 lam1 mu1 t) t (t/16)
        ∧
        0 <
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
            (quarticFourPhysicalDetector R2 lam2 mu2 t) t (t/16)
        ∧
        0 <
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
            (quarticFourPhysicalDetector R3 lam3 mu3 t) t (t/16) := by
  obtain ⟨delta,hdelta,hpos⟩ :=
    exists_radius_quarticFour_poleProjectiveDefect_pos ht
  refine ⟨delta,hdelta,?_⟩
  intro R1 R2 R3 lam1 lam2 lam3 mu1 mu2 mu3
    hR1 hR1d hR2 hR2d hR3 hR3d
    hlam1 hlam2 hlam3 hmu1 hmu2 hmu3
  exact ⟨
    hpos R1 lam1 mu1 hR1 hR1d hlam1 hmu1,
    hpos R2 lam2 mu2 hR2 hR2d hlam2 hmu2,
    hpos R3 lam3 mu3 hR3 hR3d hlam3 hmu3
  ⟩

/--
No nontrivial nonnegative three-detector combination can cancel the literal
projective pole channel in the sufficiently-narrow four-window regime.
-/
theorem no_three_narrow_quarticFour_positiveCone_pole_cancellation
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀
        (R1 R2 R3 lam1 lam2 lam3 mu1 mu2 mu3 c1 c2 c3 : ℝ),
        0 < R1 -> R1 < delta ->
        0 < R2 -> R2 < delta ->
        0 < R3 -> R3 < delta ->
        lam1 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        lam2 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        lam3 ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu1| <= 1/10 -> |mu2| <= 1/10 -> |mu3| <= 1/10 ->
        0 <= c1 -> 0 <= c2 -> 0 <= c3 ->
        (0 < c1 ∨ 0 < c2 ∨ 0 < c3) ->
        ¬ (
          c1 *
            Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
              (quarticFourPhysicalDetector R1 lam1 mu1 t) t (t/16)
          +
          c2 *
            Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
              (quarticFourPhysicalDetector R2 lam2 mu2 t) t (t/16)
          +
          c3 *
            Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
              (quarticFourPhysicalDetector R3 lam3 mu3 t) t (t/16)
          = 0) := by
  obtain ⟨delta,hdelta,hpos3⟩ :=
    three_narrow_quarticFour_poles_positive ht
  refine ⟨delta,hdelta,?_⟩
  intro R1 R2 R3 lam1 lam2 lam3 mu1 mu2 mu3 c1 c2 c3
    hR1 hR1d hR2 hR2d hR3 hR3d
    hlam1 hlam2 hlam3 hmu1 hmu2 hmu3
    hc1 hc2 hc3 hsome hzero
  obtain ⟨hp1,hp2,hp3⟩ :=
    hpos3 R1 R2 R3 lam1 lam2 lam3 mu1 mu2 mu3
      hR1 hR1d hR2 hR2d hR3 hR3d
      hlam1 hlam2 hlam3 hmu1 hmu2 hmu3
  rcases hsome with hc1p | hc2p | hc3p
  · have h1 : 0 < c1 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R1 lam1 mu1 t) t (t/16) :=
      mul_pos hc1p hp1
    have h2 : 0 <= c2 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R2 lam2 mu2 t) t (t/16) :=
      mul_nonneg hc2 hp2.le
    have h3 : 0 <= c3 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R3 lam3 mu3 t) t (t/16) :=
      mul_nonneg hc3 hp3.le
    linarith
  · have h1 : 0 <= c1 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R1 lam1 mu1 t) t (t/16) :=
      mul_nonneg hc1 hp1.le
    have h2 : 0 < c2 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R2 lam2 mu2 t) t (t/16) :=
      mul_pos hc2p hp2
    have h3 : 0 <= c3 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R3 lam3 mu3 t) t (t/16) :=
      mul_nonneg hc3 hp3.le
    linarith
  · have h1 : 0 <= c1 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R1 lam1 mu1 t) t (t/16) :=
      mul_nonneg hc1 hp1.le
    have h2 : 0 <= c2 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R2 lam2 mu2 t) t (t/16) :=
      mul_nonneg hc2 hp2.le
    have h3 : 0 < c3 *
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
          (quarticFourPhysicalDetector R3 lam3 mu3 t) t (t/16) :=
      mul_pos hc3p hp3
    linarith

end Synthesis
