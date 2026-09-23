import Integration.RiemannAdaptiveCutoffCrossingCompatibility
import Integration.RiemannPoleQuotientTerminal

/-!
# Adaptive cutoff selection feeding the terminal inequality (§§5, 7)

§7 of `Riemann_Pole_Quotient_Reduction_2026.pdf` explains how Lemma 5.1 is
actually used: the far majorant `Bfar (ρ; g, J)` tends to `0` in the cutoff `J`,
so once the finite near core plus the Gamma term sit *strictly* below the
cluster response by a fixed margin `δ`, a single cutoff can be chosen which both
crosses the quarter-period threshold and pays the far tail out of that margin.

This module records that composition: it is the exact point at which the two
proved lemmas of the manuscript (adaptive cutoff compatibility and the terminal
algebra) meet.  The uniform near-core margin `δ` is an input — it is precisely
the remaining analytic wall (Hypothesis 10.1), and nothing here proves it.
-/

namespace Integration.RiemannPoleQuotient

open Filter Topology

/-- **Adaptive selection of a cutoff realizing the strict high inequality.**

Given a family of pole–quotient responses indexed by the cutoff, in which

* the far majorant tends to `0`,
* the near core plus the Gamma term stay below the cluster response by the
  fixed margin `δ > 0`,

there is a cutoff `J ≥ 1` which crosses the quarter-period threshold `π/2 < J·L`
and for which the strict high inequality (3) holds. -/
theorem exists_cutoff_strictHigh {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (R : ℕ → PoleQuotientResponse)
    (hfar : Tendsto (fun J => (R J).far) atTop (𝓝 0))
    (hnear : ∀ J : ℕ, (R J).near + (R J).gamma + δ ≤ (R J).cluster) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.pi / 2 < J * L ∧ (R J).StrictHigh := by
  obtain ⟨J, hJ1, hJcross, hJfar⟩ := adaptive_cutoff_compatible hL hfar hδ
  refine ⟨J, hJ1, hJcross, ?_⟩
  have := hnear J
  unfold PoleQuotientResponse.StrictHigh
  linarith

/-- The same selection, run all the way to the contradiction of Theorem 8.1:
if in addition the exact balance and the near/far split hold at the selected
cutoff, the configuration is impossible. -/
theorem no_response_family_with_margin {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (R : ℕ → PoleQuotientResponse)
    (hfar : Tendsto (fun J => (R J).far) atTop (𝓝 0))
    (hnear : ∀ J : ℕ, (R J).near + (R J).gamma + δ ≤ (R J).cluster)
    (hbal : ∀ J : ℕ, (R J).Balance) (hsplit : ∀ J : ℕ, (R J).NearFarSplit) : False := by
  obtain ⟨J, -, -, hstrict⟩ := exists_cutoff_strictHigh hL hδ R hfar hnear
  exact terminal_contradiction (hbal J) (hsplit J) hstrict

end Integration.RiemannPoleQuotient
