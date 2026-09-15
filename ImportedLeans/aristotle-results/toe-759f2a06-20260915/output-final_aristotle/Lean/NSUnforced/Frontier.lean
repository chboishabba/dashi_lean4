/-
# The exact remaining A1 obligation, as one named Lean proposition

Everything in `NSUnforced.A1Budget568` is a reduction: it turns *pointwise,
cutoff-uniform* control of the collapsed Gram channels into the R568 spacetime
budget.  This file names the residual hypothesis as a single proposition
`A1ChannelObligation` so that the frontier is a Lean object rather than a
paragraph, and proves that it is genuinely sufficient.

`A1ChannelObligation G Energy Dissip ν` says: there is a finite channel index
set (the Gram factorisation of the symmetric pair resolvent supplied by the
R503/R572 spectator-row machinery), assembled forcing and cell norms `A`, `B`
(the outputs of `fullSquareSum_gram_collapse`), and constants `c_A`, `c_B`,
`θ > 0` with

* `2 θ c_A < 2 ν` — strict sub-criticality of the dissipation share;
* `G ≤ ∑_c A c · B c` — the majorisation delivered by
  `abs_fullSquareSum_gram_collapse_le`, *after* the exact signed collapse;
* `∑_c (A c)² ≤ c_A · D` — the commutator/cell square receipt (this is where
  the R571 homochiral gain `|λ_q^s − λ_p^s| ≤ ‖k‖` and the R574 cell control
  have to be spent, and where the heterochiral rows must be handled by a
  separate mechanism — see
  `heterochiral_multiplierDifference_not_output_controlled`);
* `∑_c (B c)² ≤ c_B · E` — the cell/energy receipt.

`a1_of_channelObligation` proves `A1ChannelObligation → A1`.  Nothing in this
library proves `A1ChannelObligation` itself; that is the open wall.
-/
import NSUnforced.A1Budget568

noncomputable section

namespace DASHI.NS.Unforced

/-- The exact residual hypothesis of the A1 route. -/
def A1ChannelObligation (globalForcingFull Energy Dissip : ℕ → ℝ → ℝ) (nu : ℝ) : Prop :=
  ∃ (χ : Type) (C : ℕ → ℝ → Finset χ) (A B : ℕ → ℝ → χ → ℝ) (cA cB theta : ℝ),
    0 < theta ∧ 0 ≤ cA ∧ 0 ≤ cB ∧ 2 * theta * cA < 2 * nu ∧
      (∀ N t, globalForcingFull N t ≤ ∑ c ∈ C N t, A N t c * B N t c) ∧
      (∀ N t, ∑ c ∈ C N t, (A N t c) ^ 2 ≤ cA * Dissip N t) ∧
      (∀ N t, ∑ c ∈ C N t, (B N t c) ^ 2 ≤ cB * Energy N t)

/-- **The frontier is sufficient.**  The residual channel obligation, together
with the Galerkin energy balance and a cutoff-uniform initial-energy ceiling,
pays `CommutatorOnlySpacetimeBudget568`. -/
theorem a1_of_channelObligation
    {globalForcingFull Energy Dissip : ℕ → ℝ → ℝ} {nu E0 : ℝ}
    (hnu : 0 < nu)
    (hDc : ∀ N, Continuous (Dissip N)) (hGc : ∀ N, Continuous (globalForcingFull N))
    (hEnn : ∀ N t, 0 ≤ Energy N t) (hDnn : ∀ N t, 0 ≤ Dissip N t)
    (hbal : ∀ N t, HasDerivAt (Energy N)
      (-(2 * nu) * Dissip N t + 4 * globalForcingFull N t) t)
    (hE0 : ∀ N, Energy N 0 ≤ E0)
    (hfrontier : A1ChannelObligation globalForcingFull Energy Dissip nu) :
    Nonempty (CommutatorOnlySpacetimeBudget568 globalForcingFull) := by
  obtain ⟨_χ, C, A, B, cA, cB, theta, hth, hcA, hcB, hsub, hG, hAsq, hBsq⟩ := hfrontier
  exact ⟨budget568_of_channel_control C A B globalForcingFull Energy Dissip hnu hth
    hcA hcB hsub hDc hGc hEnn hDnn hbal hG hAsq hBsq hE0⟩

end DASHI.NS.Unforced
