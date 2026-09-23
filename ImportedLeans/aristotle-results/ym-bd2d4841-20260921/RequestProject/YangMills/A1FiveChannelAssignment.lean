/-
# Row A1.4 — the five-channel assignment: each source remainder into exactly
one existing analytic interface

The remainder mathematics of the Row A lane is already finished: there are
exactly two analytic interfaces,

* the **spectral** interface `logDetChannel` — a `log det` remainder controlled
  by a spectral bound on its eigenvalue family (`abs_logDetChannel_le`);
* the **polynomial** interface `tailPolyChannel` — a truncated power series
  controlled by its Taylor coefficients (`abs_tailPolyChannel_le`).

This file records the *assignment* of the five source remainders to those two
interfaces, and proves that the assembled interaction sector is exactly the sum
of the five assigned terms.  No new Taylor/Cauchy theorem is introduced; the
content is that the assignment is total, single-valued, and complete.

* `channelInterfaceOf` — the assignment, a function on the five channels, so
  each remainder lands in exactly one interface by construction.
* `shellInteraction_eq_sum_channelTerm` — completeness: the assembled
  interaction sector of the shell coefficient is precisely the sum over the five
  channels of the term supplied by the assigned interface.  Nothing else enters
  the interaction sector.
* `channelTerm_abs_le` — soundness: each channel is bounded by the majorant of
  the interface it is assigned to, and the resulting five coefficients are the
  entries of `sourceChannelCoefficient`.
* `betaInt_ge_of_assignment` — the assembled quartic debt
  `βInt ≥ −C_β g⁴` obtained through the assignment.

**Honest status.**  The *values* of the source Taylor/spectral data
(`lamDet, lamGauge, aInt, aChart, aLoc`) are inputs, not results; what the
assignment settles is that each of the five source remainders is consumed by one
and only one of the two existing analytic interfaces, with no channel left over
and no channel counted twice.
-/
import RequestProject.YangMills.A1SourceObjects

namespace YangMills

open Finset

/-! ## 1. The two analytic interfaces and the assignment -/

/-- The two analytic interfaces available for a remainder channel. -/
inductive ChannelInterface
  | spectralLogDet
  | polynomialTail
  deriving DecidableEq, Repr

/-- **The assignment.**  Being a function, it maps every source remainder into
exactly one interface. -/
def channelInterfaceOf : BetaChannel → ChannelInterface
  | BetaChannel.determinant => ChannelInterface.spectralLogDet
  | BetaChannel.gauge => ChannelInterface.spectralLogDet
  | BetaChannel.interaction => ChannelInterface.polynomialTail
  | BetaChannel.chart => ChannelInterface.polynomialTail
  | BetaChannel.localization => ChannelInterface.polynomialTail

/-- The term contributed by a channel, through the interface it is assigned
to. -/
noncomputable def channelTerm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lamDet : ι → ℝ) (lamGauge : κ → ℝ) (aInt aChart aLoc : ℕ → ℝ) (N : ℕ) (g : ℝ) :
    BetaChannel → ℝ
  | BetaChannel.determinant => logDetChannel lamDet g
  | BetaChannel.gauge => logDetChannel lamGauge g
  | BetaChannel.interaction => tailPolyChannel aInt N g
  | BetaChannel.chart => tailPolyChannel aChart N g
  | BetaChannel.localization => tailPolyChannel aLoc N g

/-! ## 2. Completeness of the assignment -/

/-- **The interaction sector is exactly the sum of the five assigned terms.**
Every source remainder is accounted for once. -/
theorem shellInteraction_eq_sum_channelTerm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lamDet : ℕ → (ℕ → ℝ) → ι → ℝ) (lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ)
    (aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ) (N : ℕ) (j : ℕ) (h : ℕ → ℝ) :
    shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N j h
      = ∑ k, channelTerm (lamDet j h) (lamGauge j h) (aInt j h) (aChart j h)
          (aLoc j h) N (h j) k := by
  rw [show (Finset.univ : Finset BetaChannel)
      = {BetaChannel.determinant, .interaction, .chart, .gauge, .localization} from rfl]
  simp [shellInteractionOfChannels, channelTerm]
  ring

/-! ## 3. Soundness of the assignment -/

/-- **Each channel is bounded by the majorant of its assigned interface**, with
the coefficient given by the corresponding entry of `sourceChannelCoefficient`:
the two spectral channels by the spectral majorant, the three polynomial
channels by the truncated-series majorant. -/
theorem channelTerm_abs_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {lamDet : ι → ℝ} {lamGauge : κ → ℝ} {aInt aChart aLoc : ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta g : ℝ}
    (hLd : ∀ i, |lamDet i| ≤ LamDet) (hLg : ∀ i, |lamGauge i| ≤ LamGauge)
    (hg0 : 0 ≤ g) (hgth : g ≤ theta) (hth : theta < 1)
    (hgLd : g * LamDet ≤ theta) (hgLg : g * LamGauge ≤ theta) (k : BetaChannel) :
    |channelTerm lamDet lamGauge aInt aChart aLoc N g k|
      ≤ sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
          LamDet LamGauge theta aInt aChart aLoc N k * g ^ 4 := by
  cases k
  · exact abs_logDetChannel_le hLd hg0 hgLd hth
  · exact abs_tailPolyChannel_le hg0 hgth
  · exact abs_tailPolyChannel_le hg0 hgth
  · exact abs_logDetChannel_le hLg hg0 hgLg hth
  · exact abs_tailPolyChannel_le hg0 hgth

/-- **The quartic debt obtained through the assignment.**  Summing the five
assigned majorants gives the interaction bound with `C_β` the sum of the five
`sourceChannelCoefficient` entries. -/
theorem betaInt_ge_of_assignment {ι κ : Type*} [Fintype ι] [Fintype κ]
    {lamDet : ι → ℝ} {lamGauge : κ → ℝ} {aInt aChart aLoc : ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta g : ℝ}
    (hLd : ∀ i, |lamDet i| ≤ LamDet) (hLg : ∀ i, |lamGauge i| ≤ LamGauge)
    (hg0 : 0 ≤ g) (hgth : g ≤ theta) (hth : theta < 1)
    (hgLd : g * LamDet ≤ theta) (hgLg : g * LamGauge ≤ theta) :
    -(Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta aInt aChart aLoc N)) * g ^ 4
      ≤ ∑ k, channelTerm lamDet lamGauge aInt aChart aLoc N g k :=
  betaInt_ge_of_channelMajorants (betaInt := fun g' =>
      ∑ k, channelTerm lamDet lamGauge aInt aChart aLoc N g' k)
    (ch := fun k g' => channelTerm lamDet lamGauge aInt aChart aLoc N g' k) rfl
    (fun k => channelTerm_abs_le hLd hLg hg0 hgth hth hgLd hgLg k)

end YangMills
