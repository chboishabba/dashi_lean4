/-
# The other-zeros channel of the literal Weil explicit formula

This module characterizes `Q_other`, and then draws the sharp negative
consequence for the odd-channel strategy of `LiteralWeilOddChannelTaper.lean`.

## The characterization

For the twisted sample test `k_s(u) = g(u) e^{i(s-t)u}` every zero
`ρ = 1/2 + a + ib` of the configuration contributes a parity pair *of exactly the
same shape as the target*, but evaluated at a frequency shifted by its ordinate
gap `δ = b - t`:

  `Z_ρ(k_s) = m_ρ (A_a(s + δ) + i B_a(s + δ))`,
  `A_y(x) = ∫ g cosh(yu) cos(xu) du`,  `B_y(x) = ∫ g sinh(yu) sin(xu) du`.

This is `reim_zeroTerm_sampleTest`.  The target zero is the case `δ = 0`.

## The negative consequence

Zeta's zero configuration is invariant under `ρ ↦ 1 - ρ̄` with equal
multiplicity — a structural fact, already available in the companion.  For an
off-line zero `ρ* = 1/2 + a + it` with `a ≠ 0` the partner is

  `reflect ρ* = 1/2 - a + it`,

a *distinct* member of the carrier with the *same* ordinate `t`, the *same*
multiplicity, and the *opposite* height `-a`.  Its ordinate gap is therefore also
zero, so it too contributes a genuine parity pair — and since `A_y` is even in `y`
while `B_y` is odd in `y`, the two parity pairs sum to something *purely even*:

  `targetParityVec(a) + targetParityVec(-a) = evenPattern (2 A_a(r)) (2 A_a(2r))`.

Consequently the odd coordinates of the four-sample balance relation cannot
separate the target from its functional-equation partner: the partner sits
literally inside `Q_other` (`otherZerosTerm_split_at_partner`) and cancels the
odd contribution of the target exactly, for *every* taper and *every* sample
radius.

So the transversality proved in `LiteralWeilOddChannelTaper.lean` — which is a
true statement about the isolated target vector — cannot by itself be turned into
a contradiction: the danger flagged for the other-zeros channel is real, and it is
realized by the reflection partner rather than by any delicate neighbouring zero.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilParityBalance

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOtherZerosChannel

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance

/-! ## Reordinating the sample test -/

/-- The twisted sample test only sees the difference `s - t`: twisting at ordinate
`t` and frequency `s` is the same as twisting at ordinate `b` and frequency
`s + b - t`. -/
theorem sampleTest_reordinate (g : ℝ → ℝ) (t b s : ℝ) :
    sampleTest g t s = sampleTest g b (s + b - t) := by
  funext u
  unfold sampleTest
  congr 3
  push_cast
  ring

/-- **The general zero evaluation.**  A zero of height `a` and ordinate `b`
contributes the parity pair at the shifted frequency `s + b - t`. -/
theorem paperFT_sampleTest_zero_shift {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {a b : ℝ} {ρ : ℂ}
    (hre : ρ.re = 1 / 2 + a) (him : ρ.im = b) (t s : ℝ) :
    paperFT (sampleTest g t s) (gammaOf ρ)
      = ((evenResp g a (s + b - t) : ℝ) : ℂ)
        + Complex.I * ((oddResp g a (s + b - t) : ℝ) : ℂ) := by
  rw [sampleTest_reordinate g t b s]
  exact paperFT_sampleTest_zero hg hgc heven hre him _

/-- The real response of a single zero: its parity pair at the shifted frequency. -/
def zeroResp (g : ℝ → ℝ) (a δ s : ℝ) : ℝ :=
  evenResp g a (s + δ) + oddResp g a (s + δ)

/-- **The other-zeros channel, coordinatewise.**  Every zero of the configuration
contributes `m_ρ` times its own parity pair, at the frequency shifted by its
ordinate gap. -/
theorem reim_zeroTerm_sampleTest {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {a b : ℝ} {ρ : Zeros}
    (hre : (ρ : ℂ).re = 1 / 2 + a) (him : (ρ : ℂ).im = b) (t s : ℝ) :
    reim (zeroTerm (sampleTest g t s) ρ)
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * zeroResp g a (b - t) s := by
  rw [zeroTerm, paperFT_sampleTest_zero_shift hg hgc heven hre him t s, zeroResp,
    show s + (b - t) = s + b - t by ring]
  simp [reim]
  ring

/-! ## The functional-equation partner -/

/-- The reflection partner of a member of the carrier is a member of the carrier. -/
def reflectZero (ρ : Zeros) : Zeros :=
  ⟨Zeta23.reflect (ρ : ℂ), (Zeta23.zetaZeroConfig).reflect_mem (ρ : ℂ) ρ.2⟩

theorem reflectZero_mult (ρ : Zeros) :
    (Zeta23.zetaZeroConfig).mult (reflectZero ρ) = (Zeta23.zetaZeroConfig).mult ρ :=
  (Zeta23.zetaZeroConfig).mult_reflect (ρ : ℂ) ρ.2

/-! ## The parity cancellation -/

theorem evenResp_neg_height (g : ℝ → ℝ) (y s : ℝ) : evenResp g (-y) s = evenResp g y s := by
  unfold evenResp
  congr 1
  funext u
  rw [show -y * u = -(y * u) by ring, Real.cosh_neg]

theorem oddResp_neg_height (g : ℝ → ℝ) (y s : ℝ) : oddResp g (-y) s = -oddResp g y s := by
  unfold oddResp
  rw [← integral_neg]
  congr 1
  funext u
  rw [show -y * u = -(y * u) by ring, Real.sinh_neg]
  ring

/-- **The parity pairs of a zero and of its functional-equation partner sum to a
purely even vector.**  The even response is even in the height, the odd response
is odd in it, so the odd coordinates cancel exactly — for every taper and every
sample radius. -/
theorem targetParityVec_add_reflect (g : ℝ → ℝ) (a r : ℝ) :
    targetParityVec g a r + targetParityVec g (-a) r
      = evenPattern (2 * evenResp g a r) (2 * evenResp g a (2 * r)) := by
  funext i
  fin_cases i
  · show evenResp g a r + oddResp g a r + (evenResp g (-a) r + oddResp g (-a) r)
        = 2 * evenResp g a r
    rw [evenResp_neg_height, oddResp_neg_height]; ring
  · show evenResp g a r + -oddResp g a r + (evenResp g (-a) r + -oddResp g (-a) r)
        = 2 * evenResp g a r
    rw [evenResp_neg_height, oddResp_neg_height]; ring
  · show evenResp g a (2 * r) + oddResp g a (2 * r)
          + (evenResp g (-a) (2 * r) + oddResp g (-a) (2 * r))
        = 2 * evenResp g a (2 * r)
    rw [evenResp_neg_height, oddResp_neg_height]; ring
  · show evenResp g a (2 * r) + -oddResp g a (2 * r)
          + (evenResp g (-a) (2 * r) + -oddResp g (-a) (2 * r))
        = 2 * evenResp g a (2 * r)
    rw [evenResp_neg_height, oddResp_neg_height]; ring

/-! ## The partner sits inside the other-zeros sum -/

/-- **`otherZerosTerm_split_at_partner`.**  When the partner is distinct from the
target, the other-zeros sum splits off the partner's own contribution.  As with
the target split, the summability comes from the literal explicit formula, so this
is a decomposition and not a convergence step. -/
theorem otherZerosTerm_split_at_partner {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (ρstar ρ' : Zeros) (hne : ρ' ≠ ρstar) :
    otherZerosTerm k ρstar
      = zeroTerm k ρ'
        + ∑' ρ : Zeros, if ρ = ρ' then 0 else (if ρ = ρstar then 0 else zeroTerm k ρ) := by
  classical
  have hupd : (fun ρ : Zeros => if ρ = ρstar then 0 else zeroTerm k ρ)
      = Function.update (zeroTerm k) ρstar 0 := by
    funext ρ
    rw [Function.update_apply]
  have hsum : Summable (fun ρ : Zeros => if ρ = ρstar then 0 else zeroTerm k ρ) := by
    rw [hupd]
    exact (zeroTerm_summable hk hkc).update ρstar 0
  have h := hsum.tsum_eq_add_tsum_ite ρ'
  rw [otherZerosTerm, h, if_neg hne]

/-! ## The capstone -/

/-- **`literalWeilReflectionPartnerOddCancellation`.**  For an actual off-line zero
`ρ* = 1/2 + a + it` of the configuration, the functional-equation partner
`reflect ρ* = 1/2 - a + it` is a *distinct* member of the carrier with the *same*
ordinate and the *same* multiplicity, and the combined parity contribution of the
two is purely even:

  `m • targetParityVec(a) + m • targetParityVec(-a) = m • evenPattern (2A_a(r)) (2A_a(2r))`.

Moreover the partner's own contribution is literally a summand of the other-zeros
term.  Hence the odd coordinates of the four-sample balance relation cannot
separate the target from its partner, for any taper and any sample radius. -/
theorem literalWeilReflectionPartnerOddCancellation {ρstar : Zeros} {a t : ℝ}
    (hre : (ρstar : ℂ).re = 1 / 2 + a) (him : (ρstar : ℂ).im = t) (ha : a ≠ 0)
    (g : ℝ → ℝ) (r : ℝ) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ ρ' : Zeros, ρ' ≠ ρstar
      ∧ (ρ' : ℂ).re = 1 / 2 + -a
      ∧ (ρ' : ℂ).im = t
      ∧ (Zeta23.zetaZeroConfig).mult ρ' = (Zeta23.zetaZeroConfig).mult ρstar
      ∧ (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g a r
          + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r
        = ((Zeta23.zetaZeroConfig).mult ρstar : ℝ)
            • evenPattern (2 * evenResp g a r) (2 * evenResp g a (2 * r)))
      ∧ otherZerosTerm k ρstar
        = zeroTerm k ρ'
          + ∑' ρ : Zeros, if ρ = ρ' then 0 else (if ρ = ρstar then 0 else zeroTerm k ρ) := by
  refine ⟨reflectZero ρstar, ?_, ?_, ?_, reflectZero_mult ρstar, ?_, ?_⟩
  · intro hcontra
    have hval : ((reflectZero ρstar : Zeros) : ℂ) = (ρstar : ℂ) := by rw [hcontra]
    have : (1 : ℝ) - (ρstar : ℂ).re = (ρstar : ℂ).re := by
      rw [← Zeta23.reflect_re]
      exact congrArg Complex.re hval
    rw [hre] at this
    apply ha
    linarith
  · show (Zeta23.reflect (ρstar : ℂ)).re = 1 / 2 + -a
    rw [Zeta23.reflect_re, hre]
    ring
  · show (Zeta23.reflect (ρstar : ℂ)).im = t
    rw [Zeta23.reflect_im, him]
  · rw [reflectZero_mult, ← smul_add, targetParityVec_add_reflect]
  · apply otherZerosTerm_split_at_partner hk hkc
    intro hcontra
    have hval : ((reflectZero ρstar : Zeros) : ℂ) = (ρstar : ℂ) := by rw [hcontra]
    have : (1 : ℝ) - (ρstar : ℂ).re = (ρstar : ℂ).re := by
      rw [← Zeta23.reflect_re]
      exact congrArg Complex.re hval
    rw [hre] at this
    apply ha
    linarith

end LiteralWeilOtherZerosChannel
end Zeta23Bridge
