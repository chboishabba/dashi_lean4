/-
# The prime channel in the even cone: a directional gate, answered

Step 5 of the programme.  The question posed is *not* whether the prime sum is
small, but whether the literal prime image can point in the direction required to
cancel the same-ordinate cluster:

    -Q_cluster  ∈?  Cone/Span { P(log n) }_{n ≥ 2},
    P(log n) weighted by  Λ(n) n^{-1/2} × the literal taper coefficient.

This module answers it for the tapers the programme actually uses, and the answer
is as sharp as it can be: **the literal prime image is the zero vector**.

The mechanism is the *support* of the even-channel taper.  Its two windows are
centred at `π/t` and `2π/t` with radius `π/(4t)`, so the taper is supported in
`|u| < 9π/(4|t|)`.  Every prime frequency of the explicit formula sits at
`u = ± log n` with `n ≥ 2`, hence at `|u| ≥ log 2`.  As soon as

    9π ≤ 4 |t| log 2,

no prime frequency reaches the taper, every summand of the literal von Mangoldt
sum vanishes, and therefore

    Q_prime = 0   (as a vector in ℝ⁴, not merely in the quotient).

Contents:

* `primeSummand_sampleTest` — the literal prime summand of the sample family, in
  closed real form: `Λ(n) n^{-1/2} · 2 g(log n) cos((s - t) log n)`.  This is the
  "weighted prime-frequency curve" the reachability question is about; it shows
  the taper coefficient is literally `g(log n)`.
* `primeTerm_sampleTest_eq_zero_of_short_taper`, `primeVec_eq_zero_of_short_taper`,
  `primeConeValue_eq_zero_of_short_taper` — the vanishing.
* `primeEvenConeUnreachable` — the capstone.  For a nontrivial zero of
  `riemannZeta` whose ordinate satisfies `9π ≤ 4|t| log 2`, the balance reads

      0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + ε_Γ(g, t, r),   Q_prime = 0,

  so the required cancellation of the strictly positive cluster must come entirely
  from the off-ordinate zeros and the gamma factor.  The prime cone is not merely
  too small: it is a single point.

**What is not claimed.**  This is a statement about *these* tapers.  It does not
say the prime side of the explicit formula is trivial, and it produces no
contradiction: the inequality above is satisfied by on-line zeros too, since
nothing in `ℓ(Q_cluster) > 0` uses the height of the target.  The remaining
analytic obligation is unchanged and is recorded in `FRONTIER.md`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilGammaConeBound

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilPrimeEvenCone

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaConeBound

/-! ## The literal prime summand of the sample family -/

/-- **The weighted prime-frequency curve, in closed real form.**  For an even
taper the `n`-th summand of the literal von Mangoldt term of the sample test at
radius `s` is the real number

    Λ(n) n^{-1/2} · 2 g(log n) cos((s - t) log n).

In particular the "literal taper coefficient" attached to the prime frequency
`log n` is exactly `g(log n)`. -/
theorem primeSummand_sampleTest {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (t s : ℝ) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (sampleTest g t s (Real.log n) + sampleTest g t s (-Real.log n))
      = (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ)
          * (2 * g (Real.log n) * Real.cos ((s - t) * Real.log n)) : ℝ) : ℂ) := by
  have hg : g (-Real.log n) = g (Real.log n) := heven _
  have hexp : ∀ y : ℝ, Complex.exp (Complex.I * ((y : ℝ) : ℂ))
      = ((Real.cos y : ℝ) : ℂ) + ((Real.sin y : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  simp only [sampleTest, hg]
  rw [show (s - t) * -Real.log n = -((s - t) * Real.log n) by ring]
  rw [hexp, hexp, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-! ## Vanishing of the prime channel for a short taper -/

/-- **The prime channel is invisible to a taper shorter than `log 2`.**  Every
prime frequency of the literal explicit formula lies at `|u| = log n ≥ log 2`. -/
theorem primeTerm_sampleTest_eq_zero_of_short_taper {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t s : ℝ) :
    primeTerm (sampleTest g t s) = 0 := by
  have hterm : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (sampleTest g t s (Real.log n) + sampleTest g t s (-Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hn0 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
        exact_mod_cast this
      have hlog2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hlognn : 0 ≤ Real.log n := Real.log_nonneg hn0
      have hz1 : g (Real.log n) = 0 := by
        by_contra h
        have hb := hshort _ h
        rw [abs_of_nonneg hlognn] at hb
        linarith
      have hz2 : g (-Real.log n) = 0 := by
        by_contra h
        have hb := hshort _ h
        rw [abs_neg, abs_of_nonneg hlognn] at hb
        linarith
      simp [sampleTest, hz1, hz2]
    · push_neg at hn
      interval_cases n <;> simp
  rw [primeTerm, funext hterm, tsum_zero]

/-- The four-sample prime vector of a short taper vanishes identically. -/
theorem primeVec_eq_zero_of_short_taper {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t r : ℝ) :
    primeVec (sampleFam g t r) = 0 := by
  funext i
  have h : primeTerm (sampleFam g t r i) = 0 := by
    fin_cases i <;> exact primeTerm_sampleTest_eq_zero_of_short_taper hshort _ _
  show reim (primeTerm (sampleFam g t r i)) = 0
  rw [h, reim_zero]

/-- Hence the even cone functional reads the prime channel as `0`. -/
theorem primeConeValue_eq_zero_of_short_taper {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t r : ℝ) :
    evenConeFunctional (primeVec (sampleFam g t r)) = 0 := by
  rw [primeVec_eq_zero_of_short_taper hshort, map_zero]

/-- The support radius of the even-channel taper is below `log 2` as soon as the
ordinate is high enough. -/
theorem short_taper_of_height {g : ℝ → ℝ} {t : ℝ}
    (hsupp : ∀ u, g u ≠ 0 → |u| < 9 * π / (4 * |t|)) (ht : t ≠ 0)
    (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∀ u, g u ≠ 0 → |u| < Real.log 2 := by
  intro u hu
  have habs : 0 < |t| := abs_pos.mpr ht
  have hle : 9 * π / (4 * |t|) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  exact lt_of_lt_of_le (hsupp u hu) hle

/-! ## The capstone -/

/-- **`primeEvenConeUnreachable`.**  For an actual nontrivial zero `ρ*` of
`riemannZeta` whose ordinate `t` satisfies `9π ≤ 4|t| log 2`, the even-channel
taper of the programme sees *no* prime frequency at all: the literal prime
four-sample vector is exactly `0`.  The balance therefore reads

    0 < ℓ(Q_cluster) ≤ ε_zero(g, Λ, t, r) + ε_Γ(g, t, r),

with the prime channel absent.  The reachability question of step 5 is thereby
answered in the strongest possible negative form for these tapers: the admissible
prime cone is the single point `0`, so it cannot supply the direction
`-Q_cluster`; whatever cancels the cluster is the off-ordinate zero fibre together
with the gamma factor.

This is not a contradiction, and none is claimed: the displayed inequality is
equally satisfied by on-line zeros. -/
theorem primeEvenConeUnreachable {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ) ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ (∀ u, g u ≠ 0 → |u| < Real.log 2)
      ∧ primeVec (sampleFam g t r) = 0
      ∧ clusterVec (sampleFam g t r) t + offOrdVec (sampleFam g t r) t
          + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0
      ∧ 0 < evenConeFunctional (clusterVec (sampleFam g t r) t)
      ∧ |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ epsZero g Λ t r
      ∧ |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ epsGamma g t r
      ∧ evenConeFunctional (clusterVec (sampleFam g t r) t)
          ≤ epsZero g Λ t r + epsGamma g t r := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, -, -, hpole, hA, hrad⟩ :=
    exists_positive_taper_poleEven_zero ht
  obtain ⟨Lam, hLam, hsupp⟩ := exists_support_radius hgc
  have hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2 := short_taper_of_height hrad ht hheight
  have hprime : primeVec (sampleFam g t r) = 0 := primeVec_eq_zero_of_short_taper hshort t r
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  rw [hprime] at hbal
  have hbal' : clusterVec (sampleFam g t r) t + offOrdVec (sampleFam g t r) t
      + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0 := by
    simpa using hbal
  have hpos : 0 < evenConeFunctional (clusterVec (sampleFam g t r) t) :=
    sameOrdinateClusterConePositive hgs hgc heven hA ⟨ρstar, him⟩
  have hoff := offOrdinateConeEnvelope hgs hgc hsupp hLam t r
  have hgam := gammaConeEnvelope hgs.continuous hgc heven t r
  have hlin : evenConeFunctional (clusterVec (sampleFam g t r) t)
      + evenConeFunctional (offOrdVec (sampleFam g t r) t)
      + evenConeFunctional (gammaVec (sampleFam g t r))
      + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, hbal', map_zero]
  have hpolezero : evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    have hmem := poleVec_mem_poleSpace hgs.continuous hgc heven t r
    simpa using evenConeFunctional_poleSpace_le_ker (g := g) (t := t) (r := r) hpole hmem
  rw [hpolezero, add_zero] at hlin
  refine ⟨g, r, Lam, hgs, hgc, heven, hrpos, hLam, hsupp, hpole, hA, hshort, hprime,
    hbal', hpos, hoff, hgam, ?_⟩
  have h1 := abs_le.mp hoff
  have h2 := abs_le.mp hgam
  linarith [h1.1, h2.1]

end LiteralWeilPrimeEvenCone
end Zeta23Bridge
