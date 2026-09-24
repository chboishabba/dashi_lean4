/-
# The gamma channel of the literal Weil explicit formula, in parity coordinates

After `LiteralWeilParityBalance.lean` and `LiteralWeilOddChannelTaper.lean` the
literal zeta Weil explicit formula supplies, unconditionally, a four-sample
balance relation in which the pole contribution is killed exactly by the parity
quotient and the target contribution is nonzero.  The frontier is then the
residual triple `Q_other + Q_prime + Q_Γ`.  This module characterizes the last
and most deterministic of the three.

The results.  For the twisted sample test `k_s(u) = g(u) e^{i(s-t)u}` with a real,
even, `C²`, compactly supported taper `g`:

* `paperFT_sampleTest_real` — on the real axis the transform of the sample test is
  the *real* cosine transform of the taper, translated by the sample frequency:
  `h_{k_s}(r) = ĝ(r + s - t)` with `ĝ(x) = ∫ g(u) cos(xu) du`.
* `gammaTerm_sampleTest` — hence the gamma term is a real number, namely the
  smoothing of the gamma bracket by that translated cosine transform:
  `Γ_{k_s} = (1/2π) ∫ ĝ(r + s - t) · B(r) dr`,  `B(r) = Re Γ'/Γ(1/4 + ir/2) - log π`.
  In particular the gamma channel carries no imaginary contamination.
* `gammaBracket_even` — the gamma bracket is an even function of `r`, from the
  conjugation symmetry of the digamma function.
* `gammaResp_neg_sample` — **the reflection law.**  Reflecting the sample point is
  the same as reflecting the ordinate:  `Γ(t, -s) = Γ(-t, s)`.  So the parity of
  the gamma channel in the sample variable is exactly its parity in the ordinate
  of the target zero.
* `gammaVec_sampleFam_parity` — consequently the gamma four-sample vector splits
  into an even pattern built from the ordinate-symmetric part of the gamma
  response and an odd pattern built from its ordinate-antisymmetric part.
* `gammaVec_sampleFam_even_of_ordinate_zero` — at ordinate `t = 0` the odd part
  vanishes identically: the gamma channel then lives entirely in the even
  coordinates and contributes nothing to the odd channel.

No new analytic estimate occurs here; no integrability hypothesis is needed
either, since every step is either a pointwise identity, the `ℝ → ℂ` linear map
commuting with the Bochner integral, or the reflection invariance of Lebesgue
measure.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilParityBalance

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilGammaChannel

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance

/-! ## The real cosine transform of the taper -/

/-- The cosine transform `ĝ(x) = ∫ g(u) cos(xu) du`. -/
def cosFT (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u : ℝ, g u * Real.cos (x * u)

/-- The cosine transform is even, for every taper. -/
theorem cosFT_neg (g : ℝ → ℝ) (x : ℝ) : cosFT g (-x) = cosFT g x := by
  unfold cosFT
  congr 1
  funext u
  rw [show -x * u = -(x * u) by ring, Real.cos_neg]

/-- The integrand identity for a *real* frequency: the twist and the frequency
combine into the single frequency `r + s - t`. -/
theorem sampleTest_real_integrand (g : ℝ → ℝ) (t s r : ℝ) (u : ℝ) :
    sampleTest g t s u * Complex.exp (Complex.I * (r : ℂ) * u)
      = ((g u * Real.cos ((r + s - t) * u) : ℝ) : ℂ)
        + Complex.I * ((g u * Real.sin ((r + s - t) * u) : ℝ) : ℂ) := by
  rw [sampleTest, mul_assoc, ← Complex.exp_add]
  have h2 : Complex.I * (((s - t) * u : ℝ) : ℂ) + Complex.I * (r : ℂ) * (u : ℂ)
      = (((r + s - t) * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_mul_I]
  push_cast [Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- **On the real axis the sample transform is real.**  For an even taper,
`h_{k_s}(r) = ĝ(r + s - t)`. -/
theorem paperFT_sampleTest_real {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s r : ℝ) :
    paperFT (sampleTest g t s) (r : ℂ) = ((cosFT g (r + s - t) : ℝ) : ℂ) := by
  have hF : Integrable (fun u : ℝ => g u * Real.cos ((r + s - t) * u)) :=
    taper_integrable hg hgc (by fun_prop)
  have hG : Integrable (fun u : ℝ => g u * Real.sin ((r + s - t) * u)) :=
    taper_integrable hg hgc (by fun_prop)
  have hzero : ∫ u : ℝ, g u * Real.sin ((r + s - t) * u) = 0 := by
    apply integral_odd_zero
    intro u
    rw [heven u, show (r + s - t) * -u = -((r + s - t) * u) by ring, Real.sin_neg]
    ring
  rw [paperFT, show (fun u : ℝ => sampleTest g t s u * Complex.exp (Complex.I * (r : ℂ) * u))
      = fun u : ℝ => ((g u * Real.cos ((r + s - t) * u) : ℝ) : ℂ)
        + Complex.I * ((g u * Real.sin ((r + s - t) * u) : ℝ) : ℂ) from
    funext (sampleTest_real_integrand g t s r)]
  rw [integral_ofReal_add_I hF hG, hzero, cosFT]
  simp

/-! ## The gamma response -/

/-- The gamma response of the sample family: the smoothing of the gamma bracket by
the translated cosine transform of the taper. -/
def gammaResp (g : ℝ → ℝ) (t s : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ r : ℝ, cosFT g (r + s - t) * Zeta23.EF.gammaBracket r

/-- **The gamma term of a sample test is real**, and equals the gamma response. -/
theorem gammaTerm_sampleTest {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    gammaTerm (sampleTest g t s) = ((gammaResp g t s : ℝ) : ℂ) := by
  rw [gammaTerm, gammaResp]
  have hint : (fun r : ℝ => paperFT (sampleTest g t s) (r : ℂ)
        * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ))
      = fun r : ℝ => ((cosFT g (r + s - t) * Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
    funext r
    rw [paperFT_sampleTest_real hg hgc heven]
    push_cast
    ring
  rw [hint, integral_complex_ofReal]
  push_cast
  ring

/-- The real coordinate of the gamma term is the gamma response. -/
theorem reim_gammaTerm_sampleTest {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    reim (gammaTerm (sampleTest g t s)) = gammaResp g t s := by
  rw [gammaTerm_sampleTest hg hgc heven]
  simp [reim]

/-! ## The reflection law -/

/-- **The gamma bracket is even.**  `Re Γ'/Γ(1/4 + ir/2)` is even in `r`, because
`1/4 - ir/2` is the conjugate of `1/4 + ir/2` and the digamma function commutes
with conjugation. -/
theorem gammaBracket_even (r : ℝ) :
    Zeta23.EF.gammaBracket (-r) = Zeta23.EF.gammaBracket r := by
  unfold Zeta23.EF.gammaBracket
  congr 1
  have hz : starRingEnd ℂ (1 / 4 + Complex.I * (r : ℂ) / 2)
      = 1 / 4 + Complex.I * ((-r : ℝ) : ℂ) / 2 := by
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.ofReal_neg, map_one, map_ofNat]
    ring
  rw [← hz, Zeta23.digamma_conj]
  simp

/-- **The reflection law for the gamma channel.**  Reflecting the sample point is
the same as reflecting the ordinate of the target zero. -/
theorem gammaResp_neg_sample (g : ℝ → ℝ) (t s : ℝ) :
    gammaResp g t (-s) = gammaResp g (-t) s := by
  unfold gammaResp
  congr 1
  have key := MeasureTheory.integral_neg_eq_self
    (fun r : ℝ => cosFT g (r + s - -t) * Zeta23.EF.gammaBracket r) (volume : Measure ℝ)
  have hrw : (fun r : ℝ => cosFT g (-r + s - -t) * Zeta23.EF.gammaBracket (-r))
      = fun r : ℝ => cosFT g (r + -s - t) * Zeta23.EF.gammaBracket r := by
    funext r
    rw [gammaBracket_even]
    congr 1
    rw [← cosFT_neg g (r + -s - t)]
    congr 1
    ring
  calc ∫ r : ℝ, cosFT g (r + -s - t) * Zeta23.EF.gammaBracket r
      = ∫ r : ℝ, cosFT g (-r + s - -t) * Zeta23.EF.gammaBracket (-r) := by rw [hrw]
    _ = ∫ r : ℝ, cosFT g (r + s - -t) * Zeta23.EF.gammaBracket r := key

/-! ## The gamma vector in parity coordinates -/

/-- The ordinate-symmetric part of the gamma response. -/
def gammaEvenResp (g : ℝ → ℝ) (t s : ℝ) : ℝ := (gammaResp g t s + gammaResp g (-t) s) / 2

/-- The ordinate-antisymmetric part of the gamma response. -/
def gammaOddResp (g : ℝ → ℝ) (t s : ℝ) : ℝ := (gammaResp g t s - gammaResp g (-t) s) / 2

/-- **The gamma channel in parity coordinates.**  The gamma four-sample vector is
an even pattern built from the ordinate-symmetric part of the gamma response plus
an odd pattern built from its ordinate-antisymmetric part. -/
theorem gammaVec_sampleFam_parity {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    gammaVec (sampleFam g t r)
      = evenPattern (-gammaEvenResp g t r) (-gammaEvenResp g t (2 * r))
        + oddPattern (-gammaOddResp g t r) (-gammaOddResp g t (2 * r)) := by
  funext i
  have h0 : reim (gammaTerm (sampleTest g t r)) = gammaResp g t r :=
    reim_gammaTerm_sampleTest hg hgc heven t r
  have h1 : reim (gammaTerm (sampleTest g t (-r))) = gammaResp g (-t) r := by
    rw [reim_gammaTerm_sampleTest hg hgc heven, gammaResp_neg_sample]
  have h2 : reim (gammaTerm (sampleTest g t (2 * r))) = gammaResp g t (2 * r) :=
    reim_gammaTerm_sampleTest hg hgc heven t (2 * r)
  have h3 : reim (gammaTerm (sampleTest g t (-(2 * r)))) = gammaResp g (-t) (2 * r) := by
    rw [reim_gammaTerm_sampleTest hg hgc heven, gammaResp_neg_sample]
  fin_cases i
  · show -reim (gammaTerm (sampleTest g t r))
        = -gammaEvenResp g t r + -gammaOddResp g t r
    rw [h0, gammaEvenResp, gammaOddResp]; ring
  · show -reim (gammaTerm (sampleTest g t (-r)))
        = -gammaEvenResp g t r + -(-gammaOddResp g t r)
    rw [h1, gammaEvenResp, gammaOddResp]; ring
  · show -reim (gammaTerm (sampleTest g t (2 * r)))
        = -gammaEvenResp g t (2 * r) + -gammaOddResp g t (2 * r)
    rw [h2, gammaEvenResp, gammaOddResp]; ring
  · show -reim (gammaTerm (sampleTest g t (-(2 * r))))
        = -gammaEvenResp g t (2 * r) + -(-gammaOddResp g t (2 * r))
    rw [h3, gammaEvenResp, gammaOddResp]; ring

/-- **At ordinate zero the gamma channel is purely even.**  Its odd coordinates
vanish identically, so it contributes nothing to the odd channel of the balance
relation. -/
theorem gammaVec_sampleFam_even_of_ordinate_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (r : ℝ) :
    gammaVec (sampleFam g 0 r)
      = evenPattern (-gammaEvenResp g 0 r) (-gammaEvenResp g 0 (2 * r)) := by
  have hodd : ∀ s : ℝ, gammaOddResp g 0 s = 0 := by
    intro s
    simp [gammaOddResp]
  rw [gammaVec_sampleFam_parity hg hgc heven, hodd, hodd]
  funext i
  fin_cases i <;>
    simp [evenPattern, oddPattern]

end LiteralWeilGammaChannel
end Zeta23Bridge
