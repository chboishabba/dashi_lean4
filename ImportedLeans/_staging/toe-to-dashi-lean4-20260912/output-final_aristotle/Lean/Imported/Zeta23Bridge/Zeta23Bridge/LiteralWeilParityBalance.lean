/-
# The literal Weil explicit formula supplies the four-sample parity balance

This module sits in the *separate* Lean project `Zeta23Bridge/`, on the toolchain
required by the companion library `Zeta23`
(<https://github.com/anthropics/zeta-23-lean>, pinned in `Zeta23Bridge/lakefile.toml`),
because that library is built against a different Lean/Mathlib version than the main
`RiemannAnalytic` library of this repository.  It is the only reason the module is
not called `RiemannAnalytic/LiteralWeilParityBalance.lean`.

What is consumed: the companion's **literal zeta Weil explicit formula**

  `Zeta23.WeilEF.EF_lit_zetaZeroConfig : Zeta23.EF.EF_lit Zeta23.zetaZeroConfig`,

i.e. for every `k ∈ C²_c(ℝ)`, with `h = paperFT k`, the zero sum over the actual
nontrivial zeros of Mathlib's `riemannZeta` (multiplicities = analytic orders) is
absolutely convergent and

  `∑_ρ m_ρ h(γ_ρ) = h(i/2) + h(-i/2)
                     - ∑_n Λ(n) n^{-1/2} (k(log n) + k(-log n))
                     + (1/2π) ∫ h(r) (Re Γ'/Γ(1/4 + ir/2) - log π) dr`,

`γ_ρ = (ρ - 1/2)/i`.  Nothing here is assumed: the companion theorem is
unconditional and its `#print axioms` is `propext, Classical.choice, Quot.sound`.

What is produced, in the order of the requested stack:

* `literalWeilSampleBalance` — the scalar identity rearranged to
  `zeroSum + prime + (-gamma) + (-pole) = 0`;
* `targetZeroPlusOtherZerosSplit` — the absolutely convergent zero sum split at a
  chosen target zero `ρ*`, `∑_ρ Z_ρ = Z_{ρ*} + ∑_{ρ ≠ ρ*} Z_ρ`;
* `literalWeilFiveTermBalance` — the five-term scalar balance
  `v_target + v_other + v_prime + v_Γ + v_pole = 0`;
* `literalWeilFourSampleBalance` — the same balance in `ℝ⁴`, for an arbitrary
  family of four admissible test functions and the real parity functional
  `z ↦ z.re + z.im`;
* `sampleTest_*` — the literal four-member sample family
  `k_s(u) = g(u) e^{i(s-t)u}`, `s ∈ {r, -r, 2r, -2r}`, attached to an even,
  `C²`, compactly supported profile `g` and the ordinate `t = Im ρ*`;
* `literalWeilParityCoordinateIdentification` — the target coordinate is literally
  the parity pair: `v_target = m_ρ • (evenPattern (A_α r) (A_α 2r)
  + oddPattern (B_α r) (B_α 2r))` with
  `A_y(s) = ∫ g(u) cosh(yu) cos(su) du`, `B_y(s) = ∫ g(u) sinh(yu) sin(su) du`
  and `α = Re ρ* - 1/2`;
* `poleVec_mem_poleSpace` — the pole coordinate lies in the two-dimensional
  even/odd *pole space* built from the `t`-modulated pole responses
  `Ec(s) = ∫ g cosh(u/2) cos(tu) cos(su)`, `Os(s) = ∫ g cosh(u/2) sin(tu) sin(su)`;
* `literalWeilFourSampleParityBalance` — the packaged statement: for an actual
  nontrivial zero of `riemannZeta`, the four-sample balance holds with the target
  coordinate identified and the pole coordinate inside the pole space;
* `literalWeilParityQuotientDecompositionUnconditional` — the quotient
  consequence: modulo the pole space, `Q_target = -(Q_other + Q_prime + Q_Γ)`,
  and the right-hand side is nonzero as soon as the two parity minors of the
  target-versus-pole pair are nonzero.

**The one hypothesis that remains, stated exactly.**  The final corollary needs the
two `2 × 2` parity minors

  `A_α(r) Ec(2r) - A_α(2r) Ec(r) ≠ 0`   and   `B_α(r) Os(2r) - B_α(2r) Os(r) ≠ 0`

to be nonzero.  This is *not* the minor pair proved in
`RiemannAnalytic/ParityMinorAssembly.lean`: the literal explicit formula produces
the pole responses modulated by the target ordinate `t` (the factors `cos(tu)`,
`sin(tu)` above), whereas the proved minors compare `cosh(yu)`/`sinh(yu)` at two
heights against one and the same taper.  Identifying the pole side as an
even/odd pair is done here; showing that pair is transverse to the target pair is
the next analytic obligation, and it is left as an explicit hypothesis, never
assumed.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23.WeilEF.Main

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real ArithmeticFunction

namespace Zeta23Bridge
namespace LiteralWeilParityBalance

open Zeta23 Zeta23.EF

/-! ## The five terms of the literal explicit formula -/

/-- The index type of the literal zero sum: the actual nontrivial zeros of
Mathlib's `riemannZeta`. -/
abbrev Zeros : Type := (Zeta23.zetaZeroConfig).carrier

/-- The zero-side summand `Z_ρ = m_ρ h(γ_ρ)`. -/
def zeroTerm (k : ℝ → ℂ) (ρ : Zeros) : ℂ :=
  ((Zeta23.zetaZeroConfig).mult ρ : ℂ) * paperFT k (gammaOf ρ)

/-- The pole term `h(i/2) + h(-i/2)`. -/
def poleTerm (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

/-- The von-Mangoldt prime term `∑_n Λ(n) n^{-1/2} (k(log n) + k(-log n))`. -/
def primeTerm (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (k (Real.log n) + k (-Real.log n))

/-- The gamma term `(1/2π) ∫ h(r) (Re Γ'/Γ(1/4 + ir/2) - log π) dr`. -/
def gammaTerm (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)

theorem literatureRHS_eq (k : ℝ → ℂ) :
    literatureRHS k = poleTerm k - primeTerm k + gammaTerm k := rfl

/-- **The zero sum is summable**, from the companion's literal explicit formula. -/
theorem zeroTerm_summable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (zeroTerm k) :=
  (Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc).1

/-- **The literal zeta Weil explicit formula**, in the notation of this module. -/
theorem literalWeilExplicitFormula {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    ∑' ρ : Zeros, zeroTerm k ρ = poleTerm k - primeTerm k + gammaTerm k :=
  (Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc).2

/-- **`literalWeilSampleBalance`.**  The literal explicit formula rearranged as a
vanishing sum of the four literal contributions. -/
theorem literalWeilSampleBalance {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    (∑' ρ : Zeros, zeroTerm k ρ) + primeTerm k + (-gammaTerm k) + (-poleTerm k) = 0 := by
  rw [literalWeilExplicitFormula hk hkc]; ring

/-! ## Splitting the zero sum at the target zero -/

/-- The other-zeros sum `∑_{ρ ≠ ρ*} Z_ρ`. -/
def otherZerosTerm (k : ℝ → ℂ) (ρstar : Zeros) : ℂ :=
  ∑' ρ : Zeros, if ρ = ρstar then 0 else zeroTerm k ρ

/-- **`targetZeroPlusOtherZerosSplit`.**  The absolutely convergent zero sum of the
literal explicit formula splits at any chosen target zero.  The summability comes
from `EF_lit_zeta` itself, so this is a decomposition, not a convergence, step. -/
theorem targetZeroPlusOtherZerosSplit {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (ρstar : Zeros) :
    ∑' ρ : Zeros, zeroTerm k ρ = zeroTerm k ρstar + otherZerosTerm k ρstar := by
  classical
  exact (zeroTerm_summable hk hkc).tsum_eq_add_tsum_ite ρstar

/-- **`literalWeilFiveTermBalance`.**  The five literal contributions of the Weil
explicit formula — target zero, other zeros, primes, gamma, poles — sum to zero. -/
theorem literalWeilFiveTermBalance {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (ρstar : Zeros) :
    zeroTerm k ρstar + otherZerosTerm k ρstar + primeTerm k + (-gammaTerm k)
      + (-poleTerm k) = 0 := by
  have h := literalWeilSampleBalance hk hkc
  rw [targetZeroPlusOtherZerosSplit hk hkc ρstar] at h
  exact h

/-! ## The four-sample form -/

/-- The real parity functional on a complex coordinate: `z ↦ Re z + Im z`.  On the
sample family below its two summands are exactly the even and the odd parity
channel. -/
def reim (z : ℂ) : ℝ := z.re + z.im

theorem reim_add (z w : ℂ) : reim (z + w) = reim z + reim w := by
  simp [reim]; ring

theorem reim_neg (z : ℂ) : reim (-z) = -reim z := by simp [reim]; ring

theorem reim_zero : reim 0 = 0 := by simp [reim]

theorem reim_real_mul (c : ℝ) (z : ℂ) : reim ((c : ℂ) * z) = c * reim z := by
  simp [reim]; ring

/-- The target four-sample vector. -/
def targetVec (kFam : Fin 4 → ℝ → ℂ) (ρstar : Zeros) : Fin 4 → ℝ :=
  fun i => reim (zeroTerm (kFam i) ρstar)

/-- The other-zeros four-sample vector. -/
def otherVec (kFam : Fin 4 → ℝ → ℂ) (ρstar : Zeros) : Fin 4 → ℝ :=
  fun i => reim (otherZerosTerm (kFam i) ρstar)

/-- The prime four-sample vector. -/
def primeVec (kFam : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ := fun i => reim (primeTerm (kFam i))

/-- The gamma four-sample vector (sign as it enters the balance). -/
def gammaVec (kFam : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ := fun i => -reim (gammaTerm (kFam i))

/-- The pole four-sample vector (sign as it enters the balance). -/
def poleVec (kFam : Fin 4 → ℝ → ℂ) : Fin 4 → ℝ := fun i => -reim (poleTerm (kFam i))

/-- **`literalWeilFourSampleBalance`.**  For any four admissible test functions and
any target zero, the five four-sample vectors supplied by the literal zeta Weil
explicit formula sum to zero in `ℝ⁴`. -/
theorem literalWeilFourSampleBalance {kFam : Fin 4 → ℝ → ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i)) (hkc : ∀ i, HasCompactSupport (kFam i))
    (ρstar : Zeros) :
    targetVec kFam ρstar + otherVec kFam ρstar + primeVec kFam + gammaVec kFam
      + poleVec kFam = 0 := by
  funext i
  have h := literalWeilFiveTermBalance (hk i) (hkc i) ρstar
  have : reim (zeroTerm (kFam i) ρstar + otherZerosTerm (kFam i) ρstar
      + primeTerm (kFam i) + (-gammaTerm (kFam i)) + (-poleTerm (kFam i))) = 0 := by
    rw [h]; exact reim_zero
  simp only [reim_add, reim_neg] at this
  simpa [targetVec, otherVec, primeVec, gammaVec, poleVec] using this

/-! ## The literal four-member sample family

The profile `g` is an even, `C²`, compactly supported real taper — the symmetric
extension `g(u) = φ(|u|)` of the tapers used on the zero side.  The sample test
function at a real sample point `s`, twisted by the target ordinate `t`, is

  `k_s(u) = g(u) e^{i(s-t)u}`.

The twist by `t = Im ρ*` is what makes the *target* coordinate come out in the
untwisted parity responses; it moves the ordinate dependence onto the pole term,
where it appears as the modulation `cos(tu)`, `sin(tu)` of the pole taper. -/

/-- The literal sample test function `k_s(u) = g(u) e^{i(s-t)u}`. -/
def sampleTest (g : ℝ → ℝ) (t s : ℝ) : ℝ → ℂ :=
  fun u => (g u : ℂ) * Complex.exp (Complex.I * (((s - t) * u : ℝ) : ℂ))

theorem sampleTest_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (t s : ℝ) :
    ContDiff ℝ 2 (sampleTest g t s) := by
  have h1 : ContDiff ℝ 2 (fun u : ℝ => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have h2 : ContDiff ℝ 2 (fun u : ℝ => Complex.exp (Complex.I * (((s - t) * u : ℝ) : ℂ))) := by
    apply Complex.contDiff_exp.of_le le_top |>.comp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))
  exact h1.mul h2

theorem sampleTest_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) (t s : ℝ) :
    HasCompactSupport (sampleTest g t s) := by
  have h : HasCompactSupport (fun u : ℝ => (g u : ℂ)) := by
    apply hg.comp_left (g := fun x : ℝ => (x : ℂ)); simp
  exact h.mul_right

/-! ## The two parity responses and the two modulated pole responses -/

/-- The even parity response `A_y(s) = ∫ g(u) cosh(yu) cos(su) du`. -/
def evenResp (g : ℝ → ℝ) (y s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * (Real.cosh (y * u) * Real.cos (s * u))

/-- The odd parity response `B_y(s) = ∫ g(u) sinh(yu) sin(su) du`. -/
def oddResp (g : ℝ → ℝ) (y s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * (Real.sinh (y * u) * Real.sin (s * u))

/-- The even pole response, modulated by the target ordinate `t`:
`Ec(s) = ∫ g(u) cosh(u/2) cos(tu) cos(su) du`. -/
def poleEvenResp (g : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))

/-- The odd pole response, modulated by the target ordinate `t`:
`Os(s) = ∫ g(u) cosh(u/2) sin(tu) sin(su) du`. -/
def poleOddResp (g : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))

theorem evenResp_neg (g : ℝ → ℝ) (y s : ℝ) : evenResp g y (-s) = evenResp g y s := by
  unfold evenResp
  congr 1; funext u
  rw [show -s * u = -(s * u) by ring, Real.cos_neg]

theorem oddResp_neg (g : ℝ → ℝ) (y s : ℝ) : oddResp g y (-s) = -oddResp g y s := by
  unfold oddResp
  rw [← integral_neg]
  congr 1; funext u
  rw [show -s * u = -(s * u) by ring, Real.sin_neg]
  ring

theorem poleEvenResp_neg (g : ℝ → ℝ) (t s : ℝ) :
    poleEvenResp g t (-s) = poleEvenResp g t s := by
  unfold poleEvenResp
  congr 1; funext u
  rw [show -s * u = -(s * u) by ring, Real.cos_neg]

theorem poleOddResp_neg (g : ℝ → ℝ) (t s : ℝ) :
    poleOddResp g t (-s) = -poleOddResp g t s := by
  unfold poleOddResp
  rw [← integral_neg]
  congr 1; funext u
  rw [show -s * u = -(s * u) by ring, Real.sin_neg]
  ring

/-! ## Integration toolkit -/

theorem integral_odd_zero {f : ℝ → ℝ} (h : ∀ u, f (-u) = -f u) : ∫ u : ℝ, f u = 0 := by
  have h1 := MeasureTheory.integral_neg_eq_self f (volume : Measure ℝ)
  simp only [h] at h1
  rw [integral_neg] at h1
  linarith

theorem integral_ofReal_add_I {F G : ℝ → ℝ} (hF : Integrable F) (hG : Integrable G) :
    ∫ u : ℝ, (((F u : ℝ) : ℂ) + Complex.I * ((G u : ℝ) : ℂ))
      = ((∫ u : ℝ, F u : ℝ) : ℂ) + Complex.I * ((∫ u : ℝ, G u : ℝ) : ℂ) := by
  rw [integral_add hF.ofReal ((hG.ofReal).const_mul _), integral_complex_ofReal,
    integral_const_mul, integral_complex_ofReal]

theorem taper_integrable {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {h : ℝ → ℝ} (hh : Continuous h) : Integrable (fun u : ℝ => g u * h u) :=
  (hg.mul hh).integrable_of_hasCompactSupport (hgc.mul_right (f' := h))

/-! ## The target coordinate -/

/-- The integrand identity behind the target evaluation: with `ρ = 1/2 + α + it`
the twist cancels the ordinate and leaves `g(u) e^{αu} e^{isu}`. -/
theorem sampleTest_mul_exp (g : ℝ → ℝ) (t s α : ℝ) (ρ : ℂ) (hre : ρ.re = 1 / 2 + α)
    (him : ρ.im = t) (u : ℝ) :
    sampleTest g t s u * Complex.exp (Complex.I * gammaOf ρ * u)
      = ((g u * (Real.exp (α * u) * Real.cos (s * u)) : ℝ) : ℂ)
        + Complex.I * ((g u * (Real.exp (α * u) * Real.sin (s * u)) : ℝ) : ℂ) := by
  have hρ : ρ = ((1 / 2 + α : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre, him]
  have hγ : Complex.I * gammaOf ρ = (α : ℂ) + Complex.I * (t : ℂ) := by
    rw [gammaOf, hρ]
    field_simp
    ring_nf
    simp
    ring
  rw [sampleTest, mul_assoc, ← Complex.exp_add, hγ]
  have h2 : Complex.I * (((s - t) * u : ℝ) : ℂ) + ((α : ℂ) + Complex.I * (t : ℂ)) * u
      = ((α * u : ℝ) : ℂ) + ((s * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_mul_I]
  push_cast [Complex.ofReal_exp, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- `∫ g(u) e^{yu} cos(su) du = A_y(s)` for an even taper: the `sinh` half is odd. -/
theorem integral_exp_cos {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (y s : ℝ) :
    ∫ u : ℝ, g u * (Real.exp (y * u) * Real.cos (s * u)) = evenResp g y s := by
  have hsplit : (fun u : ℝ => g u * (Real.exp (y * u) * Real.cos (s * u)))
      = fun u : ℝ => g u * (Real.cosh (y * u) * Real.cos (s * u))
        + g u * (Real.sinh (y * u) * Real.cos (s * u)) := by
    funext u; rw [← Real.cosh_add_sinh]; ring
  have hi1 : Integrable (fun u : ℝ => g u * (Real.cosh (y * u) * Real.cos (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hi2 : Integrable (fun u : ℝ => g u * (Real.sinh (y * u) * Real.cos (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hzero : ∫ u : ℝ, g u * (Real.sinh (y * u) * Real.cos (s * u)) = 0 := by
    apply integral_odd_zero
    intro u
    rw [heven u, show y * -u = -(y * u) by ring, show s * -u = -(s * u) by ring,
      Real.sinh_neg, Real.cos_neg]
    ring
  rw [hsplit, integral_add hi1 hi2, hzero, add_zero, evenResp]

/-- `∫ g(u) e^{yu} sin(su) du = B_y(s)` for an even taper: the `cosh` half is odd. -/
theorem integral_exp_sin {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (y s : ℝ) :
    ∫ u : ℝ, g u * (Real.exp (y * u) * Real.sin (s * u)) = oddResp g y s := by
  have hsplit : (fun u : ℝ => g u * (Real.exp (y * u) * Real.sin (s * u)))
      = fun u : ℝ => g u * (Real.cosh (y * u) * Real.sin (s * u))
        + g u * (Real.sinh (y * u) * Real.sin (s * u)) := by
    funext u; rw [← Real.cosh_add_sinh]; ring
  have hi1 : Integrable (fun u : ℝ => g u * (Real.cosh (y * u) * Real.sin (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hi2 : Integrable (fun u : ℝ => g u * (Real.sinh (y * u) * Real.sin (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hzero : ∫ u : ℝ, g u * (Real.cosh (y * u) * Real.sin (s * u)) = 0 := by
    apply integral_odd_zero
    intro u
    rw [heven u, show y * -u = -(y * u) by ring, show s * -u = -(s * u) by ring,
      Real.cosh_neg, Real.sin_neg]
    ring
  rw [hsplit, integral_add hi1 hi2, hzero, zero_add, oddResp]

/-- **The target evaluation.**  For `ρ = 1/2 + α + it` the literal Weil evaluation of
the sample test function at the zero is exactly the parity pair of the taper at
height `α`: `h_{k_s}(γ_ρ) = A_α(s) + i B_α(s)`. -/
theorem paperFT_sampleTest_zero {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) {α t : ℝ} {ρ : ℂ} (hre : ρ.re = 1 / 2 + α) (him : ρ.im = t)
    (s : ℝ) :
    paperFT (sampleTest g t s) (gammaOf ρ)
      = ((evenResp g α s : ℝ) : ℂ) + Complex.I * ((oddResp g α s : ℝ) : ℂ) := by
  have hF : Integrable (fun u : ℝ => g u * (Real.exp (α * u) * Real.cos (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hG : Integrable (fun u : ℝ => g u * (Real.exp (α * u) * Real.sin (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  rw [paperFT]
  rw [show (fun u : ℝ => sampleTest g t s u * Complex.exp (Complex.I * gammaOf ρ * u))
      = fun u : ℝ => (((g u * (Real.exp (α * u) * Real.cos (s * u)) : ℝ)) : ℂ)
          + Complex.I * (((g u * (Real.exp (α * u) * Real.sin (s * u)) : ℝ)) : ℂ) from
    funext fun u => sampleTest_mul_exp g t s α ρ hre him u]
  rw [integral_ofReal_add_I hF hG, integral_exp_cos hg hgc heven,
    integral_exp_sin hg hgc heven]

/-! ## The pole coordinate -/

/-- The integrand identity behind the pole evaluation. -/
theorem sampleTest_pole_integrand (g : ℝ → ℝ) (t s : ℝ) (u : ℝ) :
    sampleTest g t s u * Complex.exp (Complex.I * (Complex.I / 2) * u)
        + sampleTest g t s u * Complex.exp (Complex.I * (-Complex.I / 2) * u)
      = ((g u * (2 * Real.cosh (u / 2) * Real.cos ((s - t) * u)) : ℝ) : ℂ)
        + Complex.I * ((g u * (2 * Real.cosh (u / 2) * Real.sin ((s - t) * u)) : ℝ) : ℂ) := by
  have e1 : Complex.I * (Complex.I / 2) * u = ((-(u / 2) : ℝ) : ℂ) := by
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (u / 2 : ℂ) * h
  have e2 : Complex.I * (-Complex.I / 2) * u = (((u / 2) : ℝ) : ℂ) := by
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (-(u / 2) : ℂ) * h
  have hexp : Complex.exp (Complex.I * (((s - t) * u : ℝ) : ℂ))
      = ((Real.cos ((s - t) * u) : ℝ) : ℂ) + ((Real.sin ((s - t) * u) : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hC : ((Real.exp (-(u / 2)) : ℝ) : ℂ) + ((Real.exp (u / 2) : ℝ) : ℂ)
      = 2 * ((Real.cosh (u / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    norm_cast
    rw [Real.cosh_eq]; ring
  rw [e1, e2, sampleTest, ← Complex.ofReal_exp, ← Complex.ofReal_exp, hexp]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination ((g u : ℂ) * ((Real.cos ((s - t) * u) : ℂ)
    + (Real.sin ((s - t) * u) : ℂ) * Complex.I)) * hC

/-- **The pole evaluation.**  For the twisted sample family the two pole terms of
the literal explicit formula combine into `2 (Ec(s) + Os(s))`, a real number: the
even and odd `t`-modulated pole responses. -/
theorem poleTerm_sampleTest {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    poleTerm (sampleTest g t s)
      = ((2 * (poleEvenResp g t s + poleOddResp g t s) : ℝ) : ℂ) := by
  have hF : Integrable (fun u : ℝ => g u * (2 * Real.cosh (u / 2) * Real.cos ((s - t) * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hG : Integrable (fun u : ℝ => g u * (2 * Real.cosh (u / 2) * Real.sin ((s - t) * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hFa : Integrable (fun u : ℝ =>
      g u * (2 * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u)))) :=
    taper_integrable hg hgc (by fun_prop)
  have hFb : Integrable (fun u : ℝ =>
      g u * (2 * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u)))) :=
    taper_integrable hg hgc (by fun_prop)
  have hzeroG : ∫ u : ℝ, g u * (2 * Real.cosh (u / 2) * Real.sin ((s - t) * u)) = 0 := by
    apply integral_odd_zero
    intro u
    rw [heven u, show -u / 2 = -(u / 2) by ring, Real.cosh_neg,
      show (s - t) * -u = -((s - t) * u) by ring, Real.sin_neg]
    ring
  have hFsplit : (fun u : ℝ => g u * (2 * Real.cosh (u / 2) * Real.cos ((s - t) * u)))
      = fun u : ℝ => g u * (2 * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u)))
        + g u * (2 * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))) := by
    funext u
    rw [show (s - t) * u = s * u - t * u by ring, Real.cos_sub]
    ring
  have hint : ∫ u : ℝ, g u * (2 * Real.cosh (u / 2) * Real.cos ((s - t) * u))
      = 2 * (poleEvenResp g t s + poleOddResp g t s) := by
    rw [hFsplit, integral_add hFa hFb, poleEvenResp, poleOddResp]
    rw [show (fun u : ℝ => g u * (2 * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))))
        = fun u : ℝ => 2 * (g u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))) by
      funext u; ring]
    rw [show (fun u : ℝ => g u * (2 * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))))
        = fun u : ℝ => 2 * (g u * (Real.cosh (u / 2) * Real.sin (t * u) * Real.sin (s * u))) by
      funext u; ring]
    rw [integral_const_mul, integral_const_mul]
    ring
  rw [poleTerm, paperFT, paperFT, ← integral_add]
  · rw [show (fun u : ℝ => sampleTest g t s u * Complex.exp (Complex.I * (Complex.I / 2) * u)
          + sampleTest g t s u * Complex.exp (Complex.I * (-Complex.I / 2) * u))
        = fun u : ℝ => (((g u * (2 * Real.cosh (u / 2) * Real.cos ((s - t) * u)) : ℝ)) : ℂ)
            + Complex.I * (((g u * (2 * Real.cosh (u / 2) * Real.sin ((s - t) * u)) : ℝ)) : ℂ) from
      funext (sampleTest_pole_integrand g t s)]
    rw [integral_ofReal_add_I hF hG, hzeroG, hint]
    simp
  · have : Integrable (fun u : ℝ =>
        sampleTest g t s u * Complex.exp (Complex.I * (Complex.I / 2) * u)) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((Complex.continuous_ofReal.comp hg).mul (by fun_prop)).mul (by fun_prop)
      · exact (sampleTest_hasCompactSupport hgc t s).mul_right
    exact this
  · have : Integrable (fun u : ℝ =>
        sampleTest g t s u * Complex.exp (Complex.I * (-Complex.I / 2) * u)) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((Complex.continuous_ofReal.comp hg).mul (by fun_prop)).mul (by fun_prop)
      · exact (sampleTest_hasCompactSupport hgc t s).mul_right
    exact this

/-! ## The four-sample packaging in parity coordinates -/

/-- The four literal members of the sample family, at `r, -r, 2r, -2r`. -/
def sampleFam (g : ℝ → ℝ) (t r : ℝ) : Fin 4 → ℝ → ℂ :=
  ![sampleTest g t r, sampleTest g t (-r), sampleTest g t (2 * r), sampleTest g t (-(2 * r))]

/-- An even-parity four-sample pattern: equal at `±r` and at `±2r`. -/
def evenPattern (a₁ a₂ : ℝ) : Fin 4 → ℝ := ![a₁, a₁, a₂, a₂]

/-- An odd-parity four-sample pattern: sign-flipped at `-r` and `-2r`. -/
def oddPattern (b₁ b₂ : ℝ) : Fin 4 → ℝ := ![b₁, -b₁, b₂, -b₂]

/-- The target parity vector `evenVec + oddVec` at height `α`. -/
def targetParityVec (g : ℝ → ℝ) (α r : ℝ) : Fin 4 → ℝ :=
  evenPattern (evenResp g α r) (evenResp g α (2 * r))
    + oddPattern (oddResp g α r) (oddResp g α (2 * r))

/-- The (`t`-modulated) pole parity vector. -/
def poleParityVec (g : ℝ → ℝ) (t r : ℝ) : Fin 4 → ℝ :=
  evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r))
    + oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r))

/-- The two-dimensional pole nuisance space of the literal explicit formula. -/
def poleSpace (g : ℝ → ℝ) (t r : ℝ) : Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ {evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r)),
    oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r))}

theorem sampleFam_apply (g : ℝ → ℝ) (t r : ℝ) (i : Fin 4) :
    sampleFam g t r i
      = sampleTest g t (![r, -r, 2 * r, -(2 * r)] i) := by
  fin_cases i <;> rfl

theorem sampleFam_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (t r : ℝ) (i : Fin 4) :
    ContDiff ℝ 2 (sampleFam g t r i) := by
  rw [sampleFam_apply]; exact sampleTest_contDiff hg _ _

theorem sampleFam_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) (t r : ℝ) (i : Fin 4) :
    HasCompactSupport (sampleFam g t r i) := by
  rw [sampleFam_apply]; exact sampleTest_hasCompactSupport hg _ _

theorem reim_ofReal (x : ℝ) : reim ((x : ℝ) : ℂ) = x := by simp [reim]

/-- **`literalWeilParityCoordinateIdentification`.**  For an actual zero
`ρ* = 1/2 + α + it` of the configuration, the target coordinate of the literal
explicit formula, read through the parity functional on the four-member sample
family, is exactly the multiplicity times the parity pair of the taper at height
`α`. -/
theorem literalWeilParityCoordinateIdentification {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {α t : ℝ} {ρstar : Zeros}
    (hre : (ρstar : ℂ).re = 1 / 2 + α) (him : (ρstar : ℂ).im = t) (r : ℝ) :
    targetVec (sampleFam g t r) ρstar
      = ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g α r := by
  funext i
  have key : ∀ s : ℝ, reim (zeroTerm (sampleTest g t s) ρstar)
      = ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) * (evenResp g α s + oddResp g α s) := by
    intro s
    rw [zeroTerm, paperFT_sampleTest_zero hg hgc heven hre him s]
    have : (((Zeta23.zetaZeroConfig).mult ρstar : ℕ) : ℂ)
        = ((((Zeta23.zetaZeroConfig).mult ρstar : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, reim_real_mul]
    congr 1
    simp [reim]
  have hE := evenResp_neg g α r
  have hE2 := evenResp_neg g α (2 * r)
  have hO := oddResp_neg g α r
  have hO2 := oddResp_neg g α (2 * r)
  fin_cases i
  · show reim (zeroTerm (sampleTest g t r) ρstar) = _
    rw [key]
    show _ = _ * (evenPattern (evenResp g α r) (evenResp g α (2 * r)) 0
      + oddPattern (oddResp g α r) (oddResp g α (2 * r)) 0)
    simp [evenPattern, oddPattern]
  · show reim (zeroTerm (sampleTest g t (-r)) ρstar) = _
    rw [key, hE, hO]
    show _ = _ * (evenPattern (evenResp g α r) (evenResp g α (2 * r)) 1
      + oddPattern (oddResp g α r) (oddResp g α (2 * r)) 1)
    simp [evenPattern, oddPattern]
  · show reim (zeroTerm (sampleTest g t (2 * r)) ρstar) = _
    rw [key]
    show _ = _ * (evenPattern (evenResp g α r) (evenResp g α (2 * r)) 2
      + oddPattern (oddResp g α r) (oddResp g α (2 * r)) 2)
    simp [evenPattern, oddPattern]
  · show reim (zeroTerm (sampleTest g t (-(2 * r))) ρstar) = _
    rw [key, hE2, hO2]
    show _ = _ * (evenPattern (evenResp g α r) (evenResp g α (2 * r)) 3
      + oddPattern (oddResp g α r) (oddResp g α (2 * r)) 3)
    simp [evenPattern, oddPattern]

/-- **The pole coordinate of the literal explicit formula is the pole parity
vector.**  Its two channels are the `t`-modulated even and odd pole responses. -/
theorem poleVec_sampleFam {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    poleVec (sampleFam g t r) = (-2 : ℝ) • poleParityVec g t r := by
  funext i
  have key : ∀ s : ℝ, reim (poleTerm (sampleTest g t s))
      = 2 * (poleEvenResp g t s + poleOddResp g t s) := by
    intro s
    rw [poleTerm_sampleTest hg hgc heven, reim_ofReal]
  have hE := poleEvenResp_neg g t r
  have hE2 := poleEvenResp_neg g t (2 * r)
  have hO := poleOddResp_neg g t r
  have hO2 := poleOddResp_neg g t (2 * r)
  fin_cases i
  · show -reim (poleTerm (sampleTest g t r)) = _
    rw [key]
    show _ = _ * (evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r)) 0
      + oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r)) 0)
    simp [evenPattern, oddPattern]
  · show -reim (poleTerm (sampleTest g t (-r))) = _
    rw [key, hE, hO]
    show _ = _ * (evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r)) 1
      + oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r)) 1)
    simp [evenPattern, oddPattern]
  · show -reim (poleTerm (sampleTest g t (2 * r))) = _
    rw [key]
    show _ = _ * (evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r)) 2
      + oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r)) 2)
    simp [evenPattern, oddPattern]
  · show -reim (poleTerm (sampleTest g t (-(2 * r)))) = _
    rw [key, hE2, hO2]
    show _ = _ * (evenPattern (poleEvenResp g t r) (poleEvenResp g t (2 * r)) 3
      + oddPattern (poleOddResp g t r) (poleOddResp g t (2 * r)) 3)
    simp [evenPattern, oddPattern]

theorem poleParityVec_mem (g : ℝ → ℝ) (t r : ℝ) : poleParityVec g t r ∈ poleSpace g t r :=
  Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

/-- **The pole coordinate lies in the pole space.** -/
theorem poleVec_mem_poleSpace {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    poleVec (sampleFam g t r) ∈ poleSpace g t r := by
  rw [poleVec_sampleFam hg hgc heven]
  exact Submodule.smul_mem _ _ (poleParityVec_mem g t r)

/-- **`literalWeilFourSampleParityBalance`.**  The literal zeta Weil explicit
formula, evaluated on the four-member sample family attached to a zero
`ρ* = 1/2 + α + it`, supplies a four-sample balance relation whose target
coordinate is the parity pair at height `α` and whose pole coordinate lies in the
two-dimensional pole space. -/
theorem literalWeilFourSampleParityBalance {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {α t : ℝ} {ρstar : Zeros}
    (hre : (ρstar : ℂ).re = 1 / 2 + α) (him : (ρstar : ℂ).im = t) (r : ℝ) :
    ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g α r
        + otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
        + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0
      ∧ poleVec (sampleFam g t r) ∈ poleSpace g t r := by
  have hcont : Continuous g := hgs.continuous
  refine ⟨?_, poleVec_mem_poleSpace hcont hgc heven t r⟩
  have hbal := literalWeilFourSampleBalance (kFam := sampleFam g t r)
    (fun i => sampleFam_contDiff hgs t r i) (fun i => sampleFam_hasCompactSupport hgc t r i) ρstar
  rwa [literalWeilParityCoordinateIdentification hcont hgc heven hre him r] at hbal

/-! ## The parity quotient -/

/-- The parity quotient: four samples modulo the two pole directions. -/
abbrev ParityQuotient (g : ℝ → ℝ) (t r : ℝ) : Type := (Fin 4 → ℝ) ⧸ poleSpace g t r

/-- The class of a four-sample vector in the parity quotient. -/
def qcls (g : ℝ → ℝ) (t r : ℝ) (v : Fin 4 → ℝ) : ParityQuotient g t r :=
  Submodule.Quotient.mk v

theorem qcls_add (g : ℝ → ℝ) (t r : ℝ) (v w : Fin 4 → ℝ) :
    qcls g t r (v + w) = qcls g t r v + qcls g t r w := rfl

theorem qcls_smul (g : ℝ → ℝ) (t r : ℝ) (c : ℝ) (v : Fin 4 → ℝ) :
    qcls g t r (c • v) = c • qcls g t r v := rfl

theorem qcls_eq_zero_iff (g : ℝ → ℝ) (t r : ℝ) (v : Fin 4 → ℝ) :
    qcls g t r v = 0 ↔ v ∈ poleSpace g t r :=
  Submodule.Quotient.mk_eq_zero _

/-- **`Q_pole = 0`.** -/
theorem qcls_poleVec {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    qcls g t r (poleVec (sampleFam g t r)) = 0 :=
  (qcls_eq_zero_iff g t r _).2 (poleVec_mem_poleSpace hg hgc heven t r)

/-- **`Q_target ≠ 0` from the two parity minors.**  If the even minor and the odd
minor of the target-versus-pole pair are nonzero, the target parity vector has
nonzero class in the parity quotient. -/
theorem target_quotient_ne_zero {g : ℝ → ℝ} {α t r : ℝ}
    (hEvenMinor : evenResp g α r * poleEvenResp g t (2 * r)
      - evenResp g α (2 * r) * poleEvenResp g t r ≠ 0) :
    qcls g t r (targetParityVec g α r) ≠ 0 := by
  intro hzero
  rw [qcls_eq_zero_iff, poleSpace, Submodule.mem_span_pair] at hzero
  obtain ⟨c₁, c₂, hc⟩ := hzero
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  have e2 := congrFun hc 2
  have e3 := congrFun hc 3
  simp only [targetParityVec, evenPattern, oddPattern, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at e0 e1 e2 e3
  have hA1 : evenResp g α r = c₁ * poleEvenResp g t r := by linarith
  have hA2 : evenResp g α (2 * r) = c₁ * poleEvenResp g t (2 * r) := by linarith
  apply hEvenMinor
  rw [hA1, hA2]; ring

/-- **`Q_target ≠ 0` from the odd parity minor**, the mirror of
`target_quotient_ne_zero`: either channel alone suffices. -/
theorem target_quotient_ne_zero_odd {g : ℝ → ℝ} {α t r : ℝ}
    (hOddMinor : oddResp g α r * poleOddResp g t (2 * r)
      - oddResp g α (2 * r) * poleOddResp g t r ≠ 0) :
    qcls g t r (targetParityVec g α r) ≠ 0 := by
  intro hzero
  rw [qcls_eq_zero_iff, poleSpace, Submodule.mem_span_pair] at hzero
  obtain ⟨c₁, c₂, hc⟩ := hzero
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  have e2 := congrFun hc 2
  have e3 := congrFun hc 3
  simp only [targetParityVec, evenPattern, oddPattern, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at e0 e1 e2 e3
  have hB1 : oddResp g α r = c₂ * poleOddResp g t r := by linarith
  have hB2 : oddResp g α (2 * r) = c₂ * poleOddResp g t (2 * r) := by linarith
  apply hOddMinor
  rw [hB1, hB2]; ring

/-- **Pure quotient bookkeeping**: a balance relation whose pole part lies in the
pole space descends to `Q_target = -(Q_other + Q_prime + Q_Γ)`. -/
theorem parityQuotientBalance {g : ℝ → ℝ} {t r : ℝ}
    {vTarget vOther vPrime vGamma vPole : Fin 4 → ℝ}
    (hPole : vPole ∈ poleSpace g t r)
    (hbalance : vTarget + vOther + vPrime + vGamma + vPole = 0) :
    qcls g t r vPole = 0
      ∧ qcls g t r vTarget = -qcls g t r (vOther + vPrime + vGamma)
      ∧ (qcls g t r vTarget ≠ 0 → qcls g t r (vOther + vPrime + vGamma) ≠ 0) := by
  have hp0 : qcls g t r vPole = 0 := (qcls_eq_zero_iff g t r _).2 hPole
  have hsum : qcls g t r (vTarget + (vOther + vPrime + vGamma) + vPole) = 0 := by
    have hz : vTarget + (vOther + vPrime + vGamma) + vPole = 0 := by
      rw [← hbalance]; abel
    rw [hz]
    exact (qcls_eq_zero_iff g t r _).2 (Submodule.zero_mem _)
  rw [qcls_add, qcls_add, hp0, add_zero] at hsum
  refine ⟨hp0, by linear_combination (norm := abel) hsum, fun hne hzero => ?_⟩
  apply hne
  rw [hzero, add_zero] at hsum
  exact hsum

/-- **`literalWeilParityQuotientDecompositionUnconditional`.**  For an actual zero
`ρ*` of the configuration with `ρ* = 1/2 + α + it`, no balance relation is
assumed: the literal zeta Weil explicit formula supplies it.  Modulo the pole
space, the target class equals minus the class of the other-zeros, prime and
gamma contributions, and — as soon as the two parity minors of the
target-versus-pole pair are nonzero — that class is itself nonzero. -/
theorem literalWeilParityQuotientDecompositionUnconditional {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    {α t : ℝ} {ρstar : Zeros} (hre : (ρstar : ℂ).re = 1 / 2 + α) (him : (ρstar : ℂ).im = t)
    {r : ℝ}
    (hEvenMinor : evenResp g α r * poleEvenResp g t (2 * r)
      - evenResp g α (2 * r) * poleEvenResp g t r ≠ 0)
    (hmult : ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) ≠ 0) :
    qcls g t r (poleVec (sampleFam g t r)) = 0
      ∧ qcls g t r (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g α r)
          = -qcls g t r (otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
              + gammaVec (sampleFam g t r))
      ∧ qcls g t r (otherVec (sampleFam g t r) ρstar + primeVec (sampleFam g t r)
          + gammaVec (sampleFam g t r)) ≠ 0 := by
  obtain ⟨hbal, hmem⟩ := literalWeilFourSampleParityBalance hgs hgc heven hre him r
  obtain ⟨h1, h2, h3⟩ := parityQuotientBalance hmem hbal
  refine ⟨h1, h2, h3 ?_⟩
  rw [qcls_smul]
  intro hzero
  rcases smul_eq_zero.mp hzero with h | h
  · exact hmult h
  · exact target_quotient_ne_zero hEvenMinor h

end LiteralWeilParityBalance
end Zeta23Bridge
