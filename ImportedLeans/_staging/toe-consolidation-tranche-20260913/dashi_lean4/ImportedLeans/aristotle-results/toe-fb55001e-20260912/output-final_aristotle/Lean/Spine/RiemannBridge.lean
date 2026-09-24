/-
# A narrow bridge from the generic two-regime envelope to the RH analytic lane

This file connects the *generic* results of `Spine.TwoRegime` and
`Spine.AnchoredGram` to the analytic interfaces declared (as interfaces) in the
Agda `DASHI.Analysis.Riemann*` bundle.  Everything here is Mathlib-only real
analysis and elementary arithmetic.  **No statement about the zeros of the zeta
function is made, assumed, or proved anywhere in this file**, and no analytic
hypothesis of the Agda lane is discharged silently: each one that is used
appears as an explicit hypothesis of the Lean theorem that uses it.

## What the Agda source declares, and what is bridged here

The Agda modules consulted are

* `DASHI.Analysis.RiemannAnalyticSubstrate` — a tower of *records* (complex
  analytic carrier, Gamma/Mellin layer, zeta half-plane layer, completed zeta)
  whose fields are abstract `Set`s, with `RiemannHypothesisFor` a predicate on
  an inhabitant.  No inhabitant is built there or here.
* `DASHI.Analysis.RiemannPhiCoshCoercivityReductionExact` — the taper-coercivity
  ledger, whose boundary record records
  `coshInequalityFormalizedInDashiHere = false` and
  `sourceSecondMomentBoundInstantiatedHere = false`.
* `DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact` — the Poisson
  extension / finite-retention ledger, with
  `analyticCoshCoercivityProvedHere = false`.
* `DASHI.Analysis.RiemannCenteredGridRetentionExact` — the centred grid tail
  ledger.
* `DASHI.Analysis.RiemannComplexPoissonChannelSplitExact` — the exact signed
  coordinate algebra of the bilinear (transverse-blind) and Hermitian
  (transverse-seeing) channels.
* `DASHI.Analysis.RiemannMixedKernelEnvelopeExact` — the kernel-envelope ledger,
  with `pairwiseComplexPhiDecayProvedHere = false` and
  `zeroPairEnvelopeSummedHere = false`.

Three things are established below.

1. **The ℕ ledgers carry no analytic content by themselves.**  Every ledger in
   that bundle is a conjunction of `ℕ`-equations of the form `a + slack = b`,
   which is exactly `a ≤ b` (`Spine.RiemannBridge.nat_margin_iff_le`); and each
   ledger is inhabited with all fields zero
   (`Spine.RiemannBridge.ledgers_have_trivial_inhabitants`).  So a ledger is an
   *encoding of an inequality between nonnegative quantities*, not a theorem.
   Consequently the honest transport target is the real-valued inequality, not
   the ledger type.
2. **The real-valued content of two ledgers is proved here**, over `ℝ`, from
   inequalities rather than from `ℕ` margins: the centred-grid retention bound
   (`real_centered_grid_retention`) and the doubled-finite retention bound
   (`real_finite_retention`).
3. **The two analytic gaps flagged `false` in the Agda boundary records are
   closed as Mathlib theorems**, in the generic form in which they are stated
   there — the cosh quadratic inequality and its integrated form
   (`sq_div_two_le_cosh_sub_one`, `taper_cosh_excess_ge`), the plateau second
   moment bound (`plateau_second_moment_ge`), their combination
   (`taper_coercivity_of_plateau`), and, from `Spine.TwoRegime`, the aggregate
   kernel envelope bound over an off-diagonal frequency set
   (`fourier_pair_sum_le`) and over an arithmetic grid tail
   (`grid_tail_sum_le`).

## What is *not* bridged

* No type-level transport into the Agda records is possible or claimed: their
  analytic fields are abstract `Set`s with no defining equation, so an
  inhabitant of `ComplexPhiKernelEnvelopeProducer` (say) can be built with every
  such field set to the unit type — `producer_socket_is_contentless` records
  exactly that.  What the source supports is a **shared estimate**, reused here,
  not a transport of types.
* The identification of the source's `S`/`H` kernels with a Fourier transform
  (`complexSHToPhiIdentificationProvedHere = false`) is *not* proved: it enters
  `fourier_pair_sum_le` as the hypothesis `hid`.
* The two-regime envelope does **not** discharge the grid tail-domination field:
  on an arithmetic grid the envelope's own bound is harmonic and therefore not
  summable (`grid_envelope_not_summable`).  This is an honest negative.
* Nothing here bears on Yang–Mills or Navier–Stokes, and nothing here asserts
  the Riemann hypothesis or any partial result about zeta zeros.
-/
import Mathlib
import Spine.TwoRegime
import Spine.AnchoredGram

open MeasureTheory Real Finset
open scoped FourierTransform RealInnerProductSpace

namespace Spine
namespace RiemannBridge

/-! ## 1. The `ℕ` ledgers of the Agda bundle, and what they do and do not say -/

/-- In `ℕ`, "there is a margin `m` with `a + m = b`" is *exactly* `a ≤ b`.  Every
identity in the Agda ledgers has this shape, so the ledgers are an encoding of
order relations between nonnegative quantities. -/
theorem nat_margin_iff_le (a b : ℕ) : (∃ m : ℕ, a + m = b) ↔ a ≤ b :=
  ⟨fun ⟨m, hm⟩ => hm ▸ Nat.le_add_right a m, fun h => ⟨b - a, by omega⟩⟩

/-- Mirror of `DASHI.Analysis.RiemannPhiCoshCoercivityReductionExact.PhiCoshCoercivityLedger`:
`2·(M₂)·α² + slack = excess` with the second moment written as a successor. -/
structure CoshCoercivityLedger where
  alphaSq : ℕ
  secondMomentPred : ℕ
  excess : ℕ
  slack : ℕ
  identity : 2 * (secondMomentPred + 1) * alphaSq + slack = excess

/-- Mirror of `DASHI.Analysis.RiemannCenteredGridRetentionExact.CenteredImaginaryGridLedger`
together with its tail-domination field. -/
structure CenteredGridLedger where
  finiteEnergy : ℕ
  omittedTail : ℕ
  fullEnergy : ℕ
  retainedMargin : ℕ
  reflectionDecomposition : fullEnergy = 2 * (finiteEnergy + omittedTail)
  tailDominated : omittedTail + retainedMargin = finiteEnergy

/-- Mirror of `DASHI.Analysis.RiemannMixedKernelEnvelopeExact.MixedKernelEnvelopeLedger`,
with the two ambient quantities of the global/pair ledgers as parameters. -/
structure MixedKernelEnvelopeLedger (mixedBudget otherDiagonal : ℕ) where
  kernelEnvelope : ℕ
  envelopeSlack : ℕ
  nonTargetMargin : ℕ
  mixedInsideEnvelope : mixedBudget + envelopeSlack = kernelEnvelope
  envelopeBelowOtherDiagonal : kernelEnvelope + nonTargetMargin = otherDiagonal

/-- The Agda derivation `centeredTailDominationImpliesRetention`, re-proved in
Lean: `full = 4·tail + 2·margin`. -/
theorem centered_grid_retention (g : CenteredGridLedger) :
    g.fullEnergy = 4 * g.omittedTail + 2 * g.retainedMargin := by
  have h := g.reflectionDecomposition
  have h2 := g.tailDominated
  omega

/-- The Agda derivation `kernelEnvelopeImpliesPairAlmostOrthogonality`, re-proved
in Lean: the mixed budget stays below the other diagonal energy. -/
theorem kernel_envelope_gives_almost_orthogonality {mixedBudget otherDiagonal : ℕ}
    (e : MixedKernelEnvelopeLedger mixedBudget otherDiagonal) :
    mixedBudget + (e.envelopeSlack + e.nonTargetMargin) = otherDiagonal := by
  have h1 := e.mixedInsideEnvelope
  have h2 := e.envelopeBelowOtherDiagonal
  omega

/-- **The honest gate on the ledgers.**  Each of the three ledgers is inhabited
with every numeric field zero, so possessing a ledger implies nothing about the
analytic quantities it is meant to record; the content has to live in the
real-valued inequalities proved below. -/
theorem ledgers_have_trivial_inhabitants :
    (∃ l : CoshCoercivityLedger, l.alphaSq = 0 ∧ l.excess = 0) ∧
    (∃ g : CenteredGridLedger, g.fullEnergy = 0 ∧ g.finiteEnergy = 0) ∧
    (∃ e : MixedKernelEnvelopeLedger 0 0, e.kernelEnvelope = 0) :=
  ⟨⟨⟨0, 0, 0, 0, by norm_num⟩, rfl, rfl⟩,
   ⟨⟨0, 0, 0, 0, by norm_num, by norm_num⟩, rfl, rfl⟩,
   ⟨⟨0, 0, 0, by norm_num, by norm_num⟩, rfl⟩⟩

/-- Mirror of the abstract analytic socket
`DASHI.Analysis.RiemannMixedKernelEnvelopeExact.ComplexPhiKernelEnvelopeProducer`:
the two pairwise envelope statements and the aggregate bound are *abstract*
types with no defining equation. -/
structure AbstractEnvelopeProducer where
  PairIndex : Type
  envelope : PairIndex → ℕ
  DifferenceKernelInsideEnvelope : PairIndex → Prop
  SumKernelInsideEnvelope : PairIndex → Prop
  differenceKernelInsideEnvelope : ∀ i, DifferenceKernelInsideEnvelope i
  sumKernelInsideEnvelope : ∀ i, SumKernelInsideEnvelope i
  AggregateEnvelopeBound : Prop
  aggregateEnvelopeBound : AggregateEnvelopeBound

/-- **No type-level transport is available through the abstract socket.**  An
inhabitant of the producer record exists in which every analytic field is `True`
and the numeric data is arbitrary, so an inhabitant of the socket is not
evidence for any estimate.  Only a socket whose predicates are *pinned* to
actual inequalities — as in `fourier_pair_sum_le` below — carries content. -/
theorem producer_socket_is_contentless (I : Type) (e : I → ℕ) :
    ∃ p : AbstractEnvelopeProducer, p.PairIndex = I ∧ HEq p.envelope e :=
  ⟨⟨I, e, fun _ => True, fun _ => True, fun _ => trivial, fun _ => trivial, True, trivial⟩,
    rfl, HEq.rfl⟩

/-! ## 2. The real-valued content of the retention ledgers

Over `ℝ` a "margin" field becomes an inequality, and the two retention
derivations become quantitative statements about nonnegative energies. -/

/-- Real form of `RiemannCenteredGridRetentionExact`: if the full imaginary
channel energy decomposes as `2(fin + tail)` and the omitted tail is dominated
by the retained finite part, then the finite one-sided grid retains at least a
quarter of the full transverse energy. -/
theorem real_centered_grid_retention {full fin tail : ℝ}
    (hdecomp : full = 2 * (fin + tail)) (hdom : tail ≤ fin) :
    full / 4 ≤ fin := by
  rw [hdecomp]; linarith

/-- Real form of `RiemannComplexPoissonFiniteRetentionExact`: from the coercive
full-grid identity (`defect + slack = fullExcess`, `slack ≥ 0`), the tail split
(`fullExcess = finiteExcess + tailLoss`) and tail domination
(`tailLoss ≤ finiteExcess`), the weighted transverse defect is at most twice the
*finite* grid excess. -/
theorem real_finite_retention {defect slack fullExcess finiteExcess tailLoss : ℝ}
    (hslack : 0 ≤ slack) (hcoercive : defect + slack = fullExcess)
    (hsplit : fullExcess = finiteExcess + tailLoss) (hdom : tailLoss ≤ finiteExcess) :
    defect ≤ 2 * finiteExcess := by
  linarith

/-! ## 3. Taper coercivity: the analytic gap the Agda boundary marks `false`

`RiemannPhiCoshCoercivityReductionExact` states the mechanism

    Φ(-2iα) - Φ(0) = ∫ φ(u)² (cosh(2αu) - 1) du ≥ 2α² ∫ u² φ(u)² du,

and records `coshInequalityFormalizedInDashiHere = false`,
`sourceSecondMomentBoundInstantiatedHere = false`.  Both are proved here as
ordinary real analysis, with integrability as an explicit hypothesis. -/

/-- The quadratic lower bound for `cosh`: `x²/2 ≤ cosh x - 1`. -/
theorem sq_div_two_le_cosh_sub_one (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ Real.sinh t ^ 2 := by
    intro t ht
    have := Real.self_le_sinh_iff.mpr ht
    nlinarith [this, ht]
  have habs : (|x| / 2) ^ 2 ≤ Real.sinh (|x| / 2) ^ 2 := hkey _ (by positivity)
  have hc : Real.cosh x = 2 * Real.sinh (x / 2) ^ 2 + 1 := by
    have h := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    rw [h, Real.cosh_sq]; ring
  have hsq : Real.sinh (|x| / 2) ^ 2 = Real.sinh (x / 2) ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
  rw [hsq, show (|x| / 2) ^ 2 = (x / 2) ^ 2 by rw [div_pow, div_pow, sq_abs]] at habs
  rw [hc]; nlinarith [habs]

/-- **The integrated cosh coercivity.**  For any real taper `φ` whose two
relevant integrands are integrable,

    2α² ∫ u² φ(u)² du ≤ ∫ φ(u)² (cosh(2αu) - 1) du.

This is the inequality the Agda module calls `coshMinusOneQuadraticLowerBound`,
with the coercive weight `2·M₂` visible on the left. -/
theorem taper_cosh_excess_ge (phi : ℝ → ℝ) (a : ℝ)
    (hexc : Integrable (fun u => phi u ^ 2 * (Real.cosh (2 * a * u) - 1)))
    (hmom : Integrable (fun u => u ^ 2 * phi u ^ 2)) :
    2 * a ^ 2 * ∫ u, u ^ 2 * phi u ^ 2 ≤ ∫ u, phi u ^ 2 * (Real.cosh (2 * a * u) - 1) := by
  have hpt : ∀ u : ℝ,
      2 * a ^ 2 * (u ^ 2 * phi u ^ 2) ≤ phi u ^ 2 * (Real.cosh (2 * a * u) - 1) := by
    intro u
    have h := sq_div_two_le_cosh_sub_one (2 * a * u)
    nlinarith [h, sq_nonneg (phi u)]
  have := integral_mono (hmom.const_mul (2 * a ^ 2)) hexc hpt
  rwa [integral_const_mul] at this

/-- **The plateau second-moment bound.**  If the taper is identically `1` on the
plateau `|u| ≤ R`, its second moment is at least `2R³/3`.  This is the
`TaperPlateauSecondMomentBridge` computation `symmetricUSquaredIntegralComputed`,
which the Agda module leaves to the analytic producer. -/
theorem plateau_second_moment_ge (phi : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hplateau : ∀ u : ℝ, |u| ≤ R → phi u = 1)
    (hmom : Integrable (fun u => u ^ 2 * phi u ^ 2)) :
    2 * R ^ 3 / 3 ≤ ∫ u, u ^ 2 * phi u ^ 2 := by
  have hnonneg : 0 ≤ᵐ[volume] fun u : ℝ => u ^ 2 * phi u ^ 2 :=
    Filter.Eventually.of_forall fun u => by positivity
  have hle : ∫ u in Set.Icc (-R) R, u ^ 2 * phi u ^ 2 ≤ ∫ u, u ^ 2 * phi u ^ 2 :=
    setIntegral_le_integral hmom hnonneg
  have heq : ∫ u in Set.Icc (-R) R, u ^ 2 * phi u ^ 2 = ∫ u in Set.Icc (-R) R, u ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    have hu1 : phi u = 1 := hplateau u (abs_le.mpr ⟨hu.1, hu.2⟩)
    simp [hu1]
  have hcomp : ∫ u in Set.Icc (-R) R, (u : ℝ) ^ 2 = 2 * R ^ 3 / 3 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), integral_pow]
    ring
  rw [heq, hcomp] at hle
  exact hle

/-- **Taper coercivity with an explicit positive weight.**  Combining the two
previous results: a taper with plateau radius `R` has

    (4R³/3) · α² ≤ ∫ φ(u)² (cosh(2αu) - 1) du,

so the coercive weight `c_φ = 2·M₂` of the Agda ledger may be taken to be
`4R³/3`, which is strictly positive as soon as `R > 0`. -/
theorem taper_coercivity_of_plateau (phi : ℝ → ℝ) (a R : ℝ) (hR : 0 ≤ R)
    (hplateau : ∀ u : ℝ, |u| ≤ R → phi u = 1)
    (hexc : Integrable (fun u => phi u ^ 2 * (Real.cosh (2 * a * u) - 1)))
    (hmom : Integrable (fun u => u ^ 2 * phi u ^ 2)) :
    4 * R ^ 3 / 3 * a ^ 2 ≤ ∫ u, phi u ^ 2 * (Real.cosh (2 * a * u) - 1) := by
  have h1 := taper_cosh_excess_ge phi a hexc hmom
  have h2 := plateau_second_moment_ge phi R hR hplateau hmom
  nlinarith [sq_nonneg a, h1, h2]

/-- The coercive weight is strictly positive exactly when the plateau is
nondegenerate; with `R = 0` the bound above is vacuous. -/
theorem coercive_weight_pos {R : ℝ} (hR : 0 < R) : 0 < 4 * R ^ 3 / 3 := by positivity

/-! ## 4. The kernel envelope: `Spine.TwoRegime` applied to an off-diagonal
frequency set

`RiemannMixedKernelEnvelopeExact` needs a pairwise envelope for the complex
kernels and an aggregate sum of that envelope over off-diagonal pairs, and marks
both as unproved there.  The generic two-regime theorem supplies exactly this,
*given* an identification of the kernel values with a Fourier transform — which
is the field the same module marks `complexSHToPhiIdentificationProvedHere =
false`, and which is therefore carried as the hypothesis `hid`. -/

/-- The two-regime envelope vanishes at the origin, which is why the aggregate
bound below is stated for an off-diagonal frequency set.  (This matches the
channel-split algebra: it is exactly the diagonal pair whose ordinate difference
is zero.) -/
theorem envelope_zero {K₀ K₁ : ℝ} (hK₀ : 0 ≤ K₀) : TwoRegime.envelope K₀ K₁ 0 = 0 := by
  simp [TwoRegime.envelope, min_eq_right hK₀]

/-- **The aggregate kernel envelope bound.**  Let `f` be an integrable,
differentiable taper with integrable derivative, and let `S` be a finite set of
*nonzero* frequencies with at most `N` members in each unit window and all of
modulus `< M`.  If the kernel values `k ξ` are the moduli of `𝓕 f` at those
frequencies (hypothesis `hid`; not proved here), then

    ∑_{ξ ∈ S} k ξ ≤ N‖f‖₁ + N (‖f'‖₁/2π) ∑_{m=1}^{M-1} 1/m.

Only local counts are used: no minimum separation between frequencies is
assumed. -/
theorem fourier_pair_sum_le {f : ℝ → ℂ} (hf : Integrable f) (hd : Differentiable ℝ f)
    (hf' : Integrable (deriv f)) (k : ℝ → ℝ) (S : Finset ℝ) (N M : ℕ)
    (hS0 : (0 : ℝ) ∉ S)
    (hid : ∀ ξ ∈ S, k ξ = ‖𝓕 f ξ‖)
    (hM : ∀ ξ ∈ S, |ξ| < M)
    (hcount : ∀ m : ℕ, ((S.filter (fun ξ => ⌊|ξ|⌋₊ = m)).card : ℝ) ≤ N) :
    ∑ ξ ∈ S, k ξ ≤
      N * (∫ x, ‖f x‖) + N * ((∫ x, ‖deriv f x‖) / (2 * π)) *
        ∑ m ∈ Finset.Ico 1 M, (1 : ℝ) / m := by
  set K₀ : ℝ := ∫ x, ‖f x‖ with hK₀def
  set K₁ : ℝ := (∫ x, ‖deriv f x‖) / (2 * π) with hK₁def
  have hK₀ : 0 ≤ K₀ := integral_nonneg fun x => norm_nonneg _
  have hK₁ : 0 ≤ K₁ := by
    have : (0 : ℝ) ≤ ∫ x, ‖deriv f x‖ := integral_nonneg fun x => norm_nonneg _
    have hpi := Real.pi_pos
    positivity
  have hstep : ∀ ξ ∈ S, k ξ ≤ TwoRegime.envelope K₀ K₁ ξ := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := fun h => hS0 (h ▸ hξ)
    have h := TwoRegime.norm_fourier_le_envelope hf hd hf' hξ0
    rw [hid ξ hξ]
    refine le_trans h (le_of_eq ?_)
    unfold TwoRegime.envelope
    congr 1
    rw [hK₁def, div_div]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  exact TwoRegime.sum_envelope_le hK₀ hK₁ S N M hM hcount

/-! ## 5. The grid tail, and the honest negative -/

/-- **The grid tail bound.**  On the arithmetic grid `ξ_k = k·h` with spacing
`h > 0`, the two-regime envelope over the tail `d ≤ k < M` is at most
`(K₁/h)·∑_{k=d}^{M-1} 1/k`. -/
theorem grid_tail_sum_le {K₀ K₁ h : ℝ} (hh : 0 < h) (d M : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.Ico d M, TwoRegime.envelope K₀ K₁ (k * h)
      ≤ (K₁ / h) * ∑ k ∈ Finset.Ico d M, (1 : ℝ) / k := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk1 : 1 ≤ k := le_trans hd (Finset.mem_Ico.mp hk).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have habs : |(k : ℝ) * h| = (k : ℝ) * h := abs_of_pos (by positivity)
  refine le_trans (TwoRegime.envelope_le_right _ _ _) (le_of_eq ?_)
  rw [habs]
  field_simp

/-- **The honest negative.**  The two-regime envelope alone does *not* supply the
Agda lane's `positiveLatticeTailBound`: along an arithmetic grid its own bound is
harmonic, hence not summable, so the omitted tail cannot be made small by this
estimate.  Some further input (a genuine decay rate, or a zero-counting bound) is
required. -/
theorem grid_envelope_not_summable {K₁ h : ℝ} (hK₁ : 0 < K₁) (hh : 0 < h) :
    ¬ Summable (fun k : ℕ => K₁ / ((k : ℝ) * h)) := by
  intro hsum
  have : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ)) := by
    refine (hsum.mul_left (h / K₁)).congr fun k => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp
  exact Real.not_summable_one_div_natCast this

/-! ## 5b. The complex/transverse channel split, and where the envelope may be used

`RiemannComplexPoissonChannelSplitExact` proves an exact signed-coordinate
algebra: for centred coordinates `(γ, α)` the bilinear channel sees `α_i - α_j`
and the Hermitian channel `α_i + α_j`, so the bilinear diagonal is
transverse-blind while the Hermitian diagonal doubles the transverse part.  That
algebra is reproved here over `ℤ` (it is pure arithmetic in the source too), and
then linked to the envelope: it is exactly on the diagonal that the ordinate
difference vanishes, and `envelope_zero` shows the two-regime envelope carries no
information there.  This is why `fourier_pair_sum_le` is restricted to a
frequency set avoiding `0` — the restriction is the off-diagonal restriction, not
a convenience. -/

/-- A centred complex coordinate: ordinate and transverse part. -/
structure CentredCoordinate where
  ordinate : ℤ
  transverse : ℤ

/-- The bilinear channel argument. -/
def bilinearArgument (x y : CentredCoordinate) : CentredCoordinate :=
  ⟨x.ordinate - y.ordinate, x.transverse - y.transverse⟩

/-- The Hermitian channel argument. -/
def hermitianArgument (x y : CentredCoordinate) : CentredCoordinate :=
  ⟨x.ordinate - y.ordinate, x.transverse + y.transverse⟩

/-- The bilinear diagonal is transverse-blind. -/
theorem bilinear_diagonal_transverse_zero (x : CentredCoordinate) :
    (bilinearArgument x x).transverse = 0 := by simp [bilinearArgument]

/-- The Hermitian diagonal doubles the transverse part. -/
theorem hermitian_diagonal_transverse_double (x : CentredCoordinate) :
    (hermitianArgument x x).transverse = 2 * x.transverse := by
  simp [hermitianArgument]; ring

/-- Both channels have vanishing ordinate difference on the diagonal — the
frequency at which the two-regime envelope degenerates. -/
theorem diagonal_ordinate_zero (x : CentredCoordinate) :
    (bilinearArgument x x).ordinate = 0 ∧ (hermitianArgument x x).ordinate = 0 := by
  constructor <;> simp [bilinearArgument, hermitianArgument]

/-- The two channels recover twice the first transverse coordinate. -/
theorem channels_recover_transverse (x y : CentredCoordinate) :
    (bilinearArgument x y).transverse + (hermitianArgument x y).transverse
      = 2 * x.transverse := by
  simp [bilinearArgument, hermitianArgument]; ring

/-! ## 5c. The Poisson extension interface

`RiemannComplexPoissonFiniteRetentionExact.ComplexPoissonStripContinuation`
declares a `continuedPoissonIdentity` field: the grid sum equals the kernel value
for arguments *in a strip*.  Over `ℝ` — that is, for real arguments and the unit
lattice — that identity is an actual theorem, recorded here; its analytic
continuation to complex arguments in a strip, which is what the record asks for,
is **not** supplied by it and is not proved here. -/

/-- Poisson summation on the unit lattice, in the form the Agda record
abstracts: for a continuous `f` with polynomial decay on both sides, the lattice
sum of `f` equals the lattice sum of `𝓕 f`. -/
theorem poisson_unit_lattice {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[Filter.cocompact ℝ] fun x => |x| ^ (-b))
    (hFf : 𝓕 f =O[Filter.cocompact ℝ] fun x => |x| ^ (-b)) :
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n := by
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay hc hb hf hFf 0
  simpa using this

/-! ## 6. Composition with the anchored Gram surplus

`Spine.AnchoredGram` gives the surplus `‖f‖²·det Gram(t)` for an anchored
family.  Composing it with a coercive lower bound on the anchor — the shape the
taper coercivity of §3 produces — gives a quantitative Gram surplus. -/

/-- If the anchor's squared length is at least `c` (for instance the coercive
weight times `α²` of §3), the anchored Gram determinant exceeds the transverse
one by at least `c · det Gram(t)`. -/
theorem det_gram_surplus_of_coercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {r : ℕ} (f t₀ : V) (t : Fin r → V) {c : ℝ}
    (hf₀ : ⟪f, t₀⟫ = 0) (hft : ∀ j, ⟪f, t j⟫ = 0) (hc : c ≤ ‖f‖ ^ 2) :
    c * (Matrix.gram ℝ t).det ≤ (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det := by
  have hdet : (0 : ℝ) ≤ (Matrix.gram ℝ t).det := (Matrix.posSemidef_gram ℝ t).det_nonneg
  have h := Spine.det_gram_anchored_ge f t₀ t hf₀ hft
  nlinarith [h, hdet, hc]

/-! ## 7. The bridge as one record

The fields are the statements themselves, so the inhabitant is a machine-checked
receipt of precisely what this bridge does — and, in the last two fields, of
what it does not. -/

/-- The RH-lane bridge, as a record of statements. -/
structure BridgeLedger where
  /-- The `ℕ` ledgers of the Agda lane encode order relations, not estimates. -/
  ledger_is_order_encoding : ∀ a b : ℕ, (∃ m : ℕ, a + m = b) ↔ a ≤ b
  /-- And they are inhabited trivially, so they carry no analytic content. -/
  ledger_trivially_inhabited : ∃ l : CoshCoercivityLedger, l.alphaSq = 0 ∧ l.excess = 0
  /-- The cosh mechanism, formalised. -/
  cosh_quadratic : ∀ x : ℝ, x ^ 2 / 2 ≤ Real.cosh x - 1
  /-- The taper coercivity with an explicit positive weight from the plateau. -/
  taper_coercivity : ∀ (phi : ℝ → ℝ) (a R : ℝ), 0 ≤ R → (∀ u : ℝ, |u| ≤ R → phi u = 1) →
    Integrable (fun u => phi u ^ 2 * (Real.cosh (2 * a * u) - 1)) →
    Integrable (fun u => u ^ 2 * phi u ^ 2) →
    4 * R ^ 3 / 3 * a ^ 2 ≤ ∫ u, phi u ^ 2 * (Real.cosh (2 * a * u) - 1)
  /-- The real content of the centred-grid retention ledger. -/
  grid_retention : ∀ full fin tail : ℝ, full = 2 * (fin + tail) → tail ≤ fin → full / 4 ≤ fin
  /-- The real content of the Poisson finite-retention ledger. -/
  finite_retention : ∀ defect slack fullExcess finiteExcess tailLoss : ℝ, 0 ≤ slack →
    defect + slack = fullExcess → fullExcess = finiteExcess + tailLoss →
    tailLoss ≤ finiteExcess → defect ≤ 2 * finiteExcess
  /-- The aggregate kernel envelope, from the generic two-regime theorem, under
  an explicit kernel-identification hypothesis. -/
  kernel_envelope : ∀ {f : ℝ → ℂ}, Integrable f → Differentiable ℝ f → Integrable (deriv f) →
    ∀ (k : ℝ → ℝ) (S : Finset ℝ) (N M : ℕ), (0 : ℝ) ∉ S → (∀ ξ ∈ S, k ξ = ‖𝓕 f ξ‖) →
      (∀ ξ ∈ S, |ξ| < M) →
      (∀ m : ℕ, ((S.filter (fun ξ => ⌊|ξ|⌋₊ = m)).card : ℝ) ≤ N) →
      ∑ ξ ∈ S, k ξ ≤ N * (∫ x, ‖f x‖) + N * ((∫ x, ‖deriv f x‖) / (2 * π)) *
        ∑ m ∈ Finset.Ico 1 M, (1 : ℝ) / m
  /-- The channel split: the bilinear diagonal is transverse-blind, the
  Hermitian diagonal doubles the transverse part. -/
  channel_split : ∀ x : CentredCoordinate,
    (bilinearArgument x x).transverse = 0 ∧
      (hermitianArgument x x).transverse = 2 * x.transverse
  /-- Poisson summation on the unit lattice, for real arguments. -/
  poisson_lattice : ∀ (f : ℝ → ℂ), Continuous f → ∀ (b : ℝ), 1 < b →
    (f =O[Filter.cocompact ℝ] fun x => |x| ^ (-b)) →
    (𝓕 f =O[Filter.cocompact ℝ] fun x => |x| ^ (-b)) →
    ∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n
  /-- Negative: the abstract Agda producer socket admits a contentless
  inhabitant, so there is no type-level transport through it. -/
  no_type_level_transport : ∀ (I : Type) (e : I → ℕ),
    ∃ p : AbstractEnvelopeProducer, p.PairIndex = I ∧ HEq p.envelope e
  /-- Negative: the envelope does not by itself dominate an arithmetic grid tail. -/
  envelope_tail_not_summable : ∀ K₁ h : ℝ, 0 < K₁ → 0 < h →
    ¬ Summable (fun k : ℕ => K₁ / ((k : ℝ) * h))

/-- The bridge, inhabited. -/
theorem bridgeLedger : BridgeLedger where
  ledger_is_order_encoding := nat_margin_iff_le
  ledger_trivially_inhabited := ledgers_have_trivial_inhabitants.1
  cosh_quadratic := sq_div_two_le_cosh_sub_one
  taper_coercivity := fun phi a R hR hplateau hexc hmom =>
    taper_coercivity_of_plateau phi a R hR hplateau hexc hmom
  grid_retention := fun _ _ _ h1 h2 => real_centered_grid_retention h1 h2
  finite_retention := fun _ _ _ _ _ h1 h2 h3 h4 => real_finite_retention h1 h2 h3 h4
  kernel_envelope := fun hf hd hf' k S N M hS0 hid hM hcount =>
    fourier_pair_sum_le hf hd hf' k S N M hS0 hid hM hcount
  channel_split := fun x =>
    ⟨bilinear_diagonal_transverse_zero x, hermitian_diagonal_transverse_double x⟩
  poisson_lattice := fun _ hc _ hb hf hFf => poisson_unit_lattice hc hb hf hFf
  no_type_level_transport := producer_socket_is_contentless
  envelope_tail_not_summable := fun _ _ hK₁ hh => grid_envelope_not_summable hK₁ hh

end RiemannBridge
end Spine
