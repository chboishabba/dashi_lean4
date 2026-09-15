/-
# The literal R571 signed ±y multiplier-difference carrier, over `ℝ`

## Object

`R571` (`NSTriadKNInnerHelicalComponentCommutatorRound571Exact`) splits an
arbitrary transverse physical velocity pair into its four helical sign pairs and
shows that each projected component is an exact curl eigenvector, so that `R106`
returns the **multiplier-difference vector**

```
(λ_b^t − λ_a^s) · P_p (u_a^s × u_b^t).
```

`NSTriadKNR571HomochiralRadialIncrementSpecializationExact` transports the
signed curl eigenvalues to `R311`'s signed radii,

```agda
signedRadius plus  r = r
signedRadius minus r = -r
innerMultiplierDifference sa sb ra rb = signedRadius sb rb - signedRadius sa ra
```

so on the literal carrier the scalar in front of the commutator is
`t‖q‖ − s‖p‖` for helicity signs `s,t ∈ {+,−}` and radii `‖p‖`, `‖q‖`.

## What is proved here

1. `multiplierDifference_homochiral` / `abs_multiplierDifference_homochiral_le`:
   in the *homochiral* channel `s = t` the multiplier difference is the radial
   increment `±(‖q‖ − ‖p‖)`, and on a triad `k + p + q = 0` it obeys the
   cutoff-uniform gain
   `|λ_q^t − λ_p^s| ≤ ‖k‖`:
   the commutator carrier costs one power of the *output* wavenumber, not of
   the interacting high modes.  This is the exact gain the R568 budget needs.

2. `multiplierDifference_heterochiral` and
   `heterochiral_multiplierDifference_not_output_controlled`: in the
   *heterochiral* channel `s ≠ t` the same quantity is `±(‖q‖ + ‖p‖)`, and
   **no** bound `|λ_q^t − λ_p^s| ≤ M‖k‖` can hold uniformly: for every `M`
   there is a genuine triad `k + p + q = 0` with `‖k‖ = 1` on which it fails.

   This is a *decisive typed obstruction*, not a missing estimate: the literal
   R571 carrier on its own cannot pay `CommutatorOnlySpacetimeBudget568`.  The
   four-sign split of R577 (or an equivalent mechanism that treats the
   heterochiral rows separately) is therefore **forced**, not optional.

3. `sum_multiplierDifference_homochiral_vanishes`: the exact signed cancellation
   the control record asks to preserve — on a homochiral cell the two ordered
   orientations `(a,b)` and `(b,a)` carry opposite multiplier differences, so
   the symmetrised carrier vanishes identically before any majorisation.

## Lineage

R106 (projected helical self-forcing vector), R311 (signed radii / route
split), R27 (translation-multiplier commutator), R571 and its homochiral
specialisation, R93 (Waleffe three-leg common amplitude), R577 (four-sign inner
fibre Gram).  The reverse-triangle step reuses the donor Waleffe geometry
(`ClayNS.Waleffe.triad_reverse_triangle`) in spirit; it is reproved here for an
arbitrary seminormed group so that the statement is available without importing
the Waleffe Galerkin carrier.

## Status

A1 infrastructure (items 1 and 3) plus one decisive typed obstruction (item 2).
No PDE estimate is claimed.
-/
import Mathlib

namespace DASHI.NS.Unforced

/-- The two helicity signs of the R571/R311 split. -/
inductive HelicitySign
  | plus
  | minus
  deriving DecidableEq, Repr

namespace HelicitySign

/-- `R311.signedRadius`. -/
def signedRadius : HelicitySign → ℝ → ℝ
  | plus, r => r
  | minus, r => -r

@[simp] theorem signedRadius_plus (r : ℝ) : signedRadius plus r = r := rfl
@[simp] theorem signedRadius_minus (r : ℝ) : signedRadius minus r = -r := rfl

end HelicitySign

open HelicitySign

/-- `R311.innerMultiplierDifference`: the scalar multiplying the projected
commutator in the R571 carrier. -/
def multiplierDifference (sa sb : HelicitySign) (ra rb : ℝ) : ℝ :=
  signedRadius sb rb - signedRadius sa ra

@[simp] theorem multiplierDifference_plus_plus (ra rb : ℝ) :
    multiplierDifference plus plus ra rb = rb - ra := rfl

@[simp] theorem multiplierDifference_minus_minus (ra rb : ℝ) :
    multiplierDifference minus minus ra rb = -(rb - ra) := by
  simp [multiplierDifference]; ring

/-- **Homochiral channel = radial increment.** -/
theorem multiplierDifference_homochiral (s : HelicitySign) (ra rb : ℝ) :
    |multiplierDifference s s ra rb| = |rb - ra| := by
  cases s
  · simp [multiplierDifference]
  · simp only [multiplierDifference, signedRadius_minus]
    rw [show -rb - -ra = -(rb - ra) by ring, abs_neg]

/-- **Heterochiral channel = radial sum.** -/
theorem multiplierDifference_heterochiral (ra rb : ℝ) :
    |multiplierDifference plus minus ra rb| = |ra + rb| ∧
      |multiplierDifference minus plus ra rb| = |ra + rb| := by
  constructor
  · simp only [multiplierDifference, signedRadius_plus, signedRadius_minus]
    rw [show -rb - ra = -(ra + rb) by ring, abs_neg]
  · simp only [multiplierDifference, signedRadius_plus, signedRadius_minus]
    rw [show rb - -ra = ra + rb by ring]

section Triad

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Reverse triangle inequality on a triad** (Waleffe geometry, reproved for
an arbitrary seminormed group): if `k + p + q = 0` then `‖q‖ - ‖p‖ ≤ ‖k‖`. -/
theorem triad_radius_sub_le {k p q : E} (h : k + p + q = 0) : ‖q‖ - ‖p‖ ≤ ‖k‖ := by
  have hq : q = -(k + p) := by linear_combination (norm := abel) h
  have h2 : ‖q‖ ≤ ‖k‖ + ‖p‖ := by
    rw [hq, norm_neg]; exact norm_add_le _ _
  linarith

/-- **R571 homochiral gain.**  On a triad `k + p + q = 0` the homochiral
multiplier difference is controlled by the *output* radius alone:

`|λ_q^s − λ_p^s| ≤ ‖k‖`.

This is the one derivative of gain the commutator-only route buys, and it is
uniform in the cutoff because `‖k‖` is an output-fibre datum. -/
theorem abs_multiplierDifference_homochiral_le {k p q : E} (h : k + p + q = 0)
    (s : HelicitySign) : |multiplierDifference s s ‖p‖ ‖q‖| ≤ ‖k‖ := by
  rw [multiplierDifference_homochiral]
  have h1 : ‖q‖ - ‖p‖ ≤ ‖k‖ := triad_radius_sub_le h
  have h2 : ‖p‖ - ‖q‖ ≤ ‖k‖ := by
    have : k + q + p = 0 := by linear_combination (norm := abel) h
    exact triad_radius_sub_le this
  rw [abs_sub_le_iff]
  exact ⟨h1, h2⟩

/-- **The R571 commutator carrier with its gain.**  The projected commutator
vector of a homochiral cell is `(λ_q^s − λ_p^s) • P_p(u_p^s × u_q^s)`; its norm
costs one power of the *output* radius. -/
theorem norm_commutatorCarrier_homochiral_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k p q : E} (h : k + p + q = 0) (s : HelicitySign) (w : F) :
    ‖multiplierDifference s s ‖p‖ ‖q‖ • w‖ ≤ ‖k‖ * ‖w‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_multiplierDifference_homochiral_le h s)
    (norm_nonneg w)

/-- **The homochiral forcing-side square carries the output gain.**  Summed over
a finite family of homochiral cells, the commutator squares are dominated by
the *output* radii squared times the cross-product squares.  This is the shape
the dissipation receipt `∑ ‖A c‖² ≤ c_A · D` of `A1ChannelObligation` has to
meet; the heterochiral rows are excluded here precisely because
`heterochiral_multiplierDifference_not_output_controlled` shows they cannot be
included. -/
theorem sum_commutator_square_homochiral_le {ι F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (s : Finset ι) (kv pv qv : ι → E) (w : ι → F)
    (sgn : ι → HelicitySign) (h : ∀ a ∈ s, kv a + pv a + qv a = 0) :
    ∑ a ∈ s, ‖multiplierDifference (sgn a) (sgn a) ‖pv a‖ ‖qv a‖ • w a‖ ^ 2
      ≤ ∑ a ∈ s, ‖kv a‖ ^ 2 * ‖w a‖ ^ 2 := by
  refine Finset.sum_le_sum fun a ha => ?_
  have h1 := norm_commutatorCarrier_homochiral_le (h a ha) (sgn a) (w a)
  have h2 : (0 : ℝ) ≤ ‖multiplierDifference (sgn a) (sgn a) ‖pv a‖ ‖qv a‖ • w a‖ :=
    norm_nonneg _
  calc ‖multiplierDifference (sgn a) (sgn a) ‖pv a‖ ‖qv a‖ • w a‖ ^ 2
      ≤ (‖kv a‖ * ‖w a‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = ‖kv a‖ ^ 2 * ‖w a‖ ^ 2 := by ring

end Triad

/-- **Decisive typed obstruction: the heterochiral channel has no output gain.**

For every constant `M` there is an honest triad `k + p + q = 0` of real
wavevectors with `‖k‖ = 1` on which the heterochiral multiplier difference
exceeds `M * ‖k‖`.  Hence the homochiral gain
`abs_multiplierDifference_homochiral_le` does **not** extend across the sign
split, and the literal R571 carrier alone cannot supply a cutoff-uniform
pointwise bound for `globalForcingFull`.  Any A1 route must handle the
heterochiral rows by a different mechanism (the R577 four-sign receipt, or a
cancellation internal to the heterochiral block). -/
theorem heterochiral_multiplierDifference_not_output_controlled (M : ℝ) :
    ∃ k p q : ℝ, k + p + q = 0 ∧ ‖k‖ = 1 ∧
      M * ‖k‖ < |multiplierDifference plus minus ‖p‖ ‖q‖| := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  refine ⟨1, (n : ℝ) + 1, -((n : ℝ) + 2), by ring, by norm_num, ?_⟩
  have hp : ‖((n : ℝ) + 1)‖ = (n : ℝ) + 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
  have hq : ‖(-((n : ℝ) + 2))‖ = (n : ℝ) + 2 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg]; positivity
  rw [(multiplierDifference_heterochiral _ _).1, hp, hq]
  have : |((n : ℝ) + 1) + ((n : ℝ) + 2)| = 2 * (n : ℝ) + 3 := by
    rw [abs_of_nonneg (by positivity)]; ring
  rw [this, norm_one, mul_one]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **Exact homochiral signed cancellation.**  The symmetrised ordered pair of a
homochiral cell carries opposite multiplier differences, so the signed sum
vanishes identically.  This is the cancellation the control record requires to
survive intact into the full-square carrier: it is an equation, not an
estimate. -/
theorem sum_multiplierDifference_homochiral_vanishes (s : HelicitySign) (ra rb : ℝ) :
    multiplierDifference s s ra rb + multiplierDifference s s rb ra = 0 := by
  cases s <;> simp only [multiplierDifference, signedRadius_plus, signedRadius_minus] <;> ring

end DASHI.NS.Unforced
