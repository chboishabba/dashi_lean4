/-
# The parity quotient bookkeeping of the four-sample response

`PoleQuotientTransversality.lean` shows that on the four symmetric samples
`r, -r, 2r, -2r` the two zero-side parity directions are linearly independent
from the two pole directions.  This module records that fact *as a statement
about the quotient*

  `Q := (Fin 4 → ℝ) ⧸ span ℝ {poleEvenVec, poleOddVec}`,

which is the natural home for the explicit-formula bookkeeping asked for by the
`literalWeilParityQuotientDecomposition` surface.

The sample vector of a height-`y` channel is

  `evenVec y = (A_y(r), A_y(r), A_y(2r), A_y(2r))`,
  `oddVec  y = (B_y(r), -B_y(r), B_y(2r), -B_y(2r))`,

the four coordinates being the samples at `r, -r, 2r, -2r`; the sign pattern is
exactly `evenResponse_neg` / `oddResponse_neg`.

Contents.

* `poleContribution_quotient_zero` — `Q_pole = 0`, definitionally.
* `targetPair_quotient_independent` — for an off-line zero height `a` below the
  pole height `p`, the two classes `[evenVec a]`, `[oddVec a]` are linearly
  independent in `Q` at all sufficiently small radii; in particular
  `Q_target ≠ 0` (`target_quotient_ne_zero`).
* `parityQuotientBalance` — pure bookkeeping: from a balance relation
  `v_target + v_other + v_prime + v_Γ + v_pole = 0` with `v_pole` in the pole
  space, the quotient identity `Q_target = -(Q_other + Q_prime + Q_Γ)` holds,
  and the right-hand side is nonzero as soon as `Q_target ≠ 0`.
* `literalWeilParityQuotientDecomposition` — the two combined: for an actual
  off-line nontrivial zero of `riemannZeta`, *any* four-sample balance relation
  of the above shape forces the non-target, non-pole part of the relation to
  have nonzero class in the two-dimensional parity quotient.
* `no_offline_zero_if_nuisance_in_pole_span` — the "dream case" contrapositive:
  if the other-zeros, prime and gamma contributions all lie in the pole span,
  the balance relation is contradictory.

The balance relation is a *hypothesis* of these theorems, not an assertion: the
Weil explicit formula itself is neither used nor claimed here.  What is proved
is the exact linear-algebraic consequence of having such a relation.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.ActualZetaHeightSeparation
import RiemannAnalytic.PrimeFourSampleGeometry

open MeasureTheory Set

namespace RiemannAnalytic
namespace WeilParityQuotientDecomposition

open EvenTaylorDeterminant OddTaylorDeterminant PoleQuotientTransversality
open ActualZetaHeightSeparation

/-! ## The four-sample vectors and the pole space -/

/-- The even-channel four-sample vector at height `y`: the samples of
`evenResponse` at `r, -r, 2r, -2r`.  The even channel is even in the radius, so
the first two and the last two coordinates agree. -/
noncomputable def evenVec (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : Fin 4 → ℝ :=
  ![evenResponse L φ y r, evenResponse L φ y r,
    evenResponse L φ y (2 * r), evenResponse L φ y (2 * r)]

/-- The odd-channel four-sample vector at height `y`: the samples of
`oddResponse` at `r, -r, 2r, -2r`.  The odd channel is odd in the radius, whence
the alternating signs. -/
noncomputable def oddVec (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : Fin 4 → ℝ :=
  ![oddResponse L φ y r, -oddResponse L φ y r,
    oddResponse L φ y (2 * r), -oddResponse L φ y (2 * r)]

/-- The two-dimensional pole nuisance space inside the four-sample space. -/
noncomputable def poleSpace (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) : Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ {evenVec L φ p r, oddVec L φ p r}

/-- The parity quotient: four samples modulo the two pole directions. -/
abbrev ParityQuotient (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) : Type :=
  (Fin 4 → ℝ) ⧸ poleSpace L φ p r

/-- The class of a four-sample vector in the parity quotient. -/
noncomputable def qcls (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) (v : Fin 4 → ℝ) :
    ParityQuotient L φ p r :=
  Submodule.Quotient.mk v

variable {L Cφ a p c d m : ℝ} {φ : ℝ → ℝ}

theorem qcls_add (v w : Fin 4 → ℝ) :
    qcls L φ p r (v + w) = qcls L φ p r v + qcls L φ p r w := rfl

theorem qcls_smul (s : ℝ) (v : Fin 4 → ℝ) :
    qcls L φ p r (s • v) = s • qcls L φ p r v := rfl

theorem qcls_eq_zero_iff (v : Fin 4 → ℝ) :
    qcls L φ p r v = 0 ↔ v ∈ poleSpace L φ p r :=
  Submodule.Quotient.mk_eq_zero _

/-! ## `Q_pole = 0` -/

/-- The pole-even direction is annihilated by the quotient. -/
theorem qcls_evenVec_pole (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) :
    qcls L φ p r (evenVec L φ p r) = 0 := by
  rw [qcls_eq_zero_iff]
  exact Submodule.subset_span (by simp)

/-- The pole-odd direction is annihilated by the quotient. -/
theorem qcls_oddVec_pole (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) :
    qcls L φ p r (oddVec L φ p r) = 0 := by
  rw [qcls_eq_zero_iff]
  exact Submodule.subset_span (by simp)

/-- **`Q_pole = 0`.**  Every pole contribution — any real linear combination of
the two pole directions — has zero class in the parity quotient. -/
theorem poleContribution_quotient_zero (L : ℝ) (φ : ℝ → ℝ) (p r : ℝ) (s' t' : ℝ) :
    qcls L φ p r (s' • evenVec L φ p r + t' • oddVec L φ p r) = 0 := by
  rw [qcls_add, qcls_smul, qcls_smul, qcls_evenVec_pole, qcls_oddVec_pole]
  simp

/-! ## `Q_target ≠ 0` -/

/-- **The target-zero parity pair is independent in the quotient.**  For a zero
height `0 < a` strictly below the pole height `p`, at all sufficiently small
radii the classes of the two zero-side parity directions are linearly
independent in the two-dimensional parity quotient. -/
theorem targetPair_quotient_independent
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ s t : ℝ,
      s • qcls L φ p r (evenVec L φ a r) + t • qcls L φ p r (oddVec L φ a r) = 0 →
      s = 0 ∧ t = 0 := by
  obtain ⟨r₀, hr₀, hind⟩ := pole_quotient_transversality
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt s t hrel => ?_⟩
  rw [← qcls_smul, ← qcls_smul, ← qcls_add, qcls_eq_zero_iff, poleSpace,
    Submodule.mem_span_pair] at hrel
  obtain ⟨c₁, c₂, hc₁₂⟩ := hrel
  have e0 := congrFun hc₁₂ 0
  have e1 := congrFun hc₁₂ 1
  have e2 := congrFun hc₁₂ 2
  have e3 := congrFun hc₁₂ 3
  simp only [evenVec, oddVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at e0 e1 e2 e3
  obtain ⟨hs, ht, _, _⟩ := hind r hr hlt s t (-c₁) (-c₂)
    (by linarith) (by linarith) (by linarith) (by linarith)
  exact ⟨hs, ht⟩

/-- **`Q_target ≠ 0`.**  The total zero-side response vector at a height `a`
strictly between `0` and the pole height has nonzero class in the parity
quotient, at all sufficiently small radii. -/
theorem target_quotient_ne_zero
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      qcls L φ p r (evenVec L φ a r + oddVec L φ a r) ≠ 0 := by
  obtain ⟨r₀, hr₀, hind⟩ := targetPair_quotient_independent
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt hzero => ?_⟩
  have : (1 : ℝ) • qcls L φ p r (evenVec L φ a r)
      + (1 : ℝ) • qcls L φ p r (oddVec L φ a r) = 0 := by
    rw [one_smul, one_smul, ← qcls_add]
    exact hzero
  exact one_ne_zero (hind r hr hlt 1 1 this).1

/-! ## The bookkeeping identity in the quotient -/

/-- **Pure quotient bookkeeping.**  A four-sample balance relation
`v_target + v_other + v_prime + v_Γ + v_pole = 0` whose pole part lies in the
pole space descends to `Q_target = -(Q_other + Q_prime + Q_Γ)`; if moreover the
target class is nonzero then so is the nuisance class. -/
theorem parityQuotientBalance {r : ℝ} {vTarget vOther vPrime vGamma vPole : Fin 4 → ℝ}
    (hPole : vPole ∈ poleSpace L φ p r)
    (hbalance : vTarget + vOther + vPrime + vGamma + vPole = 0) :
    qcls L φ p r vPole = 0
      ∧ qcls L φ p r vTarget = -qcls L φ p r (vOther + vPrime + vGamma)
      ∧ (qcls L φ p r vTarget ≠ 0 → qcls L φ p r (vOther + vPrime + vGamma) ≠ 0) := by
  have hp0 : qcls L φ p r vPole = 0 := (qcls_eq_zero_iff _).2 hPole
  have hsum : qcls L φ p r (vTarget + (vOther + vPrime + vGamma) + vPole) = 0 := by
    have : vTarget + (vOther + vPrime + vGamma) + vPole = 0 := by
      rw [← hbalance]; abel
    rw [this]
    exact (qcls_eq_zero_iff _).2 (Submodule.zero_mem _)
  rw [qcls_add, qcls_add, hp0, add_zero] at hsum
  refine ⟨hp0, by linear_combination (norm := abel) hsum, fun hne hzero => ?_⟩
  apply hne
  rw [hzero, add_zero] at hsum
  exact hsum

/-- **`literalWeilParityQuotientDecomposition`.**  Let `ρ` be an actual
nontrivial off-line zero of `riemannZeta`, and let `φ` be an admissible taper.
Then at all sufficiently small radii the following holds for the four symmetric
samples `r, -r, 2r, -2r`: whenever the target-zero contribution, the
other-zeros contribution, the prime contribution, the gamma contribution and a
pole contribution sum to zero, the class of

  `other zeros + primes + gamma`

in the two-dimensional parity quotient is nonzero, and equals `-Q_target`.

The balance relation is an assumption on the supplied vectors; no explicit
formula is asserted.  The content is that the target zero occupies a direction
the pole space cannot absorb, so the remaining contributions cannot all be
pole-like. -/
theorem literalWeilParityQuotientDecomposition {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2)
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      ∀ vOther vPrime vGamma vPole : Fin 4 → ℝ,
        vPole ∈ poleSpace L φ (1 / 2) r →
        (evenVec L φ |ρ.re - 1 / 2| r + oddVec L φ |ρ.re - 1 / 2| r)
            + vOther + vPrime + vGamma + vPole = 0 →
        qcls L φ (1 / 2) r vPole = 0
          ∧ qcls L φ (1 / 2) r (evenVec L φ |ρ.re - 1 / 2| r + oddVec L φ |ρ.re - 1 / 2| r)
              = -qcls L φ (1 / 2) r (vOther + vPrime + vGamma)
          ∧ qcls L φ (1 / 2) r (vOther + vPrime + vGamma) ≠ 0 := by
  obtain ⟨hapos, halt⟩ := offline_zero_strict_height_separation hz h0 h1 hoff
  obtain ⟨r₀, hr₀, hne⟩ := target_quotient_ne_zero (p := 1 / 2)
    hφmeas hφ0 hφb hL hapos halt hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt vOther vPrime vGamma vPole hPole hbal => ?_⟩
  obtain ⟨h1', h2', h3'⟩ := parityQuotientBalance hPole hbal
  exact ⟨h1', h2', h3' (hne r hr hlt)⟩

/-- **The "dream case" is impossible for a genuine off-line zero.**  If the
other-zeros, prime and gamma four-sample contributions all lay in the pole span,
then no balance relation of the explicit-formula shape could hold for an actual
off-line nontrivial zero.  Equivalently: at least one of those three
contributions must be transverse to the pole space. -/
theorem no_offline_zero_if_nuisance_in_pole_span {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2)
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      ∀ vOther vPrime vGamma vPole : Fin 4 → ℝ,
        vOther ∈ poleSpace L φ (1 / 2) r → vPrime ∈ poleSpace L φ (1 / 2) r →
        vGamma ∈ poleSpace L φ (1 / 2) r → vPole ∈ poleSpace L φ (1 / 2) r →
        ¬ ((evenVec L φ |ρ.re - 1 / 2| r + oddVec L φ |ρ.re - 1 / 2| r)
              + vOther + vPrime + vGamma + vPole = 0) := by
  obtain ⟨r₀, hr₀, hdec⟩ := literalWeilParityQuotientDecomposition hz h0 h1 hoff
    hφmeas hφ0 hφb hL hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt vOther vPrime vGamma vPole hO hP hG hPo hbal => ?_⟩
  obtain ⟨-, -, hne⟩ := hdec r hr hlt vOther vPrime vGamma vPole hPo hbal
  exact hne ((qcls_eq_zero_iff _).2
    (Submodule.add_mem _ (Submodule.add_mem _ hO hP) hG))

/-! ## The prime image in the same coordinates

`PrimeFourSampleGeometry.primeFourSampleQuotientDecision` is stated in the
*parity* coordinates `(cos rλ, sin rλ, cos 2rλ, sin 2rλ)`, whereas the pole
space above lives in the raw sample coordinates `r, -r, 2r, -2r`.  The two are
related by the invertible parity lift `(A₁,B₁,A₂,B₂) ↦ (A₁+B₁, A₁-B₁, A₂+B₂,
A₂-B₂)`, so the decision transports verbatim. -/

/-- The parity lift: from `(even₁, odd₁, even₂, odd₂)` to the raw samples at
`r, -r, 2r, -2r`. -/
def parityLift (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0 + x 1, x 0 - x 1, x 2 + x 3, x 2 - x 3]

/-- Its inverse. -/
noncomputable def parityDrop (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(z 0 + z 1) / 2, (z 0 - z 1) / 2, (z 2 + z 3) / 2, (z 2 - z 3) / 2]

theorem parityLift_add (x y : Fin 4 → ℝ) :
    parityLift (x + y) = parityLift x + parityLift y := by
  funext i; fin_cases i <;> simp [parityLift] <;> ring

theorem parityLift_smul (s : ℝ) (x : Fin 4 → ℝ) :
    parityLift (s • x) = s • parityLift x := by
  funext i; fin_cases i <;> simp [parityLift] <;> ring

theorem parityLift_parityDrop (z : Fin 4 → ℝ) : parityLift (parityDrop z) = z := by
  funext i; fin_cases i <;> simp [parityLift, parityDrop] <;> ring

theorem parityLift_injective : Function.Injective parityLift := by
  intro x y h
  funext i
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [parityLift, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
  fin_cases i <;> simp <;> linarith

/-- **The prime image is transverse to the pole space, in the sample
coordinates of the zero-side theorem.**  For every observation radius `r > 0`
there is a strictly positive log-frequency whose four-sample contribution has
nonzero class in the parity quotient.

So the parity quotient does *not* annihilate the prime side: the answer to the
`literalPrimeParityQuotientDecision` question is negative. -/
theorem primeContribution_quotient_ne_zero {r : ℝ} (hr : 0 < r) (L : ℝ) (φ : ℝ → ℝ) (p : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧
      qcls L φ p r (parityLift (PrimeFourSampleGeometry.primeFourSample r lam)) ≠ 0 := by
  obtain ⟨lam, hlam, hnot⟩ := PrimeFourSampleGeometry.primeFourSampleQuotientDecision hr
    (parityDrop (evenVec L φ p r)) (parityDrop (oddVec L φ p r))
  refine ⟨lam, hlam, fun hzero => ?_⟩
  rw [qcls_eq_zero_iff, poleSpace, Submodule.mem_span_pair] at hzero
  obtain ⟨s, t, hst⟩ := hzero
  refine hnot s t (parityLift_injective ?_)
  rw [parityLift_add, parityLift_smul, parityLift_smul, parityLift_parityDrop,
    parityLift_parityDrop, hst]

end WeilParityQuotientDecomposition
end RiemannAnalytic
