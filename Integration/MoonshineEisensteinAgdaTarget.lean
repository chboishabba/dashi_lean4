import Integration.MoonshineEisensteinAnalytic

/-!
# Canonical Lean target for the actual Agda finite Eisenstein recurrences

This module mirrors the definitions in
DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact
without changing their indexing, signs, or coefficient scales.

The purpose is not to create a second analytic definition of E4/E6. It gives
the Agda extraction compiler one canonical Lean target:

  q(tau)    = exp(2*pi*i*tau)
  E4_0      = 1
  E4_(n+1)  = E4_n + (240 * sigma_3(n+1)) q^(n+1)
  E6_0      = 1
  E6_(n+1)  = E6_n - (504 * sigma_5(n+1)) q^(n+1)

The converged Mathlib modular forms remain in
Integration.MoonshineEisensteinAnalytic.
-/

namespace Integration.MoonshineEisensteinAgdaTarget

open Complex Real
open UpperHalfPlane hiding I
open ArithmeticFunction
open scoped Real Nat ArithmeticFunction.sigma BigOperators MatrixGroups

noncomputable section

/-- Literal target for Agda qOf. Multiplication is parenthesized to match the
Agda source before ring normalization. -/
def qOfTarget (τ : ℍ) : ℂ :=
  Complex.exp (((2 : ℂ) * (I * π)) * (τ : ℂ))

/-- The literal target q is the Mathlib analytic q parameter. -/
theorem qOfTarget_eq_qParam (τ : ℍ) :
    qOfTarget τ = Integration.MoonshineEisensteinAnalytic.qParam τ := by
  unfold qOfTarget Integration.MoonshineEisensteinAnalytic.qParam
  congr 1
  ring

/-- Lean target of the Agda repeated-addition natural scaling. -/
def scaleNatTarget (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) * z

@[simp]
theorem scaleNatTarget_zero (z : ℂ) :
    scaleNatTarget 0 z = 0 := by
  simp [scaleNatTarget]

@[simp]
theorem scaleNatTarget_succ (n : ℕ) (z : ℂ) :
    scaleNatTarget (n + 1) z = z + scaleNatTarget n z := by
  simp [scaleNatTarget]
  ring

/-- Canonical Lean target of Agda e4Truncated, parameterized by q so that the
recurrence itself is independent of the upper-half-plane packaging. -/
def e4TruncatedTarget : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, q =>
      e4TruncatedTarget n q +
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1))

/-- Canonical Lean target of Agda e6Truncated. -/
def e6TruncatedTarget : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, q =>
      e6TruncatedTarget n q -
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1))

@[simp]
theorem e4TruncatedTarget_zero (q : ℂ) :
    e4TruncatedTarget 0 q = 1 := rfl

@[simp]
theorem e4TruncatedTarget_succ (n : ℕ) (q : ℂ) :
    e4TruncatedTarget (n + 1) q =
      e4TruncatedTarget n q +
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1)) := rfl

@[simp]
theorem e6TruncatedTarget_zero (q : ℂ) :
    e6TruncatedTarget 0 q = 1 := rfl

@[simp]
theorem e6TruncatedTarget_succ (n : ℕ) (q : ℂ) :
    e6TruncatedTarget (n + 1) q =
      e6TruncatedTarget n q -
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1)) := rfl

/-- Closed finite-sum form of the literal Agda E4 recurrence. -/
theorem e4TruncatedTarget_eq_sum (N : ℕ) (q : ℂ) :
    e4TruncatedTarget N q =
      1 + ∑ n ∈ Finset.range N,
        scaleNatTarget (240 * σ 3 (n + 1)) (q ^ (n + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [e4TruncatedTarget_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- Closed finite-sum form of the literal Agda E6 recurrence. -/
theorem e6TruncatedTarget_eq_sum (N : ℕ) (q : ℂ) :
    e6TruncatedTarget N q =
      1 - ∑ n ∈ Finset.range N,
        scaleNatTarget (504 * σ 5 (n + 1)) (q ^ (n + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [e6TruncatedTarget_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- The exact target recurrence evaluated at the canonical q parameter. -/
def e4At (N : ℕ) (τ : ℍ) : ℂ :=
  e4TruncatedTarget N (qOfTarget τ)

/-- The exact target recurrence evaluated at the canonical q parameter. -/
def e6At (N : ℕ) (τ : ℍ) : ℂ :=
  e6TruncatedTarget N (qOfTarget τ)

/-- Literal shifted E4 term used by the Agda recurrence. -/
def e4Term (τ : ℍ) (n : ℕ) : ℂ :=
  scaleNatTarget (240 * σ 3 (n + 1)) (qOfTarget τ ^ (n + 1))

/-- Literal shifted E6 term used by the Agda recurrence. -/
def e6Term (τ : ℍ) (n : ℕ) : ℂ :=
  scaleNatTarget (504 * σ 5 (n + 1)) (qOfTarget τ ^ (n + 1))

/-- The exact shifted E4 term family is summable. -/
theorem summable_e4Term (τ : ℍ) :
    Summable (e4Term τ) := by
  have hs :=
    (summable_nat_add_iff 1).mpr
      (Integration.MoonshineEisensteinAnalytic.summable_240_sigma3_q τ)
  simpa [e4Term, scaleNatTarget,
    qOfTarget_eq_qParam, Nat.cast_mul, mul_assoc] using hs

/-- The exact shifted E6 term family is summable. -/
theorem summable_e6Term (τ : ℍ) :
    Summable (e6Term τ) := by
  have hs :=
    (summable_nat_add_iff 1).mpr
      (Integration.MoonshineEisensteinAnalytic.summable_504_sigma5_q τ)
  simpa [e6Term, scaleNatTarget,
    qOfTarget_eq_qParam, Nat.cast_mul, mul_assoc] using hs

/-- The literal Agda E4 truncations converge to their canonical infinite sum. -/
theorem e4At_tendsto (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop
      (𝓝 (1 + ∑' n : ℕ, e4Term τ n)) := by
  have hs := summable_e4Term τ
  have ht := hs.hasSum.tendsto_sum_nat
  simpa [e4At, e4TruncatedTarget_eq_sum, e4Term] using
    tendsto_const_nhds.add ht

/-- The literal Agda E6 truncations converge to their canonical infinite sum. -/
theorem e6At_tendsto (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop
      (𝓝 (1 - ∑' n : ℕ, e6Term τ n)) := by
  have hs := summable_e6Term τ
  have ht := hs.hasSum.tendsto_sum_nat
  simpa [e6At, e6TruncatedTarget_eq_sum, e6Term] using
    tendsto_const_nhds.sub ht

/-- Canonical infinite targets selected by the actual Agda recurrences. -/
def e4Limit (τ : ℍ) : ℂ :=
  1 + ∑' n : ℕ, e4Term τ n

def e6Limit (τ : ℍ) : ℂ :=
  1 - ∑' n : ℕ, e6Term τ n

theorem e4At_tendsto_limit (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop (𝓝 (e4Limit τ)) := by
  simpa [e4Limit] using e4At_tendsto τ

theorem e6At_tendsto_limit (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop (𝓝 (e6Limit τ)) := by
  simpa [e6Limit] using e6At_tendsto τ

/-- The canonical infinite target of the literal Agda E4 recurrence is
exactly Mathlib's normalized weight-four Eisenstein series. -/
theorem e4Limit_eq_mathlib_E4 (τ : ℍ) :
    e4Limit τ = Integration.MoonshineEisensteinAnalytic.E4 τ := by
  rw [Integration.MoonshineEisensteinAnalytic.E4_qExpansion,
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        (σ 3 n : ℂ) *
          Integration.MoonshineEisensteinAnalytic.qParam τ ^ n)]
  simp_rw [← qOfTarget_eq_qParam τ]
  unfold e4Limit e4Term scaleNatTarget
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]
  ring

/-- The canonical infinite target of the literal Agda E6 recurrence is
exactly Mathlib's normalized weight-six Eisenstein series. -/
theorem e6Limit_eq_mathlib_E6 (τ : ℍ) :
    e6Limit τ = Integration.MoonshineEisensteinAnalytic.E6 τ := by
  rw [Integration.MoonshineEisensteinAnalytic.E6_qExpansion,
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        (σ 5 n : ℂ) *
          Integration.MoonshineEisensteinAnalytic.qParam τ ^ n)]
  simp_rw [← qOfTarget_eq_qParam τ]
  unfold e6Limit e6Term scaleNatTarget
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]
  ring

/-- Therefore the exact Agda-shaped finite E4 recurrence converges to Mathlib E4. -/
theorem e4At_tendsto_mathlib_E4 (τ : ℍ) :
    Tendsto (fun N => e4At N τ) atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E4 τ)) := by
  simpa [e4Limit_eq_mathlib_E4 τ] using e4At_tendsto_limit τ

/-- Therefore the exact Agda-shaped finite E6 recurrence converges to Mathlib E6. -/
theorem e6At_tendsto_mathlib_E6 (τ : ℍ) :
    Tendsto (fun N => e6At N τ) atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E6 τ)) := by
  simpa [e6Limit_eq_mathlib_E6 τ] using e6At_tendsto_limit τ

/-- Literal finite discriminant numerator carried by the Agda recurrence. -/
def discriminantNumeratorAt (N : ℕ) (τ : ℍ) : ℂ :=
  e4At N τ ^ 3 - e6At N τ ^ 2

/-- Normalized finite Delta candidate used by the source-facing Klein formula. -/
def normalizedDeltaAt (N : ℕ) (τ : ℍ) : ℂ :=
  discriminantNumeratorAt N τ / 1728

/-- Mathlib E4/E6 discriminant numerator target. -/
def discriminantNumeratorLimit (τ : ℍ) : ℂ :=
  Integration.MoonshineEisensteinAnalytic.E4 τ ^ 3 -
    Integration.MoonshineEisensteinAnalytic.E6 τ ^ 2

/-- Normalized E4/E6 Delta target. -/
def normalizedDeltaLimit (τ : ℍ) : ℂ :=
  discriminantNumeratorLimit τ / 1728

/-- The literal finite discriminant numerators converge to the E4/E6 numerator. -/
theorem discriminantNumeratorAt_tendsto (τ : ℍ) :
    Tendsto (fun N => discriminantNumeratorAt N τ) atTop
      (𝓝 (discriminantNumeratorLimit τ)) := by
  exact
    (e4At_tendsto_mathlib_E4 τ).pow 3 |>.sub
      ((e6At_tendsto_mathlib_E6 τ).pow 2)

/-- The normalized finite Delta candidates converge to the normalized E4/E6 expression. -/
theorem normalizedDeltaAt_tendsto (τ : ℍ) :
    Tendsto (fun N => normalizedDeltaAt N τ) atTop
      (𝓝 (normalizedDeltaLimit τ)) := by
  simpa [normalizedDeltaAt, normalizedDeltaLimit, div_eq_mul_inv] using
    (discriminantNumeratorAt_tendsto τ).mul_const ((1728 : ℂ)⁻¹)

/-- Nonvanishing of the denominator is finite arithmetic, not an analytic seam. -/
theorem complex_1728_ne_zero : (1728 : ℂ) ≠ 0 := by
  norm_num

/-- Weight-12 modular form obtained from the pinned Mathlib E4/E6 objects
without using the later discriminant package. -/
def e4CubeWeight12 : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num)
    ((Integration.MoonshineEisensteinAnalytic.E4.mul
      Integration.MoonshineEisensteinAnalytic.E4).mul
      Integration.MoonshineEisensteinAnalytic.E4)

/-- Weight-12 E6 square. -/
def e6SquareWeight12 : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num)
    (Integration.MoonshineEisensteinAnalytic.E6.mul
      Integration.MoonshineEisensteinAnalytic.E6)

/-- The normalized E4/E6 Delta candidate is itself a genuine level-one
weight-12 modular form at the pinned Mathlib version. -/
def normalizedDeltaForm : ModularForm 𝒮ℒ 12 :=
  ((1728 : ℂ)⁻¹) • (e4CubeWeight12 - e6SquareWeight12)

/-- The packaged modular form evaluates to the route-B normalized Delta limit. -/
theorem normalizedDeltaForm_apply (τ : ℍ) :
    normalizedDeltaForm τ = normalizedDeltaLimit τ := by
  simp [normalizedDeltaForm, normalizedDeltaLimit, discriminantNumeratorLimit,
    e4CubeWeight12, e6SquareWeight12, div_eq_mul_inv]
  ring

/-- Upper-half-plane reflection preserving positive imaginary part. -/
def negConj (τ : ℍ) : ℍ :=
  ⟨-conj (τ : ℂ), by simpa using τ.2⟩

@[simp]
theorem negConj_coe (τ : ℍ) :
    ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

/-- q respects the upper-half-plane real-structure reflection. -/
theorem qOfTarget_negConj (τ : ℍ) :
    qOfTarget (negConj τ) = conj (qOfTarget τ) := by
  unfold qOfTarget
  rw [← Complex.exp_conj]
  congr 1
  simp [negConj]
  ring

/-- The canonical E4 limit has real Fourier coefficients. -/
theorem e4Limit_negConj (τ : ℍ) :
    e4Limit (negConj τ) = conj (e4Limit τ) := by
  unfold e4Limit
  rw [map_add, map_one, RCLike.conjCLE.map_tsum]
  congr 1
  apply tsum_congr
  intro n
  simp [e4Term, scaleNatTarget, qOfTarget_negConj, map_mul, map_pow]

/-- The canonical E6 limit has real Fourier coefficients. -/
theorem e6Limit_negConj (τ : ℍ) :
    e6Limit (negConj τ) = conj (e6Limit τ) := by
  unfold e6Limit
  rw [map_sub, map_one, RCLike.conjCLE.map_tsum]
  congr 1
  apply tsum_congr
  intro n
  simp [e6Term, scaleNatTarget, qOfTarget_negConj, map_mul, map_pow]

/-- Mathlib E4 inherits the same real-structure conjugation law. -/
theorem mathlib_E4_negConj (τ : ℍ) :
    Integration.MoonshineEisensteinAnalytic.E4 (negConj τ) =
      conj (Integration.MoonshineEisensteinAnalytic.E4 τ) := by
  rw [← e4Limit_eq_mathlib_E4 (negConj τ),
      ← e4Limit_eq_mathlib_E4 τ]
  exact e4Limit_negConj τ

/-- Mathlib E6 inherits the same real-structure conjugation law. -/
theorem mathlib_E6_negConj (τ : ℍ) :
    Integration.MoonshineEisensteinAnalytic.E6 (negConj τ) =
      conj (Integration.MoonshineEisensteinAnalytic.E6 τ) := by
  rw [← e6Limit_eq_mathlib_E6 (negConj τ),
      ← e6Limit_eq_mathlib_E6 τ]
  exact e6Limit_negConj τ

/-- The normalized E4/E6 Delta target has the required conjugation symmetry. -/
theorem normalizedDeltaLimit_negConj (τ : ℍ) :
    normalizedDeltaLimit (negConj τ) =
      conj (normalizedDeltaLimit τ) := by
  simp [normalizedDeltaLimit, discriminantNumeratorLimit,
    mathlib_E4_negConj, mathlib_E6_negConj, map_sub, map_pow, map_div]

/-- The normalized route-B Delta target has the genuine weight-12 S law. -/
theorem normalizedDeltaLimit_S (τ : ℍ) :
    normalizedDeltaLimit (ModularGroup.S • τ) =
      (τ : ℂ) ^ 12 * normalizedDeltaLimit τ := by
  have hS :
      (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    ⟨ModularGroup.S, rfl⟩
  have h :=
    SlashInvariantForm.slash_action_eqn''
      normalizedDeltaForm hS τ
  simpa [normalizedDeltaForm_apply, ModularGroup.denom_S] using h

/-- The S-image of -conj(tau) is literally 1/conj(tau). -/
theorem S_negConj_coe (τ : ℍ) :
    (((ModularGroup.S • negConj τ : ℍ) : ℂ)) =
      1 / conj (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [negConj, one_div]

/-- Concrete reflection identity for the normalized E4/E6 Delta target.

This is the analytic identity isolated by the JMD fixed-locus image, now
derived from two independent machine-formalized facts:
1. weight-12 S modularity;
2. real Fourier-coefficient conjugation.
-/
theorem normalizedDelta_inv_conj (τ : ℍ) :
    normalizedDeltaLimit (ModularGroup.S • negConj τ) =
      conj ((τ : ℂ) ^ 12 * normalizedDeltaLimit τ) := by
  rw [normalizedDeltaLimit_S, normalizedDeltaLimit_negConj]
  simp [negConj, map_mul, map_pow]
  ring

/-- Unit norm is the concrete reciprocal-conjugate fixed-locus condition. -/
theorem S_negConj_fixed_of_normSq_one
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    ModularGroup.S • negConj τ = τ := by
  apply UpperHalfPlane.ext
  rw [S_negConj_coe]
  have hconj : conj (τ : ℂ) ≠ 0 := by
    simpa only [map_ne_zero] using UpperHalfPlane.ne_zero τ
  apply (div_eq_iff hconj).2
  calc
    (1 : ℂ) = (Complex.normSq (τ : ℂ) : ℂ) := by simp [hunit]
    _ = conj (τ : ℂ) * (τ : ℂ) := Complex.normSq_eq_conj_mul_self
    _ = (τ : ℂ) * conj (τ : ℂ) := by ring

/-- Fixed-locus value identity consumed by the Agda sixfold phase compiler. -/
theorem normalizedDelta_unitCircle_fixed
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    normalizedDeltaLimit τ =
      conj ((τ : ℂ) ^ 12 * normalizedDeltaLimit τ) := by
  have hfix := S_negConj_fixed_of_normSq_one τ hunit
  calc
    normalizedDeltaLimit τ =
        normalizedDeltaLimit (ModularGroup.S • negConj τ) := by
      exact congrArg normalizedDeltaLimit hfix.symm
    _ = conj ((τ : ℂ) ^ 12 * normalizedDeltaLimit τ) :=
      normalizedDelta_inv_conj τ

/-- Weight-zero j target built from the same normalized E4 and Delta target.

This is the standard normalized quotient E4^3 / Delta.  The definition is total
as a field expression; nonvanishing is only needed for inverse-style
rearrangements, not for the conjugation theorem below. -/
def jTarget (τ : ℍ) : ℂ :=
  Integration.MoonshineEisensteinAnalytic.E4 τ ^ 3 /
    normalizedDeltaLimit τ

/-- E4 carries the expected weight-four S transformation. -/
theorem mathlib_E4_S (τ : ℍ) :
    Integration.MoonshineEisensteinAnalytic.E4 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 4 *
        Integration.MoonshineEisensteinAnalytic.E4 τ := by
  have hS :
      (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    ⟨ModularGroup.S, rfl⟩
  have h :=
    SlashInvariantForm.slash_action_eqn''
      Integration.MoonshineEisensteinAnalytic.E4 hS τ
  simpa [ModularGroup.denom_S] using h

/-- The weight factors cancel: j is S-invariant. -/
theorem jTarget_S_invariant (τ : ℍ) :
    jTarget (ModularGroup.S • τ) = jTarget τ := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [jTarget, jTarget, mathlib_E4_S, normalizedDeltaLimit_S]
  field_simp
  ring

/-- j has the real-structure conjugation law inherited from E4 and Delta. -/
theorem jTarget_negConj (τ : ℍ) :
    jTarget (negConj τ) = conj (jTarget τ) := by
  simp [jTarget, mathlib_E4_negConj, normalizedDeltaLimit_negConj,
    map_div, map_pow]

/-- Reciprocal-conjugate reflection for weight-zero j. -/
theorem jTarget_inv_conj (τ : ℍ) :
    jTarget (ModularGroup.S • negConj τ) =
      conj (jTarget τ) := by
  rw [jTarget_S_invariant, jTarget_negConj]

/-- On the reciprocal-conjugate fixed locus, j is fixed by conjugation. -/
theorem jTarget_unitCircle_conj_fixed
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    jTarget τ = conj (jTarget τ) := by
  have hfix := S_negConj_fixed_of_normSq_one τ hunit
  calc
    jTarget τ =
        jTarget (ModularGroup.S • negConj τ) := by
      exact congrArg jTarget hfix.symm
    _ = conj (jTarget τ) := jTarget_inv_conj τ

/-- Equivalent real-axis statement on the modular boundary fixed locus. -/
theorem jTarget_unitCircle_im_zero
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    (jTarget τ).im = 0 := by
  have h := congrArg Complex.im (jTarget_unitCircle_conj_fixed τ hunit)
  simp only [Complex.conj_im] at h
  linarith

/-- Machine-readable seam. -/
structure AgdaTargetBoundary where
  literalQTargetOwned : Bool
  literalE4RecurrenceOwned : Bool
  literalE6RecurrenceOwned : Bool
  finiteSumNormalFormsOwned : Bool
  qTargetIdentifiedWithMathlibQ : Bool
  agdaPrimitiveExtractionInhabited : Bool
  finiteRecurrenceBoundToExtractedAgdaObject : Bool
  finiteToInfiniteLimitTransportPaid : Bool
  infiniteLimitIdentifiedWithMathlibE4E6 : Bool
  discriminantNumeratorLimitCompiled : Bool
  normalizedDeltaLimitCompiled : Bool
  normalizedDeltaPackagedAsWeight12ModularForm : Bool
  realStructureConjugationLawOwned : Bool
  weight12SActionOwned : Bool
  concreteInvConjReflectionOwned : Bool
  unitNormFixedLocusOwned : Bool
  fixedLocusValueIdentityOwned : Bool
  jWeightZeroTargetOwned : Bool
  jSInvariantOwned : Bool
  jConjugationOwned : Bool
  jInverseConjugationOwned : Bool
  jUnitCircleRealityOwned : Bool

def agdaTargetBoundary : AgdaTargetBoundary where
  literalQTargetOwned := true
  literalE4RecurrenceOwned := true
  literalE6RecurrenceOwned := true
  finiteSumNormalFormsOwned := true
  qTargetIdentifiedWithMathlibQ := true
  agdaPrimitiveExtractionInhabited := false
  finiteRecurrenceBoundToExtractedAgdaObject := false
  finiteToInfiniteLimitTransportPaid := true
  infiniteLimitIdentifiedWithMathlibE4E6 := true
  discriminantNumeratorLimitCompiled := true
  normalizedDeltaLimitCompiled := true
  normalizedDeltaPackagedAsWeight12ModularForm := true
  realStructureConjugationLawOwned := true
  weight12SActionOwned := true
  concreteInvConjReflectionOwned := true
  unitNormFixedLocusOwned := true
  fixedLocusValueIdentityOwned := true
  jWeightZeroTargetOwned := true
  jSInvariantOwned := true
  jConjugationOwned := true
  jInverseConjugationOwned := true
  jUnitCircleRealityOwned := true

end

end Integration.MoonshineEisensteinAgdaTarget
