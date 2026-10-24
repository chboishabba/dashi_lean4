import Mathlib

/-!
# Navier–Stokes unforced A/B: two source-level analytic reductions

A (whole-space): the *actual scalar resolvent coefficient* on a punctured
positive heat rate `a = ν |ξ|²` has an exact finite difference identity.
This yields a non-artificial one-sided low-frequency saturation bound.
The physical Fourier transform, Gram identification and finite-energy
majorant are separate source obligations.

B (periodic): the exact physical noncore/core R440 defect is a signed
bipartite covariance. Its finite-pairwise signed form admits a sharp,
non-absolute oscillation-square envelope, and vanishes identically on
pairs with equal input-Laplacian rates.

These are DASHI mathematical refinements of the existing (not new)
canonical A/B owner definitions:
  dashi_agda/DASHI/Physics/Closure/
    NSWholeSpaceCanonicalPairSaturationOriginExact.agda
    NSTriadKNFiniteBipartiteCovarianceExact.agda
    NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact.agda

**2026-10-24 B4 source no-go:** A fixed, globally smooth unforced
shear solution with Fourier support ±e_x, ±e_y makes the literal
*full-output-fibre* R440 noncore/core signed covariance diverge under
cutoff padding by zero-amplitude incidences, whereas its Core-Core
companion stabilizes. The upstream classifier has STRICT +3 shell gaps.
This new negative control is in
dashi_agda/scripts/ns_b4_literal_padding_adversary.py and the canonical
NSProofControl roadmap. Consequently the finite pairwise Young bound
below CANNOT be promoted to the desired cutoff-uniform B4 physical
payment if local ED is cutoff-uniform. Reformulate against the
zero-padding-invariant raw R440 modal amplitude rather than inventing
another estimate on the defective centering.

The propositions below are NOT the unforced global regularity theorem:
the finite B bound is not uniform in physical shell count, and A still
requires the same-object physical Fourier/majorant producer.
-/

namespace NSUnforcedAnalyticCuts

section WholeSpaceOrigin

/-- Literal positive-heat centered resolvent saturation coefficient. -/
def originSaturation (a s : ℝ) : ℝ :=
  s / (a * (a + s))

/-- Exact rational-resolvent identity, without introducing a new kernel. -/
theorem originSaturation_eq_inverse_difference
    {a s : ℝ} (ha : a ≠ 0) (has : a + s ≠ 0) :
    originSaturation a s = a⁻¹ - (a + s)⁻¹ := by
  unfold originSaturation
  field_simp [ha, has]
  <;> ring

theorem originSaturation_nonneg
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    0 ≤ originSaturation a s := by
  unfold originSaturation
  exact div_nonneg hs (le_of_lt (mul_pos ha (by linarith)))

/-- The sharp saturation bound behind the A near-origin branch. -/
theorem originSaturation_le_heat_inverse
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    originSaturation a s ≤ a⁻¹ := by
  have has : 0 < a + s := by linarith
  rw [originSaturation_eq_inverse_difference (ne_of_gt ha) (ne_of_gt has)]
  have hinv : 0 ≤ (a + s)⁻¹ := inv_nonneg.mpr (le_of_lt has)
  linarith

/-- Exact stability of the scalar source coefficient under a change in
    physical centered residual. No asymptotic approximation is made. -/
theorem originSaturation_difference
    {a s t : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    originSaturation a s - originSaturation a t =
      (s - t) / ((a + s) * (a + t)) := by
  have has : 0 < a + s := by linarith
  have hat : 0 < a + t := by linarith
  rw [originSaturation_eq_inverse_difference (ne_of_gt ha) (ne_of_gt has)]
  rw [originSaturation_eq_inverse_difference (ne_of_gt ha) (ne_of_gt hat)]
  field_simp [ne_of_gt has, ne_of_gt hat]
  <;> ring

/-- The heat scale is a uniform modulus of continuity for the centered
    resolvent scalar; no artificial positivity of the *signed Gram* is used. -/
theorem originSaturation_stability
    {a s t : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |originSaturation a s - originSaturation a t|
       ≤ |s - t| / a ^ 2 := by
  rw [originSaturation_difference ha hs ht]
  have has : 0 < a + s := by linarith
  have hat : 0 < a + t := by linarith
  have hden : 0 < (a + s) * (a + t) := mul_pos has hat
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hdenLower : a ^ 2 ≤ (a + s) * (a + t) := by
    nlinarith [mul_nonneg hs ht, mul_nonneg (le_of_lt ha) hs,
      mul_nonneg (le_of_lt ha) ht]
  rw [abs_div, abs_of_pos hden]
  apply (div_le_div_iff₀ hden ha2).2
  nlinarith [mul_nonneg (abs_nonneg (s - t))
    (sub_nonneg.mpr hdenLower)]

end WholeSpaceOrigin

section PeriodicNoncoreCore

variable {ι : Type*} [DecidableEq ι]

/-- Same signed bipartite covariance as R440's noncore/core defect,
    expressed on finite incidence lists (allowing repeated cells by
    taking the carrier to be list-position indices). -/
def signedNoncoreCoreDefect
    (noncore core : Finset ι) (rate work : ι → ℝ) : ℝ :=
  ∑ i ∈ noncore, ∑ j ∈ core,
    -((rate i - rate j) * (work i - work j))

/-- A rigorous signed, frequency-oscillation-sensitive finite B4 bound.
    It does not silently manufacture cutoff-uniform physical control. -/
theorem signedDefect_le_pair_oscillation
    (noncore core : Finset ι) (rate work : ι → ℝ) :
    signedNoncoreCoreDefect noncore core rate work
      ≤ ∑ i ∈ noncore, ∑ j ∈ core,
          ((rate i - rate j) ^ 2 + (work i - work j) ^ 2) / 2 := by
  unfold signedNoncoreCoreDefect
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  nlinarith [sq_nonneg
    ((rate i - rate j) + (work i - work j))]

/-- Tunable signed Young payment. Choosing 0 < ε < 1 leaves a
    STRICTLY SUB-HALF coefficient ε/2 for the pairwise work oscillation.
    WARNING: the raw rate-oscillation term here is independent of velocity
    amplitude, so it CANNOT by itself be charged to homogeneous local ED.
    A useful physical theorem needs amplitude-weighted R440 rate differences,
    not a scalar variance floor. This is a mathematical audit bound, NOT B4. -/
theorem signedDefect_le_tunable_pair_oscillation
    (noncore core : Finset ι) (rate work : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    signedNoncoreCoreDefect noncore core rate work
      ≤ ∑ i ∈ noncore, ∑ j ∈ core,
        (ε ^ 2 * (work i - work j) ^ 2 +
          (rate i - rate j) ^ 2) / (2 * ε) := by
  unfold signedNoncoreCoreDefect
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hden : 0 < 2 * ε := mul_pos (by norm_num) hε
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg
    (ε * (work i - work j) + (rate i - rate j))]

/-- Any cross-partition with equal physical input-Laplacian multipliers
    has *zero* B4 defect, without appealing to an absolute-value estimate. -/
theorem signedDefect_zero_of_flat_cross_rates
    (noncore core : Finset ι) (rate work : ι → ℝ)
    (hequal : ∀ i ∈ noncore, ∀ j ∈ core, rate i = rate j) :
    signedNoncoreCoreDefect noncore core rate work = 0 := by
  unfold signedNoncoreCoreDefect
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [hequal i hi j hj]
  ring

end PeriodicNoncoreCore


section PhysicalR440PaddingAudit

/-!
The actual Agda R440 signed noncore/core defect is -W(M, residual),
where residual = nC*R_N+nN*R_C-rN*M_C-rC*M_N and R_X is the
input-Laplacian weighted amplitude fold. Write V_X=W(M,M_X),
W_X=W(M,R_X). Adding an amplitude-ZERO noncore triad at rate s
does not change the weighted/unweighted amplitude folds, but increments
nN by one and rN by s. Thus the actual signed defect changes by
s*V_C-W_C. In the physical shear source V_C=1, W_C=2, producing
the positive (s-2) rate excess of the exact adversary.

This is a precise algebraic padding diagnostic, not the new physical
uniform estimate. A substitute B4 target must preserve the original
unforced-NS critical-production semantics and be padding-invariant.
-/

/-- The literal four-moment scalar form of negative signed R440 work. -/
def physicalR440FusedDefect
    (nN nC rN rC vN vC wN wC : ℝ) : ℝ :=
  -(nC * wN + nN * wC - rN * vC - rC * vN)

/-- Adding a zero-amplitude noncore incidence contributes its count and
    scalar input rate, even though its modal amplitude is zero. -/
theorem physicalR440_zero_padding_increment
    (nN nC rN rC vN vC wN wC s : ℝ) :
    physicalR440FusedDefect (nN + 1) nC (rN + s) rC vN vC wN wC
      - physicalR440FusedDefect nN nC rN rC vN vC wN wC =
    s * vC - wC := by
  unfold physicalR440FusedDefect
  ring

/-- Actual shear values: V_C= W(M,M)=1 and
    W_C=W(M,2M)=2, hence positive rate excess for s>2. -/
theorem physicalR440_shear_padding_increment
    (nN nC rN rC vN wN s : ℝ) :
    physicalR440FusedDefect (nN + 1) nC (rN + s) rC vN 1 wN 2
      - physicalR440FusedDefect nN nC rN rC vN 1 wN 2 =
    s - 2 := by
  simpa using
    physicalR440_zero_padding_increment
      nN nC rN rC vN (1 : ℝ) wN (2 : ℝ) s

end PhysicalR440PaddingAudit

end NSUnforcedAnalyticCuts
