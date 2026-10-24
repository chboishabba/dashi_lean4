import Mathlib

/-!
# Conditional sibling-adaptive Hatcher holonomy budget
Attribution: Hatcher (AT Example 2B.2), Gotô (JMSJ 1949);
existing Agda PR #1247 already supplies positive selected SU3 representation,
#1244 owns geometric horn/C3, #1249 and Lean #84 own earlier sharp 2^n
and curved eta bounds. The new theorem here is a rational conditional envelope.

Analytic source step d(parent) <= eta+2*min(1,d(sibling))*d(child)
requires genuine marked based loops and normed unitary commutator physics;
for a curved connection eta needs a REAL based Stokes homotopy.
No topological marking, physical gauge field or kernel receipt claimed.
-/
namespace DASHIHornAdaptiveSibling

/-- Sibling-sensitive commutator coefficient, applied ONLY when the
source supplies a nonnegative upper bound on the sibling's norm gap. -/
def amp (s : ℚ) : ℚ := 2 * min (1 : ℚ) s

theorem amp_nonneg (s : ℚ) (hs : 0 ≤ s) : 0 ≤ amp s := by
  unfold amp
  have h : 0 ≤ min (1 : ℚ) s := le_min (by norm_num) hs
  linarith

theorem amp_le_two (s : ℚ) : amp s ≤ 2 := by
  unfold amp
  have h : min (1 : ℚ) s ≤ 1 := min_le_left _ _
  linarith

/-- Ordered root-first list: (sibling gap, based holonomy defect). -/
def envelope : List (ℚ × ℚ) → ℚ → ℚ
  | [], leaf => leaf
  | (s, e) :: tail, leaf => e + amp s * envelope tail leaf

/-- This is a CERTIFIED source gate; arbitrary pi1 homotopy does
not supply hstep for curved Wilson matrices. -/
inductive CertifiedChain : List (ℚ × ℚ) → ℚ → ℚ → Prop where
  | nil (x : ℚ) : CertifiedChain [] x x
  | cons (s e root child leaf : ℚ) (tail : List (ℚ × ℚ))
      (hs : 0 ≤ s)
      (hstep : root ≤ e + amp s * child)
      (hchild : CertifiedChain tail child leaf) :
      CertifiedChain ((s, e) :: tail) root leaf

/-- No uniform sibling bounds, fast-shrinking leaf or flatness is assumed;
every curvature defect is an explicitly supplied number. -/
theorem chain_envelope
    {entries : List (ℚ × ℚ)} {root leaf : ℚ}
    (h : CertifiedChain entries root leaf) :
    root ≤ envelope entries leaf := by
  induction h with
  | nil x => simp [envelope]
  | cons s e root child leaf tail hs hstep hchild ih =>
      have hm : 0 ≤ amp s := amp_nonneg s hs
      have hmul := mul_le_mul_of_nonneg_left ih hm
      change root ≤ e + amp s * envelope tail leaf
      linarith

/-- A cap on the leaf gap transports through every nonnegative multiplier,
without requiring that the chosen leaf has a short geometric representative. -/
theorem chain_envelope_cap
    {entries : List (ℚ × ℚ)} {root leaf : ℚ}
    (h : CertifiedChain entries root leaf)
    (cap : ℚ) (hleaf : leaf ≤ cap) :
    root ≤ envelope entries cap := by
  induction h with
  | nil x => simpa [envelope] using hleaf
  | cons s e root child leaf tail hs hstep hchild ih =>
      have hm : 0 ≤ amp s := amp_nonneg s hs
      have ht : child ≤ envelope tail cap := ih
      have hmul := mul_le_mul_of_nonneg_left ht hm
      change root ≤ e + amp s * envelope tail cap
      linarith

/-- Previously certified selected source W has norm gap strictly >1.
Reject a real source realization only once actual sibling/defect caps
force the root bound <=1. -/
theorem selectedRootAdaptiveRejection
    {entries : List (ℚ × ℚ)} {root leaf leafCap : ℚ}
    (h : CertifiedChain entries root leaf)
    (hroot : 1 < root)
    (hleaf : leaf ≤ leafCap)
    (hcap : envelope entries leafCap ≤ 1) : False := by
  have bound := chain_envelope_cap h leafCap hleaf
  exact (not_lt_of_ge (le_trans bound hcap) hroot)


/-!
## 2026-10-25 finite 3-stage and inverse-gauge-cost max-cut

The original norm inequality is analytic (not proved here); the three-stage
conditional rational cap is exact. A source-selected root with gap >1
cannot satisfy a real three-stage chain having any two siblings <=1/4,
third sibling <=2, zero curvature defects, and leaf gap <=2.
Original mathematical owner of marked commutators: Hatcher.
Original compact Lie group commutator theorem: Gotô (1949).
Previous SU3 positive bridge: Agda neutrino PR #1247.
-/

/-- Two short siblings can appear in any positions. All leaf estimates
remain the universal unitary d(U)<=2: no geometric leaf bound assumed. -/
theorem twoSmallSiblingA :
    envelope [(1/4, 0), (1/4, 0), (2, 0)] (2 : ℚ) = 1 := by
  norm_num [envelope, amp]

theorem twoSmallSiblingB :
    envelope [(1/4, 0), (2, 0), (1/4, 0)] (2 : ℚ) = 1 := by
  norm_num [envelope, amp]

theorem twoSmallSiblingC :
    envelope [(2, 0), (1/4, 0), (1/4, 0)] (2 : ℚ) = 1 := by
  norm_num [envelope, amp]

/-- DEPTH-THREE PRODUCT-ONLY negative control: this bound equals 4.
The shorter-prefix direct linear sibling criterion may STILL reject
from this same input (in particular root sibling gap 1/4 gives 1/2).
Do not infer that a single small sibling cannot suffice. -/
theorem oneShortDepthThreeProductIsLoose :
    envelope [(1/4, 0), (2, 0), (2, 0)] (2 : ℚ) = 4 := by
  norm_num [envelope, amp]

/-- The inverse regularity acceptance interface. Its bounded-gauge
source must supply an actual length law and the analytical root-bound
hypothesis. It does NOT construct any such horn metric. -/
theorem necessaryGaugeCoefficientGrowth
    (n : ℕ) (root M L0 q : ℚ)
    (hroot : 1 < root)
    (hsource : root ≤
      2 * (2 * M * L0) ^ n * q ^ (n * (n - 1) / 2)) :
    (1/2 : ℚ) <
      (2 * M * L0) ^ n * q ^ (n * (n - 1) / 2) := by
  have h := lt_of_lt_of_le hroot hsource
  linarith

/-- Precise finite threshold at a synthetic depth 7, q=3/4,
M=3, L0=1/3. A hypothetical genuine marked flat source with
these bounds could not have the previously selected root gap >1. -/
theorem syntheticDepthSevenNoGo :
    2 * (2 * (3 : ℚ) * (1/3)) ^ 7 *
      (3/4 : ℚ) ^ (7 * (7 - 1) / 2) ≤ 1 := by
  norm_num


end DASHIHornAdaptiveSibling
