import Synthesis.RiemannSelectedPrimeSensitiveTwoScale

/-!
# RH P0: the original two-prime Weil source on a frozen-online aperture carrier

The selected four-window source is short of log 2 and therefore prime-blind.
The already source-checked TwoScale file proves the literal prime-2/prime-3
weights and the full four-channel balance, but its shifted profile changes
the on-line projective column (quadratic in amplitudes).

This module isolates the exact *conditional* carrier needed by the
eight-invariant projection: a replacement even smooth physical detector
for each endpoint, with the SAME two on-line responses, SAME signed even
moments through 8, and SAME original pole response. Unlike TwoScale, its
projective prime term is linear in its independently controlled *point*
values at log 2 and log 3.

This file does NOT prove that the carrier is inhabited by a smooth projected
aperture. That finite-codimension construction, quantitative absolute
derivative bounds and the independent RH strict estimate are separate P0
obligations. No RH/GRH assertion is made.
-/

noncomputable section

namespace Synthesis

open MeasureTheory
open scoped Real

/-- The exact contribution of each genuine prime in the even cone.
The factor FOUR is essential: the single sample has factor 2 and the
two ±s sampling radii provide another factor 2. -/
theorem primeAperture_literalPrimeSummand_zero_of_four_le
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) (n : ℕ) (hn : 4 ≤ n) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          g t s (Real.log n)
        + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          g t s (-Real.log n)) = 0 := by
  have hp := hfar n hn
  have hm : g (-Real.log n) = 0 := by
    rw [heven (Real.log n)]
    exact hp
  simp [Zeta23Bridge.LiteralWeilParityBalance.sampleTest, hp, hm]

theorem primeAperture_primeTerm_eq_two_summands
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s) =
    ∑ n ∈ ({2,3} : Finset ℕ),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
            g t s (Real.log n)
          + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
            g t s (-Real.log n)) := by
  unfold Zeta23Bridge.LiteralWeilParityBalance.primeTerm
  apply tsum_eq_sum
  intro n hn
  have hne2 : n ≠ 2 := by
    intro h
    exact hn (by simp [h])
  have hne3 : n ≠ 3 := by
    intro h
    exact hn (by simp [h])
  by_cases h4 : 4 ≤ n
  · exact primeAperture_literalPrimeSummand_zero_of_four_le
      heven hfar t s n h4
  · have hn4 : n < 4 := Nat.lt_of_not_ge h4
    interval_cases n <;>
      simp [hne2, hne3, ArithmeticFunction.vonMangoldt]

/-- Exact Zeta23 prime term for an arbitrary original-compatible even
two-port aperture; it is not a hand-written replacement arithmetic sum. -/
theorem primeAperture_primeTerm_eq_two_real_terms
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s) =
    (((2 : ℝ) *
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
         * g (Real.log 2) * Real.cos ((s-t)*Real.log 2)
       + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
         * g (Real.log 3) * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  rw [primeAperture_primeTerm_eq_two_summands heven hfar t s]
  simp only [Finset.sum_insert (by simp : (2:ℕ) ∉ ({3}:Finset ℕ)),
    Finset.sum_singleton]
  rw [Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      heven t s 2,
    Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      heven t s 3]
  push_cast
  ring

/-- EXACT prime-2/prime-3 even channel. In particular the output is not
an arbitrary sign: both original t-phases are retained. -/
theorem primeAperture_primeChannel_eq
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      g t s =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * g (Real.log 2) * Real.cos (s*Real.log 2)
        * Real.cos (t*Real.log 2)
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * g (Real.log 3) * Real.cos (s*Real.log 3)
        * Real.cos (t*Real.log 3)) := by
  change
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s))
    +
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t (-s))) = _
  rw [primeAperture_primeTerm_eq_two_real_terms heven hfar t s,
      primeAperture_primeTerm_eq_two_real_terms heven hfar t (-s)]
  simp only [Zeta23Bridge.LiteralWeilParityBalance.reim,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  calc
    _ =
      (2 : ℝ) *
        ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * g (Real.log 2) *
          (Real.cos ((s-t)*Real.log 2)
            + Real.cos ((-s-t)*Real.log 2))
         + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * g (Real.log 3) *
          (Real.cos ((s-t)*Real.log 3)
            + Real.cos ((-s-t)*Real.log 3))) := by ring
    _ = _ := by
      rw [threeTap_prime_cosine_pair s t (Real.log 2),
          threeTap_prime_cosine_pair s t (Real.log 3)]
      ring

/-- Literal projective prime source. The two online responses must be
sampled on the SAME detector (not a replacement normalized fixture). -/
theorem primeAperture_primeProjective_eq
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t r : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      g t r =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * g (Real.log 2) * Real.cos (t*Real.log 2)
        * twoScalePrimeShape g r (Real.log 2)
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * g (Real.log 3) * Real.cos (t*Real.log 3)
        * twoScalePrimeShape g r (Real.log 3)) := by
  unfold Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.channelProjectiveDefect
    twoScalePrimeShape
  rw [primeAperture_primeChannel_eq heven hfar t (2*r),
      primeAperture_primeChannel_eq heven hfar t r]
  ring

/-- The original four-window *atomic* Fourier-response determinant.
This is used only as a source-local small-R nondegeneracy seed; the
small-R transfer for the smooth selected witness is a separate theorem. -/
def quarticFourPrimeApertureAtomicResponseDet
    (muHalf muTwo : ℝ) : ℝ :=
  ((1/2 : ℝ) - muHalf) * ((5/6 : ℝ) + muTwo)
    - ((1 : ℝ) + muHalf) * ((1/2 : ℝ) - muTwo)

theorem quarticFourPrimeApertureAtomicResponseDet_eq
    (muHalf muTwo : ℝ) :
    quarticFourPrimeApertureAtomicResponseDet muHalf muTwo
      = -(1/12 : ℝ) - (4/3 : ℝ)*muHalf + (3/2 : ℝ)*muTwo := by
  unfold quarticFourPrimeApertureAtomicResponseDet
  ring

/-- Exact source corridor: the two atomic endpoint on-line vectors are
nonproportional throughout the FULL original mu corridors. -/
theorem quarticFourPrimeApertureAtomicResponseDet_neg
    {muHalf muTwo : ℝ}
    (hHalf :
      |muHalf - quarticFourAtomicMu (1/2)| <=
        quarticFourAtomicMuRadius)
    (hTwo :
      |muTwo - quarticFourAtomicMu (2/3)| <=
        quarticFourAtomicMuRadius) :
    quarticFourPrimeApertureAtomicResponseDet muHalf muTwo < 0 := by
  have hmuHalf : quarticFourAtomicMu (1/2) = -(1/78 : ℝ) := by
    norm_num [quarticFourAtomicMu]
  have hmuTwo : quarticFourAtomicMu (2/3) = (1/162 : ℝ) := by
    norm_num [quarticFourAtomicMu]
  rw [hmuHalf] at hHalf
  rw [hmuTwo] at hTwo
  unfold quarticFourAtomicMuRadius at hHalf hTwo
  obtain ⟨hHL, hHU⟩ := abs_le.mp hHalf
  obtain ⟨hTL, hTU⟩ := abs_le.mp hTwo
  rw [quarticFourPrimeApertureAtomicResponseDet_eq]
  linarith

/-- The actual physical projective moment, not a stand-in atomic moment. -/
def primeAperturePhysicalMoment
    (g : ℝ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ,
    (4*g u *
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
         * Real.cos (2*r*u)
       - Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)
         * Real.cos (r*u))) * u^k

/-!
## E0 explicit source-construction route — the even monic order-52 annihilator

The external exact SymPy regression
  check_rh_p0_exact_differential_annihilator_20261123.py
constructs a source-native, NON-rank-based smooth solution to every E0 moment
and pole integral condition, for each fixed original W and height t.

Write D=d/du and r=t/16. Take the even monic constant-coefficient operator

  (D²+r²)^9 (D²+4r²)^9
  * Π_{c=1,2} Π_{sign=±1}
      [((D-1/2)²+(t+sign*c*r)²)
       ((D+1/2)²+(t+sign*c*r)²)].

The two first factors annihilate u^k*cos(r*u) and
u^k*cos(2*r*u) for k≤8; the remaining factors annihilate
cosh(u/2)*cos(t*u)*cos(c*r*u), c=1,2. It is even in D,
so its formal adjoint is itself. Applying it to an even C-infinity bump
compactly supported near ±log2 or ±log3 gives an EVEN C-infinity compact
h. Integration by parts forces the exact eight original integral
constraints to ZERO. Choosing the starting bump's 0..51 jets to be zero
and its 52nd derivative to be one at the designated prime yields
h(log p)=1 because the operator is MONIC; disjoint supports give zero
at the other prime and all n≥4.

This construction is a mathematical E0 existence proof and exact SymPy
regression, NOT a Lean proof body in this file. To instantiate the carrier,
weld the high-order derivative operator, compact support, formal adjoint
and prescribed-jet bump into Mathlib. The high derivative order makes
quantitative E2 norms (including sixth/eighth absolute shells) a MAJOR
independent obligation; it cannot be called a ready-to-use RH test.
-/

/-- Scalar symbol of the real even fourth-order annihilator for
exp(±u/2)*cos(omega*u). This expression is even in D. -/
def primeAperturePoleModeSymbol (omega D : ℝ) : ℝ :=
  (D^2 + omega^2 + (1/4 : ℝ))^2 - D^2

theorem primeAperturePoleModeSymbol_eq_shifted
    (omega D : ℝ) :
    primeAperturePoleModeSymbol omega D
      = ((D-(1/2 : ℝ))^2+omega^2)
          * ((D+(1/2 : ℝ))^2+omega^2) := by
  unfold primeAperturePoleModeSymbol
  ring

/-- The complete source annihilator symbol is monic of formal order 52:
two quadratic factors to power nine, then four fourth-order pole factors. -/
def primeApertureAnnihilatorSymbol (t r D : ℝ) : ℝ :=
  (D^2+r^2)^9 * (D^2+(2*r)^2)^9
    * primeAperturePoleModeSymbol (t-r) D
    * primeAperturePoleModeSymbol (t+r) D
    * primeAperturePoleModeSymbol (t-2*r) D
    * primeAperturePoleModeSymbol (t+2*r) D

/-- Source-level algebraic parity. The analytic differential-operator lift,
compact support, 52-fold integration-by-parts and port-jet realization remain
mathematical proofs only, NOT kernel-checked in this file. -/
theorem primeApertureAnnihilatorSymbol_even
    (t r D : ℝ) :
    primeApertureAnnihilatorSymbol t r (-D)
      = primeApertureAnnihilatorSymbol t r D := by
  simp [primeApertureAnnihilatorSymbol, primeAperturePoleModeSymbol]

/-!
## E2 normalized-annihilator correction, avoiding 52nd-jet derivative blowup

The monic order-52 annihilator is exact but a poor conditioning
normalization. Define Q_t(D)=A_t(D)/A_t(0), r=t/16. For t>0,
A_t(0)>0. Q_t is EVEN, its constant coefficient is 1, and it
annihilates the SAME eight integral source weights.

An external exact-rational source regression proves the coefficientwise
majorant for every t>=200:

    Q_t(D)=sum_(j=0)^26 q_j(t) D^(2j),
    q_0(t)=1,
    0<=q_j(t)<=binom(26,j)(256/t²)^j.

Choose an even compact smooth FLAT-TOP function b_p, equal one in a
neighborhood of ±log p and zero at the other prime logs. Then
Q_t(D)b_p(log p)=1 for EVERY t>0, since b_p's positive derivatives
vanish at that evaluation. Exact integral constraints still vanish by
the same even formal-adjoint and weight-annihilation argument.

For each fixed smooth b_p and derivative k, the finite source bound

    ||(Q_t(D)b_p)^(k)||1 <=
      sum_j binom(26,j)(256/t²)^j ||b_p^(k+2j)||1

converges to ||b_p^(k)||1 as t->infty. This is a mathematical E2
Sobolev INCREMENT estimate, NOT a theorem formalized below, and it
does not certify the full original far/zero/Gamma/post-sixth budget.
-/

/-- Non-monic, height-normalized source operator *symbol*. The analytic
52nd-order differential operator itself remains an E0 Mathlib weld. -/
def primeApertureNormalizedAnnihilatorSymbol (t D : ℝ) : ℝ :=
  primeApertureAnnihilatorSymbol t (t/16) D /
    primeApertureAnnihilatorSymbol t (t/16) 0

theorem primeApertureAnnihilatorSymbol_at_zero_pos
    {t : ℝ} (ht : 0 < t) :
    0 < primeApertureAnnihilatorSymbol t (t/16) 0 := by
  unfold primeApertureAnnihilatorSymbol primeAperturePoleModeSymbol
  positivity

theorem primeApertureNormalizedAnnihilatorSymbol_at_zero
    {t : ℝ} (ht : 0 < t) :
    primeApertureNormalizedAnnihilatorSymbol t 0 = 1 := by
  unfold primeApertureNormalizedAnnihilatorSymbol
  exact div_self (primeApertureAnnihilatorSymbol_at_zero_pos ht).ne'

theorem primeApertureNormalizedAnnihilatorSymbol_even
    (t D : ℝ) :
    primeApertureNormalizedAnnihilatorSymbol t (-D)
      = primeApertureNormalizedAnnihilatorSymbol t D := by
  unfold primeApertureNormalizedAnnihilatorSymbol
  rw [primeApertureAnnihilatorSymbol_even]

/-!
## P0 geometric normalization and existing punctured-27 source correspondence

The old general \`256/t²\` estimate is exactly \`1/r²\`, r=t/16.
There are 26 effective *bounding quadratic slots* grouped:

  9 on-line (frequency r, weight 1),
  8 central (four pole quartics, each majorized by two quadratic
     slots with respective weights 1/196,1/225,1/289,1/324),
  9 on-line (frequency 2r, weight 1/4).

This matches the ORIGINAL \`27=1+(9+8+9)\` punctured balanced-trit
INDEX CHART of DASHI, not an Albert product / F4 action.

With z=(D/r)² and delta=1/(4r²), each pole quartic at k*r,
k in {14,15,17,18}, becomes

  1+2(k²-delta)/(k²+delta)²*z + 1/(k²+delta)²*z²

and is coefficientwise <= (1+z/k²)². Hence
Q_t(D) coefficientwise <= geometric shell envelope below.
The upper envelope is SHARP coefficientwise as t->infinity.
Exact rational polynomial verification lives in DASHI's
\`check_rh_p0_punctured27_geometric_majorant_20261123.py\`.
The source inequality has NOT been kernel-proved in this Lean file.

The canonical original 26 non-origin points are 13 antipodal pairs,
but on the outer two 9-sheets the weights 1 and 1/4 are DIFFERENT.
Therefore an unoriented 13-axis quotient would discard analytic data.
The 26 bounding factor slots are not canonically the 26 grades
j=1..26 of the degree-26 z-polynomial (although both are 26-sets).
-/

/-- The original radius makes the 256/t² estimate a unit coefficient. -/
theorem primeApertureGeometricInverseRadius
    {t : ℝ} (ht : t ≠ 0) :
    (256 : ℝ) / t^2 = 1 / (t/16)^2 := by
  field_simp [ht]
  ring

/-- Both on-line and four pole frequencies are exact integer multiples of r. -/
theorem primeApertureOriginalPoleFrequencies (t : ℝ) :
    t - 2*(t/16) = 14*(t/16)
    ∧ t - (t/16) = 15*(t/16)
    ∧ t + (t/16) = 17*(t/16)
    ∧ t + 2*(t/16) = 18*(t/16) := by
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

/-- Exact dimensionless limiting coefficientwise E2 envelope.
THIS is a scalar polynomial definition; no claim of new Lie action. -/
def primeAperturePuncturedShellMajorantSymbol (z : ℝ) : ℝ :=
  (1+z)^9 * (1+z/4)^9 *
    (1+z/196)^2 * (1+z/225)^2 *
    (1+z/289)^2 * (1+z/324)^2

theorem primeAperturePuncturedShellMajorantSymbol_at_zero :
    primeAperturePuncturedShellMajorantSymbol 0 = 1 := by
  norm_num [primeAperturePuncturedShellMajorantSymbol]

/-- P0 E0 carrier: exactly which source facts the finite-codimension
projection must produce. Inhabitation is NOT claimed here. -/
structure QuarticFourFrozenPrimeAperture (t : ℝ) where
  W : QuarticFourSignedPolePair t
  half : ℝ → ℝ
  two : ℝ → ℝ
  halfSmooth : ContDiff ℝ 2 half
  twoSmooth : ContDiff ℝ 2 two
  halfCompact : HasCompactSupport half
  twoCompact : HasCompactSupport two
  halfEven : ∀ u, half (-u) = half u
  twoEven : ∀ u, two (-u) = two u
  halfPrimeTail : ∀ n : ℕ, 4 ≤ n → half (Real.log n) = 0
  twoPrimeTail : ∀ n : ℕ, 4 ≤ n → two (Real.log n) = 0
  halfResp1 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp half 0 (t/16) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) 0 (t/16)
  halfResp2 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp half 0 (2*(t/16)) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) 0 (2*(t/16))
  twoResp1 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp two 0 (t/16) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) 0 (t/16)
  twoResp2 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp two 0 (2*(t/16)) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) 0 (2*(t/16))
  halfMoments :
    ∀ k : ℕ, (k=2 ∨ k=4 ∨ k=6 ∨ k=8) →
      primeAperturePhysicalMoment half (t/16) k =
      primeAperturePhysicalMoment
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) (t/16) k
  twoMoments :
    ∀ k : ℕ, (k=2 ∨ k=4 ∨ k=6 ∨ k=8) →
      primeAperturePhysicalMoment two (t/16) k =
      primeAperturePhysicalMoment
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) (t/16) k
  halfPole :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      half t (t/16) =
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) t (t/16)
  twoPole :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      two t (t/16) =
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) t (t/16)

/-- Exact source fourth/sixth/eighth (and second) moment preservation
on the new same-W signed pair. It is a theorem, not a Taylor estimate. -/
def QuarticFourFrozenPrimeAperture.signedMoment
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t)
    (k : ℕ) : ℝ :=
  A.W.poleTwo * primeAperturePhysicalMoment A.half (t/16) k
    - A.W.poleHalf * primeAperturePhysicalMoment A.two (t/16) k

theorem QuarticFourFrozenPrimeAperture.signedMoment_eq_original
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t)
    (k : ℕ) (hk : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8) :
    A.signedMoment k =
      A.W.poleTwo *
        primeAperturePhysicalMoment
          (quarticFourPhysicalDetector A.W.R (1/2) A.W.muHalf t)
          (t/16) k
      - A.W.poleHalf *
        primeAperturePhysicalMoment
          (quarticFourPhysicalDetector A.W.R (2/3) A.W.muTwo t)
          (t/16) k := by
  unfold QuarticFourFrozenPrimeAperture.signedMoment
  rw [A.halfMoments k hk, A.twoMoments k hk]

/-- Reuse the original signed-pole coefficients. The source of EVERY channel
below is the SAME pair of extended detectors. -/
def QuarticFourFrozenPrimeAperture.channel
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t)
    (C : (ℝ → ℝ) → ℝ → ℝ → ℝ) : ℝ :=
  A.W.poleTwo * C A.half t (t/16)
    - A.W.poleHalf * C A.two t (t/16)

/-- Frozen original pole weights still cancel *exactly*, without assuming
the extended detectors satisfy the old short-support theorem. -/
theorem QuarticFourFrozenPrimeAperture.poleChannel_zero
    {t : ℝ} (ht : 0 < t)
    (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      = 0 := by
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [A.halfPole, A.twoPole]
  convert A.W.literalPole_cancel ht using 1 <;> ring

/-- The source-exact signed two-prime term, with no eps² projective error
because both original on-line Fourier responses are frozen. -/
theorem QuarticFourFrozenPrimeAperture.signedPrime_eq_frozen
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * Real.cos (t*Real.log 2)
        * (A.W.poleTwo * A.half (Real.log 2)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (1/2) A.W.muHalf t)
                 (t/16) (Real.log 2)
           - A.W.poleHalf * A.two (Real.log 2)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (2/3) A.W.muTwo t)
                 (t/16) (Real.log 2))
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * Real.cos (t*Real.log 3)
        * (A.W.poleTwo * A.half (Real.log 3)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (1/2) A.W.muHalf t)
                 (t/16) (Real.log 3)
           - A.W.poleHalf * A.two (Real.log 3)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (2/3) A.W.muTwo t)
                 (t/16) (Real.log 3))) := by
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [primeAperture_primeProjective_eq A.halfEven A.halfPrimeTail t (t/16),
      primeAperture_primeProjective_eq A.twoEven A.twoPrimeTail t (t/16)]
  unfold twoScalePrimeShape
  rw [A.halfResp1, A.halfResp2, A.twoResp1, A.twoResp2]
  ring

/-- The full ORIGINAL Zeta23 four-channel explicit formula transports to
the extended pair, while the prime term is now explicitly present. This
is only a completed SOURCE IDENTITY, not the missing independent strict
upper estimate. -/
theorem QuarticFourFrozenPrimeAperture.completedCluster_eq_fourChannels
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect := by
  have hhalf :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      A.halfSmooth A.halfCompact A.halfEven t (t/16)
  have htwo :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      A.twoSmooth A.twoCompact A.twoEven t (t/16)
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [hhalf, htwo]
  ring

theorem QuarticFourFrozenPrimeAperture.completedCluster_eq_off_prime_gamma
    {t : ℝ} (ht : 0 < t) (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect := by
  have hs := A.completedCluster_eq_fourChannels
  have hp := A.poleChannel_zero ht
  linarith

end Synthesis
