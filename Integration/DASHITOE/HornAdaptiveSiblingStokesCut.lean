import Mathlib

/-!
# Sibling-adaptive Hatcher holonomy budget (conditional rational carrier)

Original group marking: Hatcher, Algebraic Topology, Ex. 2B.2.
Original commutator surjectivity: Morikuni Gotô, JMSJ 1 (1949), 270-272.
Already selected SU(3) W and positive group representation: Agda PR #1247.
Original sharp 2^n branch and curved eta: Agda #1249 / Lean #84.

New conditional step coefficient:
  d([A,B]) ≤ 2*d(A)*min(1,d(B))
  c_k=2*min(1,d(sibling_k))
  d(parent) ≤ eta_k+c_k*d(chosen child).
The analytic operator norm/Stokes source must supply each hstep.
This file does not construct a horn embedding, a physical gauge field or
a kernel-verified SU(3) operator-norm theorem.
-/

namespace DASHIHornAdaptiveSibling

/-- Rational upper multiplier for a source-certified unitary sibling gap. -/
def amp (siblingGap : ℚ) : ℚ := 2 * min (1 : ℚ) siblingGap

theorem amp_nonneg (s : ℚ) (hs : 0 ≤ s) : 0 ≤ amp s := by
  unfold amp
  have hmin : 0 ≤ min (1 : ℚ) s := le_min (by norm_num) hs
  linarith

theorem amp_le_two (s : ℚ) : amp s ≤ 2 := by
  unfold amp
  have hmin : min (1 : ℚ) s ≤ 1 := min_le_left _ _
  linarith

/-- Each entry carries (sibling holonomy gap, based curvature defect).
The list runs from the root towards a selected descendant. -/
def envelope : List (ℚ × ℚ) → ℚ → ℚ
  | [], leaf => leaf
  | (sibling, defect) :: tail, leaf =>
      defect + amp sibling * envelope tail leaf

/-- Genuinely SOURCE-SUPPLIED local chain. We do not infer its
one-step estimates from mere homotopy for curved Wilson loops. -/
inductive CertifiedChain : List (ℚ × ℚ) → ℚ → ℚ → Prop where
  | nil (x : ℚ) : CertifiedChain [] x x
  | cons (sibling defect root child leaf : ℚ) (tail : List (ℚ × ℚ))
      (hstep : root ≤ defect + amp sibling * child)
      (hchild : CertifiedChain tail child leaf) :
      CertifiedChain ((sibling, defect) :: tail) root leaf

/-- General heterogeneous product/sum envelope with NO 2^n
relaxation. No hypothesis requiring the chosen leaf to be short. -/
theorem chain_envelope
    {entries : List (ℚ × ℚ)} {root leaf : ℚ}
    (hchain : CertifiedChain entries root leaf)
    (hgap : ∀ p ∈ entries, 0 ≤ p.1) :
    root ≤ envelope entries leaf := by
  induction hchain with
  | nil x =>
      simp [envelope]
  | cons sibling defect root child leaf tail hstep hchild ih =>
      have hs : 0 ≤ sibling := hgap (sibling, defect) (by simp)
      have htail : ∀ p ∈ tail, 0 ≤ p.1 := by
        intro p hp
        apply hgap p
        simp [hp]
      have hc : child ≤ envelope tail leaf := ih htail
      have hm : 0 ≤ amp sibling := amp_nonneg sibling hs
      have hmul := mul_le_mul_of_nonneg_left hc hm
      change root ≤ defect + amp sibling * envelope tail leaf
      linarith

theorem selectedRootAdaptiveRejection
    {entries : List (ℚ × ℚ)} {root leaf leafCap : ℚ}
    (hchain : CertifiedChain entries root leaf)
    (hgap : ∀ p ∈ entries, 0 ≤ p.1)
    (hroot : 1 < root)
    (hleaf : leaf ≤ leafCap)
    (hleafGap : 0 ≤ leafCap)
    (hcap : envelope entries leafCap ≤ 1) : False := by
  have hrootBudget := chain_envelope hchain hgap
  have hmono : envelope entries leaf ≤ envelope entries leafCap := by
    induction entries with
    | nil => simpa [envelope] using hleaf
    | cons hd tail ih =>
        have hs : 0 ≤ hd.1 := hgap hd (by simp)
        have hm : 0 ≤ amp hd.1 := amp_nonneg hd.1 hs
        simp only [envelope]
        have hmul := mul_le_mul_of_nonneg_left ih hm
        linarith
  have hrootLe : root ≤ 1 := le_trans hrootBudget (le_trans hmono hcap)
  exact (not_lt_of_ge hrootLe hroot)

end DASHIHornAdaptiveSibling
