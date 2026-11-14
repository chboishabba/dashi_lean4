import Mathlib

/-!
# One FAST marked Hatcher branch obstructs any bounded FLAT SU3 image

Original source:
  A. Hatcher, Algebraic Topology, Example 2B.2, pp.171–172:
  horn meridian m_w=[m_w0,m_w1] in the OPEN exterior π1.
  Standard operator norm d(U)=||U-I||op for unitary matrices:
  0<=d(U)<=2 and d([A,B])=||AB-BA||<=2 min(d(A),d(B)).

This general theorem is stronger than the prior finite A5 one-leaf
obstruction in HornFiniteImageOneBranchCut: it needs NO FINITE IMAGE
but does require the leaf length to shrink FASTER than 2^(-depth).

Theorems below are a fully SOURCE-CONDITIONAL rational carrier:
the semantic link to actual marked Hatcher loops and a FLAT compatible
SU3 connection is NOT created here. In particular the commutator
identity is invalid for unrestricted CURVED holonomy unless a
quantified nonabelian-Stokes defect is supplied.
Independent selected W source: Agda neutrino #1247. Its exact
nontrivial root norm certificate is in Agda #1249 / Lean #84,
but no cross-PR import is assumed.
-/

namespace DASHIHornFastBranch

def grpComm {G : Type*} [Group G] (a b : G) : G :=
  a * b * a⁻¹ * b⁻¹

/-- Source analytical lemma: ||[A,B]-I||=||AB-BA||
    <=2 min(||A-I||,||B-I||). Supplied as an explicit external
    premise until the true normed SU3 matrix/holonomy owner is welded. -/
theorem oneUnitarySiblingStep
    {G : Type*} [Group G] (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hcommLinear : ∀ a b,
      d (grpComm a b) ≤ 2 * d a ∧ d (grpComm a b) ≤ 2 * d b)
    (w : List Bool) (bit : Bool) :
    d (g w) ≤ 2 * d (g (bit :: w)) := by
  rw [hrec w]
  obtain ⟨hl, hr⟩ := hcommLinear (g (false :: w)) (g (true :: w))
  cases bit with
  | false => exact hl
  | true => exact hr

/-- Any one binary descendant at depth n, no finite-image assumption. -/
theorem oneArbitraryMarkedBranchBound
    {G : Type*} [Group G] (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hcommLinear : ∀ a b,
      d (grpComm a b) ≤ 2 * d a ∧ d (grpComm a b) ≤ 2 * d b)
    (path : List Bool) :
    d (g []) ≤ (2 : ℚ) ^ path.length * d (g path.reverse) := by
  have hpath : ∀ (p base : List Bool),
      d (g base) ≤ (2 : ℚ) ^ p.length * d (g (p.reverse ++ base)) := by
    intro p
    induction p with
    | nil =>
        intro base
        simp
    | cons bit rest ih =>
        intro base
        have hstep := oneUnitarySiblingStep g d hrec hcommLinear base bit
        have hrest := ih (bit :: base)
        have hscaled :
            2 * d (g (bit :: base)) ≤
              2 * ((2 : ℚ) ^ rest.length *
                d (g (rest.reverse ++ bit :: base))) :=
          mul_le_mul_of_nonneg_left hrest (by norm_num)
        calc
          d (g base) ≤ 2 * d (g (bit :: base)) := hstep
          _ ≤ 2 * ((2 : ℚ) ^ rest.length *
                d (g (rest.reverse ++ bit :: base))) := hscaled
          _ = (2 : ℚ) ^ (bit :: rest).length *
                d (g ((bit :: rest).reverse ++ base)) := by
                simp only [List.length_cons, List.reverse_cons, List.append_assoc]
                rw [pow_succ]
                ring
  simpa using hpath path []

/-- Conditional physically marked flat length criterion, without A5. -/
theorem selectedRootOneFastBranchNoGo
    {G : Type*} [Group G] (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hcommLinear : ∀ a b,
      d (grpComm a b) ≤ 2 * d a ∧ d (grpComm a b) ≤ 2 * d b)
    (path : List Bool) (M ell : ℚ)
    (hroot : 1 < d (g []))
    (hflatLength : d (g path.reverse) ≤ M * ell)
    (hshort : (2 : ℚ) ^ path.length * (M * ell) ≤ 1) :
    False := by
  have hb := oneArbitraryMarkedBranchBound g d hrec hcommLinear path
  have hm : 0 ≤ (2 : ℚ) ^ path.length := by positivity
  have ht :
      (2 : ℚ) ^ path.length * d (g path.reverse) ≤
        (2 : ℚ) ^ path.length * (M * ell) :=
    mul_le_mul_of_nonneg_left hflatLength hm
  have hc : d (g []) ≤ 1 := le_trans hb (le_trans ht hshort)
  exact (not_lt_of_ge hc hroot)

/-- Exact rate/example witnesses. These are hypothetical geometry,
not a certified realization of the wild horned embedding. -/
theorem syntheticFastRateDepthFour :
    (2 : ℚ) ^ 4 * 100 * (1 / 8 : ℚ) ^ 4 ≤ 1 := by norm_num

theorem syntheticFastRateDepthSix :
    (2 : ℚ) ^ 6 * 100 * (1 / 5 : ℚ) ^ 6 ≤ 1 := by norm_num

/-- Heterogeneous full-leaf bounds instead of one uniform epsilon.
2*envelope(tree)=product over leaves(2*leafGap), exactly. -/
inductive GapTree where
  | leaf : ℚ → GapTree
  | node : GapTree → GapTree → GapTree

def gapEnvelope : GapTree → ℚ
  | .leaf x => x
  | .node a b => 2 * gapEnvelope a * gapEnvelope b

def twiceLeafProduct : GapTree → ℚ
  | .leaf x => 2 * x
  | .node a b => twiceLeafProduct a * twiceLeafProduct b

theorem heterogeneousCommutatorEnvelope (t : GapTree) :
    2 * gapEnvelope t = twiceLeafProduct t := by
  induction t with
  | leaf x => rfl
  | node a b ha hb =>
      simp only [gapEnvelope, twiceLeafProduct]
      calc
        2 * (2 * gapEnvelope a * gapEnvelope b) =
          (2 * gapEnvelope a) * (2 * gapEnvelope b) := by ring
        _ = twiceLeafProduct a * twiceLeafProduct b := by rw [ha,hb]


/-- Rational squared commutator/child-gap ratio for the source
explicit SU3 family A_n=diag(z,z⁻¹,1), z=(n+i)/(n-i);
B rotates first two basis vectors by 90 degrees.
Then [A_n,B]=A_n², so the ratio squared is 4n²/(n²+1).
The MATRIX/SU3 premise is verified by direct mathematical
calculation and independent local numerical matrices,
not constructed inside this rational-coefficient Lean file. -/
def optimalityRatioSquared (n : ℚ) : ℚ :=
  4 * n ^ 2 / (n ^ 2 + 1)

/-- The deficit below factor-two-squared goes to zero
along the natural-number sequence n→∞; its exact value
here is algebraic, not a topology/horn proof. -/
theorem optimalityDeficit (n : ℚ) :
    4 - optimalityRatioSquared n = 4 / (n ^ 2 + 1) := by
  have hden : n ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg n]
  unfold optimalityRatioSquared
  field_simp
  ring

theorem selectedSharpnessWitnessHundred :
    optimalityRatioSquared 100 = 40000 / 10001 := by
  norm_num [optimalityRatioSquared]


end DASHIHornFastBranch
