import Mathlib

/-!
# One FAST marked Hatcher branch obstructs any bounded FLAT SU3 image

Original source:
  A. Hatcher, Algebraic Topology, Example 2B.2, pp.171–172:
  horn meridian m_w=[m_w0,m_w1] in the OPEN exterior π1.
  Standard operator norm d(U)=||U-I||op for unitary matrices:
  0<=d(U)<=2 and d([A,B])<=2d(A)d(B).

This general theorem is stronger than the prior finite A5 one-leaf
obstruction in HornFiniteImageOneBranchCut: it needs NO FINITE IMAGE
but does require the leaf length to shrink FASTER than 4^(-depth).

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

/-- Binary child addresses prepend the chosen bit, as in the original
Hatcher finite-stage formal address owner. -/
theorem oneUnitarySiblingStep
    {G : Type*} [Group G]
    (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hgapNonneg : ∀ a, 0 ≤ d a)
    (hunitaryTwo : ∀ a, d a ≤ 2)
    (hcommBound : ∀ a b, d (grpComm a b) ≤ 2 * d a * d b)
    (w : List Bool) (bit : Bool) :
    d (g w) ≤ 4 * d (g (bit :: w)) := by
  rw [hrec w]
  have hb := hcommBound (g (false :: w)) (g (true :: w))
  cases bit with
  | false =>
    have ha := hgapNonneg (g (false :: w))
    have hc := hunitaryTwo (g (true :: w))
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hc)]
  | true =>
    have ha := hgapNonneg (g (true :: w))
    have hc := hunitaryTwo (g (false :: w))
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hc)]

/-- Follow ANY one depth-n path, with child addresses stored by prefix.
For flat monodromy, the Hatcher commutator relation supplies hrec.
Both abstract group and norm facts are deliberately explicit inputs. -/
theorem oneArbitraryMarkedBranchBound
    {G : Type*} [Group G]
    (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hgapNonneg : ∀ a, 0 ≤ d a)
    (hunitaryTwo : ∀ a, d a ≤ 2)
    (hcommBound : ∀ a b, d (grpComm a b) ≤ 2 * d a * d b)
    (path : List Bool) :
    d (g []) ≤ (4 : ℚ) ^ path.length * d (g path.reverse) := by
  have hpath : ∀ (p base : List Bool),
      d (g base) ≤ (4 : ℚ) ^ p.length *
         d (g (p.reverse ++ base)) := by
    intro p
    induction p with
    | nil =>
        intro base
        simp
    | cons bit rest ih =>
        intro base
        have hstep :=
          oneUnitarySiblingStep g d hrec hgapNonneg
            hunitaryTwo hcommBound base bit
        have hrest := ih (bit :: base)
        have hscaled :
            4 * d (g (bit :: base)) ≤
              4 * ((4 : ℚ) ^ rest.length *
                d (g (rest.reverse ++ bit :: base))) :=
          mul_le_mul_of_nonneg_left hrest (by norm_num)
        calc
          d (g base) ≤ 4 * d (g (bit :: base)) := hstep
          _ ≤ 4 * ((4 : ℚ) ^ rest.length *
                  d (g (rest.reverse ++ bit :: base))) := hscaled
          _ = (4 : ℚ) ^ (bit :: rest).length *
                d (g ((bit :: rest).reverse ++ base)) := by
                simp only [List.length_cons, List.reverse_cons,
                  List.append_assoc, List.singleton_append]
                rw [pow_succ]
                ring
  simpa using hpath path []

/-- The EXACT finite acceptance interface: if selected root gap >1,
a genuinely marked descendant of path length n cannot have a
source-controlled flat holonomy gap <= M*ell with
4^n*M*ell <=1. All physical hypotheses are explicit. -/
theorem selectedRootOneFastBranchNoGo
    {G : Type*} [Group G]
    (g : List Bool → G) (d : G → ℚ)
    (hrec : ∀ w, g w = grpComm (g (false :: w)) (g (true :: w)))
    (hgapNonneg : ∀ a, 0 ≤ d a)
    (hunitaryTwo : ∀ a, d a ≤ 2)
    (hcommBound : ∀ a b, d (grpComm a b) ≤ 2 * d a * d b)
    (path : List Bool) (M ell : ℚ)
    (hroot : 1 < d (g []))
    (hM : 0 ≤ M) (hell : 0 ≤ ell)
    (hflatLength : d (g path.reverse) ≤ M * ell)
    (hshort : (4 : ℚ) ^ path.length * (M * ell) ≤ 1) :
    False := by
  have hbranch :=
    oneArbitraryMarkedBranchBound g d hrec hgapNonneg
      hunitaryTwo hcommBound path
  have hpower : 0 ≤ (4 : ℚ) ^ path.length := by positivity
  have htransport :
      (4 : ℚ) ^ path.length * d (g path.reverse) ≤
        (4 : ℚ) ^ path.length * (M * ell) :=
    mul_le_mul_of_nonneg_left hflatLength hpower
  have : d (g []) ≤ 1 := le_trans hbranch (le_trans htransport hshort)
  exact (not_lt_of_ge this hroot)

/-- Exact rate/example witnesses. These are hypothetical geometry,
not a certified realization of the wild horned embedding. -/
theorem syntheticFastRateDepthSeven :
    (4 : ℚ) ^ 7 * 100 * (1 / 8 : ℚ) ^ 7 ≤ 1 := by norm_num

theorem syntheticFastRateDepthTwentyOne :
    (4 : ℚ) ^ 21 * 100 * (1 / 5 : ℚ) ^ 21 ≤ 1 := by norm_num

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

end DASHIHornFastBranch
