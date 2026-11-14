import Synthesis.MillenniumBSDCMRealAffineLocusExact
import Mathlib.Tactic

/-!
# BSD K1: COMPLETE ORIGINAL REAL NONEXCEPTIONAL x-T SIGN IMAGE

For the LITERAL original curve y^2=x^3-x over real numbers, not an
auxiliary Boolean model or arbitrary set of candidate square classes,
consider the image of its nonexceptional affine points (x != 0,1)
under the ACTUAL two signs of x and x-1.

* Necessary direction: the already proved exact real affine locus and
  cmRealAffine_kummerCoordinateSignsAgree.
* Sufficiency: construct two genuinely NONEXCEPTIONAL real points
  at x=2,y=sqrt(6), and x=-1/2,y=sqrt(3/8).
  These realize precisely the (++), (--) pairs.
* Signs are the real square-class images of original Stoll x-T
  nonexceptional coordinates. No alternate curve is used.

This pays actual real sign IMAGE on affine points.
It does NOT construct real Galois H1(E[2]) Kummer equivalence,
identify E(R)/2E(R), Sha[2] or any BSD formula.

Source: original #107 CM BSD branch, E:y2=x3-x,
classical 2-descent in Silverman, Arithmetic of Elliptic Curves X.
K0 current-head Lean kernel/axiom admission still pending.
-/

namespace Synthesis.Millennium.BSD

/-- Literal source image of two ordinary real Kummer signs,
with actual E(R) equation retained as a witness. -/
def cmOriginalRealNonexceptionalXTSignImage : Set (Bool × Bool) :=
  {c | ∃ x y : ℝ,
    y ^ 2 = x ^ 3 - x ∧
    x ≠ 0 ∧ x ≠ 1 ∧
    c = (decide (x < 0), decide (x - 1 < 0))}

/-- Positive non-torsion real point x=2,y=sqrt 6. -/
theorem cmOriginalRealXTPositiveSignsRealized :
    (false, false) ∈ cmOriginalRealNonexceptionalXTSignImage := by
  refine ⟨2, Real.sqrt (6 : ℝ), ?_, by norm_num, by norm_num, ?_⟩
  · norm_num [Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ))]
  · norm_num

/-- Negative non-torsion real point x=-1/2,y=sqrt(3/8). -/
theorem cmOriginalRealXTNegativeSignsRealized :
    (true, true) ∈ cmOriginalRealNonexceptionalXTSignImage := by
  refine ⟨(-1/2 : ℝ), Real.sqrt ((3/8 : ℝ)), ?_,
    by norm_num, by norm_num, ?_⟩
  · norm_num [Real.sq_sqrt (by norm_num : 0 ≤ (3/8 : ℝ))]
  · norm_num

/-- Full actual nonexceptional real sign image. -/
theorem cmOriginalRealNonexceptionalXTSignImage_eq :
    cmOriginalRealNonexceptionalXTSignImage =
      {c : Bool × Bool | c.1 = c.2} := by
  ext c
  constructor
  · rintro ⟨x, y, hcurve, hx0, hx1, rfl⟩
    change decide (x < 0) = decide (x - 1 < 0)
    have hsign := cmRealAffine_kummerCoordinateSignsAgree
      x y hcurve hx0 hx1
    by_cases hxneg : x < 0
    · have hxminus : x - 1 < 0 := hsign.mp hxneg
      simp [hxneg, hxminus]
    · have hxminus : ¬ x - 1 < 0 :=
        fun h => hxneg (hsign.mpr h)
      simp [hxneg, hxminus]
  · rcases c with ⟨a, b⟩
    intro hab
    change a = b at hab
    subst b
    cases a with
    | false => exact cmOriginalRealXTPositiveSignsRealized
    | true  => exact cmOriginalRealXTNegativeSignsRealized

end Synthesis.Millennium.BSD
