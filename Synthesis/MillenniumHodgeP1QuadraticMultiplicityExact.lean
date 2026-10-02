import Mathlib.Algebra.Polynomial.Roots

/-!
# Hodge donor: exact multiplicity two for the quadratic P¹ point-section pullback

The Agda geometric donor computes the pulled-back homogeneous point section as x₁².
On the affine coordinate chart this is the polynomial X².

Mathlib's actual polynomial root multiset therefore records TWO copies of the selected
root. This is stronger than merely observing that the pullback polynomial factors as
a square: the algebraic multiplicity is computed.

This is still below the Chow-theoretic frontier:
  * no projective closed-subscheme graph is constructed here;
  * no Cartier/Weil divisor on P¹ is built here;
  * no cycle-class map or singular-cohomology pullback is claimed.

It isolates exactly the local multiplicity input needed by the future divisor theorem.
-/

namespace Synthesis.Millennium.Hodge

open Polynomial

/-- Affine local equation of the target point after pulling back along
[z₀:z₁] ↦ [z₀²:z₁²]. -/
def quadraticPointPullbackLocalEquation : ℚ[X] :=
  X ^ 2

/-- The pulled-back local equation has exactly the double root multiset {0,0}. -/
theorem quadraticPointPullback_roots :
    quadraticPointPullbackLocalEquation.roots = ({0, 0} : Multiset ℚ) := by
  simp [quadraticPointPullbackLocalEquation, pow_two, Polynomial.roots_mul]

/-- In particular the selected point occurs with algebraic multiplicity exactly two. -/
theorem quadraticPointPullback_rootMultiplicity :
    rootMultiplicity (0 : ℚ) quadraticPointPullbackLocalEquation = 2 := by
  rw [← Polynomial.count_roots]
  simp [quadraticPointPullbackLocalEquation, pow_two, Polynomial.roots_mul]

/-- The same multiplicity is visible directly by counting the root multiset. -/
theorem quadraticPointPullback_count_zero :
    quadraticPointPullbackLocalEquation.roots.count 0 = 2 := by
  simp [quadraticPointPullbackLocalEquation, pow_two, Polynomial.roots_mul]

/-- Effective zero-divisor on the affine chart, represented by the
root multiset with algebraic multiplicity. -/
def affineEffectiveZeroDivisor (p : ℚ[X]) : Multiset ℚ :=
  p.roots

/-- The selected target point y₁=0 restricts to the origin on this chart. -/
def targetPointAffineDivisor : Multiset ℚ :=
  {0}

/-- Pullback of the selected point section gives exactly TWO copies of the
same affine prime divisor, not merely the same support. -/
theorem quadraticPointPullback_affineDivisor :
    affineEffectiveZeroDivisor quadraticPointPullbackLocalEquation
      =
    targetPointAffineDivisor + targetPointAffineDivisor := by
  simp [affineEffectiveZeroDivisor, targetPointAffineDivisor,
    quadraticPointPullbackLocalEquation, pow_two, Polynomial.roots_mul]

/-- The divisor degree on this affine zero-cycle is exactly two. -/
theorem quadraticPointPullback_affineDivisor_degree :
    Multiset.card
      (affineEffectiveZeroDivisor quadraticPointPullbackLocalEquation)
      = 2 := by
  rw [quadraticPointPullback_affineDivisor]
  simp [targetPointAffineDivisor]

/-!
The next genuine geometric theorem is:
  f^*[1:0] = 2·[1:0] in CH¹(P¹)
followed by cycle-class compatibility. The polynomial multiplicity result is an
input to that theorem, not a replacement for it.
-/

end Synthesis.Millennium.Hodge
