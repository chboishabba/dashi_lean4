import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact

/-!
# P¹×P¹ primitive-ruling regression lattice

The actual geometric surface P¹×P¹ has two ruling classes h₁,h₂ with
  h₁² = 0, h₂² = 0, h₁·h₂ = 1.

This file formalizes that rank-two intersection lattice as an exact regression
surface for correspondence code. The diagonal polarization is h=h₁+h₂ and
h₁-h₂ is primitive because (h₁-h₂)·h = 0.

The factor-swap correspondence fixes h and sends h₁-h₂ to its negative.

This file does NOT identify the lattice with actual singular cohomology or
construct the graph of the factor swap as an algebraic correspondence; those
are the next geometric welds. The genuine scheme-level cycle carrier used by
the donor lives in MillenniumHodgeRealAlgebraicCycleMultiplicityExact.
-/

namespace Synthesis.Millennium.Hodge

abbrev RulingLattice := ℤ × ℤ

def h₁ : RulingLattice := (1, 0)
def h₂ : RulingLattice := (0, 1)
def polarization : RulingLattice := (1, 1)
def primitiveDifference : RulingLattice := (1, -1)

/-- Intersection form in the ruling basis. -/
def rulingIntersection (x y : RulingLattice) : ℤ :=
  x.1 * y.2 + x.2 * y.1

@[simp] theorem h₁_square :
    rulingIntersection h₁ h₁ = 0 := by
  norm_num [rulingIntersection, h₁]

@[simp] theorem h₂_square :
    rulingIntersection h₂ h₂ = 0 := by
  norm_num [rulingIntersection, h₂]

@[simp] theorem h₁_inter_h₂ :
    rulingIntersection h₁ h₂ = 1 := by
  norm_num [rulingIntersection, h₁, h₂]

@[simp] theorem primitiveDifference_is_primitive :
    rulingIntersection primitiveDifference polarization = 0 := by
  norm_num [rulingIntersection, primitiveDifference, polarization]

/-- Factor exchange on the two ruling coordinates. -/
def swapRulings (x : RulingLattice) : RulingLattice :=
  (x.2, x.1)

@[simp] theorem swapRulings_involution (x : RulingLattice) :
    swapRulings (swapRulings x) = x := by
  rcases x with ⟨a,b⟩
  rfl

@[simp] theorem swapRulings_fixes_polarization :
    swapRulings polarization = polarization := by
  rfl

@[simp] theorem swapRulings_negates_primitiveDifference :
    swapRulings primitiveDifference = - primitiveDifference := by
  norm_num [swapRulings, primitiveDifference]

@[simp] theorem primitiveDifference_self_intersection :
    rulingIntersection primitiveDifference primitiveDifference = -2 := by
  norm_num [rulingIntersection, primitiveDifference]

/-!
MAX-CUT boundary.

PAID:
* exact rank-two ruling intersection lattice;
* nonzero primitive direction for the diagonal polarization;
* factor-swap involution;
* polarization fixed and primitive direction negated.

OPEN:
* actual P¹×P¹ Scheme;
* actual codimension-one ruling cycles in AlgebraicCycle;
* graph of factor swap as an algebraic correspondence;
* induced action on singular/de Rham cohomology;
* compatibility with the cycle-class map;
* migration to a variety with genuinely difficult primitive Hodge classes.
-/

end Synthesis.Millennium.Hodge
