import Integration.OggSSP2B4AActualIntegralMultiplicities
import Integration.OggSSP2BExplicitIntegralCARestriction
import Integration.OggSSP2BActualRestrictedTate

/-!
# Residual C4/C2 action does not supply the desired binary phase

Let g be the published 4A generator and H=<g^2> the 2B subgroup.
It is tempting to use C4/H = C2 as the binary orientation on ordinary
H-Tate cohomology.  The actual source modules rule this out at the per-copy
level.

* A is rank one with trace(g)=1, hence g acts as +1 on the integral line.
  Its Hhat0 class is therefore fixed by the residual quotient action.
* For the explicit C^A presentation, the unique Hhat1 parity class is also
  fixed modulo H-coboundaries by g.

Thus the residual quotient action inherited from the cyclic 4A generator is
trivial on the one-dimensional ordinary Tate class contributed by either
non-acyclic source family.  It cannot realize the nontrivial pair-swap
BinaryPhase used by the 5x2 completion ontology.

A nontrivial binary orientation on a selected ten-class subquotient must come
from additional source structure (normalizer/local inertia/Hecke/etc.), not
from the cyclic C4/H quotient alone.
-/

namespace Integration.OggSSP2BResidualC4BinaryPhaseNoGo

namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities
namespace C := Integration.OggSSP2BExplicitIntegralCARestriction

/-- Rank-one A with generator trace one has the only possible integral
automorphism +1.  We expose the action explicitly. -/
def AGenerator (n : ℤ) : ℤ := n

theorem AGenerator_is_identity (n : ℤ) :
    AGenerator n = n := rfl

/-- The nonzero ordinary Hhat0 class of A is fixed under the residual
C4/H action.  ZMod 2 represents the quotient Z/2Z. -/
def residualOnATateH0 (x : ZMod 2) : ZMod 2 := x

theorem residualOnATateH0_identity :
    residualOnATateH0 = id := rfl

/-- On the explicit C^A lattice, compare g(oddClass) to oddClass. -/
def CAResidualDifference : C.Lattice3 :=
  let moved := C.generator4 C.oddClass
  ⟨moved.a - C.oddClass.a,
   moved.b - C.oddClass.b,
   moved.c - C.oddClass.c⟩

theorem CA_generator_moves_odd_by_coboundary :
    ∃ u : C.Lattice3,
      C.diff2 u = CAResidualDifference := by
  refine ⟨⟨1,0,0⟩, ?_⟩
  decide

/-- Therefore the unique nonzero Hhat1 parity class of C^A is fixed by
the residual generator modulo H-coboundaries. -/
theorem CA_odd_class_residual_fixed_mod_diff :
    ∃ u : C.Lattice3,
      C.diff2 u =
        let moved := C.generator4 C.oddClass
        ⟨moved.a - C.oddClass.a,
         moved.b - C.oddClass.b,
         moved.c - C.oddClass.c⟩ :=
  CA_generator_moves_odd_by_coboundary

/-- A genuine two-state swap cannot equal the identity action. -/
def swapBool : Bool → Bool
  | false => true
  | true => false

theorem swapBool_not_identity :
    swapBool ≠ id := by
  intro h
  have := congrFun h false
  simp [swapBool] at this

/-- Hence the residual C4/H action on the per-copy A Tate class cannot
instantiate the nontrivial BinaryPhase flip. -/
theorem A_residual_cannot_be_nontrivial_binary_swap :
    ¬ ∃ e : ZMod 2 ≃ Bool,
      ∀ x : ZMod 2,
        e (residualOnATateH0 x) = swapBool (e x) := by
  rintro ⟨e, h⟩
  let x : ZMod 2 := 0
  have hx := h x
  simp [residualOnATateH0, swapBool] at hx

end Integration.OggSSP2BResidualC4BinaryPhaseNoGo
