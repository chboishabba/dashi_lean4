import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/ConstraintAlgebraClosure.agda`
(and `…ClosureTests.agda`) — faithful interface + genuine witness

The abstract operator constraint (Lie) algebra with a commutator bracket, the
Dirac closure statement (commutators of constraints re-express as constraints),
the axiom bundle, and the closure extraction theorem.  Everything is honest
interface (no postulates in the source), and we additionally back it with a
genuine trivial-algebra witness for which the Dirac closure genuinely holds.
-/

namespace AgdaMirror.ConstraintAlgebraClosure

/-- An abstract operator algebra with a composition and a difference, a unit, an
index set, a Hamiltonian constraint `H`, and momentum constraints `Hi`. -/
structure ConstraintAlgebraStructure where
  Op : Type
  comp : Op → Op → Op
  sub : Op → Op → Op
  I : Op
  Idx : Type
  H : Op
  Hi : Idx → Op

/-- The commutator bracket `[X, Y] = X∘Y − Y∘X`. -/
def bracket (S : ConstraintAlgebraStructure) (X Y : S.Op) : S.Op :=
  S.sub (S.comp X Y) (S.comp Y X)

/-- The Dirac closure: commutators of constraints re-express as constraints. -/
structure DiracClosure (S : ConstraintAlgebraStructure) : Prop where
  mom_mom : ∀ i j, ∃ k, bracket S (S.Hi i) (S.Hi j) = S.Hi k
  ham_mom : ∀ i, bracket S S.H (S.Hi i) = S.H
  ham_ham : ∃ k, bracket S S.H S.H = S.Hi k

/-- The axiom bundle (no postulates — the abstract conditions are honest
fields). -/
structure ConstraintAlgebraAxioms where
  struct : ConstraintAlgebraStructure
  ValuationEquivariance : Prop
  NoLeakageStability : Prop
  closure : DiracClosure struct

/-- The closure theorem: extract the Dirac closure from the bundle. -/
def ConstraintAlgebraTheorem (A : ConstraintAlgebraAxioms) : DiracClosure A.struct :=
  A.closure

/-- A bundle wrapper. -/
structure ConstraintClosureBundle where
  axioms : ConstraintAlgebraAxioms

/-- Closure from a bundle. -/
def closure_from_bundle (bundle : ConstraintClosureBundle) :
    DiracClosure bundle.axioms.struct :=
  ConstraintAlgebraTheorem bundle.axioms

/-! ### Genuine trivial-algebra witness -/

/-- The trivial one-element operator algebra. -/
def trivialStruct : ConstraintAlgebraStructure where
  Op := Unit
  comp := fun _ _ => ()
  sub := fun _ _ => ()
  I := ()
  Idx := Unit
  H := ()
  Hi := fun _ => ()

/-- The trivial algebra genuinely satisfies the Dirac closure. -/
theorem trivial_diracClosure : DiracClosure trivialStruct where
  mom_mom := fun _ _ => ⟨(), rfl⟩
  ham_mom := fun _ => rfl
  ham_ham := ⟨(), rfl⟩

/-- The trivial axiom bundle. -/
def trivialAxioms : ConstraintAlgebraAxioms where
  struct := trivialStruct
  ValuationEquivariance := True
  NoLeakageStability := True
  closure := trivial_diracClosure

end AgdaMirror.ConstraintAlgebraClosure
