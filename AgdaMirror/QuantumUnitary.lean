import AgdaMirror.OperatorTypes

/-!
# Lean mirror of `DASHI/Algebra/Quantum/Unitary.agda` (genuine interface + witness)

Faithful transcription of the abstract "unitary operator" interface:

* `ComplexAxioms` — an abstract scalar field with an equality relation,
* `InnerProductSpace A S` — an inner product `⟪_,_⟫ : S → S → ℂ`,
* `Unitary IPS U` — `U` is invertible and preserves the inner product.

These are pure interface records (reusing the `Invertible` predicate from
`AgdaMirror.OperatorTypes`).  We give a genuine *witness*: on the trivial inner
product the identity operator is unitary.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.QuantumUnitary

open AgdaMirror.OperatorTypes

/-- Abstract scalar field with an equality relation (Agda `record ComplexAxioms`). -/
structure ComplexAxioms where
  C : Type
  eqC : C → C → Prop

/-- Abstract inner-product space over an abstract scalar field. -/
structure InnerProductSpace (A : ComplexAxioms) (S : Type) where
  inner : S → S → A.C

/-- A unitary operator: invertible and inner-product preserving. -/
structure Unitary {A : ComplexAxioms} {S : Type}
    (IPS : InnerProductSpace A S) (U : S → S) where
  invertible : Invertible U
  preserves : ∀ x y, A.eqC (IPS.inner (U x) (U y)) (IPS.inner x y)

/-- The trivial scalar field with universal equality. -/
def trivialComplex : ComplexAxioms where
  C := PUnit
  eqC := fun _ _ => True

/-- The trivial inner product on any carrier. -/
def trivialIPS (S : Type) : InnerProductSpace trivialComplex S where
  inner := fun _ _ => PUnit.unit

/-- Genuine witness: the identity operator is unitary for the trivial inner
product. -/
def idUnitary (S : Type) : Unitary (trivialIPS S) (id) where
  invertible := { inv := id, left := fun _ => rfl, right := fun _ => rfl }
  preserves := fun _ _ => trivial

end AgdaMirror.QuantumUnitary
