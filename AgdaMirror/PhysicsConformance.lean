import AgdaMirror.PhysicsSignature

/-!
# Lean mirror of `DASHI/Algebra/PhysicsConformance.agda` (genuine conformance)

Faithful transcription of the finite-list conformance predicate:

* `ConformsOn f g xs` — `f` and `g` agree on every element of the list `xs`.

The Agda original ships a concrete `physics-conformance : ConformsOn implSig
specSig vectors`, proved by a `refl`-fold over a fixed witness table.  We mirror
the genuine, table-independent core: conformance is **reflexive** (`ConformsOn
f f xs` for every list), and it transfers along pointwise equality.  Specialised
to the `Sig15` scanner from `AgdaMirror.PhysicsSignature`, this is the genuine
content underlying the shipped conformance theorem.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.PhysicsConformance

open AgdaMirror.PhysicsSignature

/-- `f` and `g` produce equal signatures on every element of `xs`
(Agda `ConformsOn`). -/
def ConformsOn (f g : State → Sig15) : List State → Prop
  | [] => True
  | s :: ss => f s = g s ∧ ConformsOn f g ss

/-- Conformance is reflexive: any scanner conforms with itself on any list. -/
theorem conformsOn_self (f : State → Sig15) :
    ∀ xs, ConformsOn f f xs
  | [] => trivial
  | _ :: ss => ⟨rfl, conformsOn_self f ss⟩

/-- Conformance transfers along pointwise equality of the scanners. -/
theorem conformsOn_of_pointwise {f g : State → Sig15}
    (h : ∀ s, f s = g s) : ∀ xs, ConformsOn f g xs
  | [] => trivial
  | s :: ss => ⟨h s, conformsOn_of_pointwise h ss⟩

end AgdaMirror.PhysicsConformance
